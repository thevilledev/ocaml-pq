import OcamlPq.MLDSA.NTT

/-!
# Closed forms of the FIPS 204 NTT loops

The imperative loops of Algorithms 41 and 42 are rewritten as compositions
of eight explicit layer maps (`layerF`, `layerI`).
-/

namespace OcamlPq.MLDSA

/-! ## Arithmetic on block indices -/

theorem iteT {α : Sort*} {c : Prop} [Decidable c] (h : c) (a b : α) : ite c a b = a := by
  simp [h]

theorem iteF {α : Sort*} {c : Prop} [Decidable c] (h : ¬c) (a b : α) : ite c a b = b := by
  simp [h]


/-- The butterfly half-lengths used by the NTT: `len = 2^(7-s)`. -/
def IsLen (len : ℕ) : Prop :=
  len = 1 ∨ len = 2 ∨ len = 4 ∨ len = 8 ∨ len = 16 ∨ len = 32 ∨ len = 64 ∨ len = 128

theorem IsLen.pos {len : ℕ} (h : IsLen len) : 1 ≤ len := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem blk_lt {len : ℕ} (h : IsLen len) (k : ℕ) (hk : k < 256) : k / (2 * len) < 256 / (2 * len) := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Block arithmetic for `L = 2·len`: position and block of indices inside,
    after, and at a partner offset of a block. -/
theorem blk_arith {len : ℕ} (h : IsLen len) (b k : ℕ) :
    (2 * len * b ≤ k → k < 2 * len * b + 2 * len →
      k / (2 * len) = b ∧ k % (2 * len) = k - 2 * len * b) ∧
    (2 * len * b + 2 * len ≤ k →
      b + 1 ≤ k / (2 * len) ∧ (len ≤ k % (2 * len) → 2 * len * b + 2 * len + len ≤ k)) ∧
    (2 * len * b < 256 → 2 * len * b + 2 * len ≤ 256 ∧ b < 256 / (2 * len)) ∧
    (2 * len * b ≤ 256 → ¬ 2 * len * b < 256 → b = 256 / (2 * len)) ∧
    2 * len * (b + 1) = 2 * len * b + 2 * len := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨fun h1 h2 => ⟨by omega, by omega⟩, fun h1 => ⟨by omega, fun h2 => by omega⟩,
      fun h1 => ⟨by omega, by omega⟩, fun h1 h2 => by omega, by ring⟩

/-- Partner indices inside a layer. -/
theorem partner_arith {len : ℕ} (h : IsLen len) (k : ℕ) (hk : k < 256) :
    (k % (2 * len) < len →
      k + len < 256 ∧ (k + len) % (2 * len) = k % (2 * len) + len ∧
      (k + len) / (2 * len) = k / (2 * len) ∧
      k % len = k % (2 * len) ∧ k / len = 2 * (k / (2 * len))) ∧
    (len ≤ k % (2 * len) →
      len ≤ k ∧ (k - len) % (2 * len) = k % (2 * len) - len ∧
      (k - len) / (2 * len) = k / (2 * len) ∧
      k % len = k % (2 * len) - len ∧ k / len = 2 * (k / (2 * len)) + 1) := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨fun h1 => ⟨by omega, by omega, by omega, by omega, by omega⟩,
      fun h1 => ⟨by omega, by omega, by omega, by omega, by omega⟩⟩

/-! ## Inner loops -/

theorem nttSpecInner_eq (z : Zq) (len start : ℕ) (hlen : 0 < len) (w : ℕ → Zq) :
    nttSpecInner z len start w = fun k =>
      if start ≤ k ∧ k < start + len then w k + z * w (k + len)
      else if start + len ≤ k ∧ k < start + 2 * len then w (k - len) - z * w k
      else w k := by
  have key : ∀ n, n ≤ len → (List.range n).foldl
      (fun w i =>
        let j := start + i
        let t := z * w (j + len)
        let w := Function.update w (j + len) (w j - t)
        Function.update w j (w j + t)) w = fun k =>
      if start ≤ k ∧ k < start + n then w k + z * w (k + len)
      else if start + len ≤ k ∧ k < start + len + n then w (k - len) - z * w k
      else w k := by
    intro n hn
    induction n with
    | zero => funext k; split_ifs <;> first | omega | rfl
    | succ n ih =>
      rw [List.range_succ (n := n), List.foldl_append, ih (by omega)]
      funext k
      simp only [List.foldl_cons, List.foldl_nil, Function.update_apply]
      by_cases h1 : k = start + n
      · subst h1
        simp only [ite_true]
        split_ifs <;> first | omega | rfl
      · by_cases h2 : k = start + n + len
        · subst h2
          split_ifs <;> first | omega | rfl | simp only [Nat.add_sub_cancel]
        · simp only [h1, h2, ite_false]
          split_ifs <;> first | omega | rfl
  unfold nttSpecInner
  rw [key len le_rfl]
  funext k
  split_ifs <;> first | omega | rfl

theorem invSpecInner_eq (z : Zq) (len start : ℕ) (hlen : 0 < len) (w : ℕ → Zq) :
    invSpecInner z len start w = fun k =>
      if start ≤ k ∧ k < start + len then w k + w (k + len)
      else if start + len ≤ k ∧ k < start + 2 * len then z * (w (k - len) - w k)
      else w k := by
  have key : ∀ n, n ≤ len → (List.range n).foldl
      (fun w i =>
        let j := start + i
        let t := w j
        let w := Function.update w j (t + w (j + len))
        let w := Function.update w (j + len) (t - w (j + len))
        Function.update w (j + len) (z * w (j + len))) w = fun k =>
      if start ≤ k ∧ k < start + n then w k + w (k + len)
      else if start + len ≤ k ∧ k < start + len + n then z * (w (k - len) - w k)
      else w k := by
    intro n hn
    induction n with
    | zero => funext k; split_ifs <;> first | omega | rfl
    | succ n ih =>
      rw [List.range_succ (n := n), List.foldl_append, ih (by omega)]
      funext k
      simp only [List.foldl_cons, List.foldl_nil, Function.update_apply]
      by_cases h1 : k = start + n
      · subst h1
        split_ifs <;> first | omega | rfl
      · by_cases h2 : k = start + n + len
        · subst h2
          split_ifs <;> first | omega | rfl | simp only [Nat.add_sub_cancel]
        · simp only [h1, h2, ite_false]
          split_ifs <;> first | omega | rfl
  unfold invSpecInner
  rw [key len le_rfl]
  funext k
  split_ifs <;> first | omega | rfl

/-! ## Middle loops -/

/-- The `while start < 256` loop of Algorithm 41 started at block `b`
    processes every block `b' ≥ b` with `zetas[m + 1 + (b' - b)]`. -/
theorem nttSpecMiddle_eq (len : ℕ) (hlen : 1 ≤ len) (hL : IsLen len) (b m : ℕ) (w : ℕ → Zq)
    (hb : 2 * len * b ≤ 256) :
    nttSpecMiddle len hlen (2 * len * b) m w =
      (fun k => if 2 * len * b ≤ k ∧ k < 256 then
          (if k % (2 * len) < len then w k + zetaSpec (m + 1 + k / (2 * len) - b) * w (k + len)
           else w (k - len) - zetaSpec (m + 1 + k / (2 * len) - b) * w k)
        else w k,
       m + (256 / (2 * len) - b)) := by
  rw [nttSpecMiddle]
  have A := blk_arith hL b 0
  split_ifs with hs
  · have h3 := A.2.2.1 hs
    have hb1 : 2 * len * (b + 1) ≤ 256 := by rw [A.2.2.2.2]; exact h3.1
    have ih := nttSpecMiddle_eq len hlen hL (b + 1) (m + 1)
      (nttSpecInner (zetaSpec (m + 1)) len (2 * len * b) w) hb1
    rw [← A.2.2.2.2, ih, nttSpecInner_eq _ _ _ hlen]
    refine Prod.ext ?_ ?_
    · funext k
      obtain ⟨B1, B2, -, -, B5⟩ := blk_arith hL b k
      simp only
      rw [B5]
      rcases Nat.lt_or_ge k (2 * len * b) with c1 | c1
      · simp (disch := omega) only [iteT, iteF]
      rcases Nat.lt_or_ge k (2 * len * b + 2 * len) with c2 | c2
      · obtain ⟨d1, d2⟩ := B1 c1 c2
        rcases Nat.lt_or_ge k (2 * len * b + len) with c3 | c3
        · simp (disch := omega) only [iteT, iteF]
          rw [show m + 1 + k / (2 * len) - b = m + 1 by omega]
        · simp (disch := omega) only [iteT, iteF]
          rw [show m + 1 + k / (2 * len) - b = m + 1 by omega]
      rcases Nat.lt_or_ge k 256 with c4 | c4
      · obtain ⟨d1, d2⟩ := B2 c2
        rcases Nat.lt_or_ge (k % (2 * len)) len with c5 | c5
        · simp (disch := omega) only [iteT, iteF]
          rw [show m + 1 + 1 + k / (2 * len) - (b + 1) = m + 1 + k / (2 * len) - b by omega]
        · have d3 := d2 c5
          simp (disch := omega) only [iteT, iteF]
          rw [show m + 1 + 1 + k / (2 * len) - (b + 1) = m + 1 + k / (2 * len) - b by omega]
      · simp (disch := omega) only [iteT, iteF]
    · simp only; omega
  · have := A.2.2.2.1 hb hs
    refine Prod.ext ?_ ?_
    · funext k; simp only; split_ifs <;> first | omega | rfl
    · simp only; omega
termination_by 256 - 2 * len * b
decreasing_by
  have := (blk_arith hL b 0).2.2.2.2
  omega

/-- The `while start < 256` loop of Algorithm 42 started at block `b`
    processes every block `b' ≥ b` with `-zetas[m - 1 - (b' - b)]`. -/
theorem invSpecMiddle_eq (len : ℕ) (hlen : 1 ≤ len) (hL : IsLen len) (b m : ℕ) (w : ℕ → Zq)
    (hb : 2 * len * b ≤ 256) (hm : 256 / (2 * len) - b ≤ m) :
    invSpecMiddle len hlen (2 * len * b) m w =
      (fun k => if 2 * len * b ≤ k ∧ k < 256 then
          (if k % (2 * len) < len then w k + w (k + len)
           else -zetaSpec (m - 1 - (k / (2 * len) - b)) * (w (k - len) - w k))
        else w k,
       m - (256 / (2 * len) - b)) := by
  rw [invSpecMiddle]
  have A := blk_arith hL b 0
  split_ifs with hs
  · have h3 := A.2.2.1 hs
    have hb1 : 2 * len * (b + 1) ≤ 256 := by rw [A.2.2.2.2]; exact h3.1
    have ih := invSpecMiddle_eq len hlen hL (b + 1) (m - 1)
      (invSpecInner (-zetaSpec (m - 1)) len (2 * len * b) w) hb1 (by omega)
    rw [← A.2.2.2.2, ih, invSpecInner_eq _ _ _ hlen]
    refine Prod.ext ?_ ?_
    · funext k
      obtain ⟨B1, B2, -, -, B5⟩ := blk_arith hL b k
      simp only
      rw [B5]
      rcases Nat.lt_or_ge k (2 * len * b) with c1 | c1
      · simp (disch := omega) only [iteT, iteF]
      rcases Nat.lt_or_ge k (2 * len * b + 2 * len) with c2 | c2
      · obtain ⟨d1, d2⟩ := B1 c1 c2
        rcases Nat.lt_or_ge k (2 * len * b + len) with c3 | c3
        · simp (disch := omega) only [iteT, iteF]
        · simp (disch := omega) only [iteT, iteF]
          rw [show m - 1 - (k / (2 * len) - b) = m - 1 by omega]
      rcases Nat.lt_or_ge k 256 with c4 | c4
      · obtain ⟨d1, d2⟩ := B2 c2
        have d4 := blk_lt hL k c4
        rcases Nat.lt_or_ge (k % (2 * len)) len with c5 | c5
        · simp (disch := omega) only [iteT, iteF]
        · have d3 := d2 c5
          simp (disch := omega) only [iteT, iteF]
          rw [show m - 1 - 1 - (k / (2 * len) - (b + 1)) = m - 1 - (k / (2 * len) - b) by omega]
      · simp (disch := omega) only [iteT, iteF]
    · simp only; omega
  · have := A.2.2.2.1 hb hs
    refine Prod.ext ?_ ?_
    · funext k; simp only; split_ifs <;> first | omega | rfl
    · simp only; omega
termination_by 256 - 2 * len * b
decreasing_by
  have := (blk_arith hL b 0).2.2.2.2
  omega

/-! ## Layers -/

/-- One layer of Algorithm 41 in closed form: block `b = k / (2 len)` uses
    the factor `zf b`. -/
def layerF (len : ℕ) (zf : ℕ → Zq) (w : ℕ → Zq) : ℕ → Zq := fun k =>
  if k < 256 then
    if k % (2 * len) < len then w k + zf (k / (2 * len)) * w (k + len)
    else w (k - len) - zf (k / (2 * len)) * w k
  else w k

/-- One layer of Algorithm 42 in closed form. -/
def layerI (len : ℕ) (zi : ℕ → Zq) (w : ℕ → Zq) : ℕ → Zq := fun k =>
  if k < 256 then
    if k % (2 * len) < len then w k + w (k + len)
    else zi (k / (2 * len)) * (w (k - len) - w k)
  else w k

theorem nttSpecMiddle_zero (len : ℕ) (hlen : 1 ≤ len) (hL : IsLen len) (m : ℕ) (w : ℕ → Zq) :
    nttSpecMiddle len hlen 0 m w =
      (layerF len (fun b => zetaSpec (m + 1 + b)) w, m + 256 / (2 * len)) := by
  have h := nttSpecMiddle_eq len hlen hL 0 m w (by omega)
  rw [show 2 * len * 0 = 0 by ring] at h
  rw [h]
  refine Prod.ext ?_ ?_
  · funext k
    simp only [layerF, Nat.sub_zero, zero_le, true_and]
  · simp

theorem invSpecMiddle_zero (len : ℕ) (hlen : 1 ≤ len) (hL : IsLen len) (m : ℕ) (w : ℕ → Zq)
    (hm : 256 / (2 * len) ≤ m) :
    invSpecMiddle len hlen 0 m w =
      (layerI len (fun b => -zetaSpec (m - 1 - b)) w, m - 256 / (2 * len)) := by
  have h := invSpecMiddle_eq len hlen hL 0 m w (by omega) (by omega)
  rw [show 2 * len * 0 = 0 by ring] at h
  rw [h]
  refine Prod.ext ?_ ?_
  · funext k
    simp only [layerI, Nat.sub_zero, zero_le, true_and]
  · simp

/-! ## Outer loops -/

theorem nttSpecOuter_step (len m : ℕ) (w : ℕ → Zq) (hL : IsLen len) :
    nttSpecOuter len m w =
      nttSpecOuter (len / 2) (m + 256 / (2 * len))
        (layerF len (fun b => zetaSpec (m + 1 + b)) w) := by
  rw [nttSpecOuter, dite_eq_left_of_eq_true (eq_true hL.pos)]
  simp only [nttSpecMiddle_zero len hL.pos hL]

theorem nttSpecOuter_zero (m : ℕ) (w : ℕ → Zq) : nttSpecOuter 0 m w = w := by
  rw [nttSpecOuter]; simp

theorem invSpecOuter_step (len : ℕ) (hlen : 1 ≤ len) (m : ℕ) (w : ℕ → Zq) (hL : IsLen len)
    (hm : 256 / (2 * len) ≤ m) :
    invSpecOuter len hlen m w =
      invSpecOuter (2 * len) (by omega) (m - 256 / (2 * len))
        (layerI len (fun b => -zetaSpec (m - 1 - b)) w) := by
  have h256 : len < 256 := by rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rw [invSpecOuter, iteT h256]
  simp only [invSpecMiddle_zero len hlen hL m w hm]

theorem invSpecOuter_256 (hlen : 1 ≤ 256) (m : ℕ) (w : ℕ → Zq) : invSpecOuter 256 hlen m w = w := by
  rw [invSpecOuter]; simp

/-- Layer `s` of Algorithm 41 (`len = 2^(7-s)`, block `b` uses
    `zetas[2^s + b]`). -/
def fwdLayer (s : ℕ) : (ℕ → Zq) → ℕ → Zq :=
  layerF (2 ^ (7 - s)) (fun b => zetaSpec (2 ^ s + b))

/-- Layer `s` of Algorithm 42 (`len = 2^(7-s)`, block `b` uses
    `-zetas[2^(s+1) - 1 - b]`). -/
def invLayer (s : ℕ) : (ℕ → Zq) → ℕ → Zq :=
  layerI (2 ^ (7 - s)) (fun b => -zetaSpec (2 ^ (s + 1) - 1 - b))

/-- Scaling of the first 256 coefficients. -/
def smul256 (c : Zq) (w : ℕ → Zq) : ℕ → Zq := fun k => if k < 256 then c * w k else w k

/-- Algorithm 41 is the composition of its eight layers. -/
theorem nttSpec_eq_layers (w : ℕ → Zq) :
    nttSpec w = fwdLayer 7 (fwdLayer 6 (fwdLayer 5 (fwdLayer 4
      (fwdLayer 3 (fwdLayer 2 (fwdLayer 1 (fwdLayer 0 w))))))) := by
  unfold nttSpec
  rw [nttSpecOuter_step _ _ _ (by unfold IsLen; norm_num)]
  rw [nttSpecOuter_step _ _ _ (by unfold IsLen; norm_num)]
  rw [nttSpecOuter_step _ _ _ (by unfold IsLen; norm_num)]
  rw [nttSpecOuter_step _ _ _ (by unfold IsLen; norm_num)]
  rw [nttSpecOuter_step _ _ _ (by unfold IsLen; norm_num)]
  rw [nttSpecOuter_step _ _ _ (by unfold IsLen; norm_num)]
  rw [nttSpecOuter_step _ _ _ (by unfold IsLen; norm_num)]
  rw [nttSpecOuter_step _ _ _ (by unfold IsLen; norm_num)]
  rw [nttSpecOuter_zero]
  rfl

/-- Algorithm 42 is the composition of its eight layers followed by the
    scaling by `f = 8347681`. -/
theorem invNttSpec_eq_layers (w : ℕ → Zq) :
    invNttSpec w = smul256 8347681 (invLayer 0 (invLayer 1 (invLayer 2 (invLayer 3
      (invLayer 4 (invLayer 5 (invLayer 6 (invLayer 7 w)))))))) := by
  unfold invNttSpec
  rw [scale_loop_eq]
  rw [invSpecOuter_step _ _ _ _ (by unfold IsLen; norm_num) (by norm_num)]
  rw [invSpecOuter_step _ _ _ _ (by unfold IsLen; norm_num) (by norm_num)]
  rw [invSpecOuter_step _ _ _ _ (by unfold IsLen; norm_num) (by norm_num)]
  rw [invSpecOuter_step _ _ _ _ (by unfold IsLen; norm_num) (by norm_num)]
  rw [invSpecOuter_step _ _ _ _ (by unfold IsLen; norm_num) (by norm_num)]
  rw [invSpecOuter_step _ _ _ _ (by unfold IsLen; norm_num) (by norm_num)]
  rw [invSpecOuter_step _ _ _ _ (by unfold IsLen; norm_num) (by norm_num)]
  rw [invSpecOuter_step _ _ _ _ (by unfold IsLen; norm_num) (by norm_num)]
  rw [invSpecOuter_256]
  rfl

end OcamlPq.MLDSA
