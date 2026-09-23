import OcamlPq.MLKEM.Tables

/-!
# FIPS 203 NTT algorithms (specification)

Transcriptions of FIPS 203 Algorithms 9 (`NTT`), 10 (`NTT⁻¹`),
11 (`MultiplyNTTs`) and 12 (`BaseCaseMultiply`) over `ℤ_q = ZMod 3329`,
written from the standard and independently of `lib/mlkem_engine.ml`.
An array `f ∈ ℤ_q^256` is a function `ℕ → ℤ_q`; only indices `< 256` are
read or written by the algorithms.

The C-style loops `for (x ← a; cond; x ← step)` are transcribed as
well-founded recursions with the same condition and step; `for (j ← start;
j < start + len; j++)` is a left fold over `List.range' start len`.

The second half of the file proves what the `j` loops and one run of the
`start` loop compute (`fipsNtt_jloop`, `fipsInv_jloop`,
`fipsNttStartLoop_spec`, `fipsInvStartLoop_spec`); `OcamlPq.MLKEM.NTTLayers`
uses these to split the algorithms into seven layers.
-/

namespace OcamlPq.MLKEM

/-- An element of `ℤ_q^256`, indexed by `ℕ` (entries `≥ 256` are unused). -/
abbrev Poly := ℕ → Zq

/-! ## Algorithm 9: NTT -/

/-- FIPS 203 Algorithm 9, lines 8–10:
    `t ← zeta·f̂[j+len]; f̂[j+len] ← f̂[j] − t; f̂[j] ← f̂[j] + t`. -/
def fipsNttStep (z : Zq) (len : ℕ) (f : Poly) (j : ℕ) : Poly :=
  let t := z * f (j + len)
  let f := Function.update f (j + len) (f j - t)
  Function.update f j (f j + t)

/-- FIPS 203 Algorithm 9, lines 4–11: `for (start ← 0; start < 256;
    start ← start + 2·len)` with `zeta ← ζ^BitRev7(i); i ← i + 1` and the
    `j` loop. Returns the array and `i`. Terminates because `len > 0`. -/
def fipsNttStartLoop (len : ℕ) (hlen : 0 < len) (start i : ℕ) (f : Poly) : Poly × ℕ :=
  if start < 256 then
    let z := zeta ^ bitRev7 i
    let f := (List.range' start len).foldl (fipsNttStep z len) f
    fipsNttStartLoop len hlen (start + 2 * len) (i + 1) f
  else (f, i)
termination_by 256 - start
decreasing_by omega

/-- FIPS 203 Algorithm 9, lines 3–12: `for (len ← 128; len ≥ 2; len ← len/2)`. -/
def fipsNttLenLoop (len i : ℕ) (f : Poly) : Poly :=
  if h : len ≥ 2 then
    let r := fipsNttStartLoop len (by omega) 0 i f
    fipsNttLenLoop (len / 2) r.2 r.1
  else f
termination_by len
decreasing_by omega

/-- FIPS 203 Algorithm 9, `NTT(f)`: `f̂ ← f; i ← 1; ...`. -/
def fipsNtt (f : Poly) : Poly := fipsNttLenLoop 128 1 f

/-! ## Algorithm 10: NTT⁻¹ -/

/-- FIPS 203 Algorithm 10, lines 8–10:
    `t ← f[j]; f[j] ← t + f[j+len]; f[j+len] ← zeta·(f[j+len] − t)`. -/
def fipsInvStep (z : Zq) (len : ℕ) (f : Poly) (j : ℕ) : Poly :=
  let t := f j
  let f := Function.update f j (t + f (j + len))
  Function.update f (j + len) (z * (f (j + len) - t))

/-- FIPS 203 Algorithm 10, lines 4–11 (`zeta ← ζ^BitRev7(i); i ← i − 1`). -/
def fipsInvStartLoop (len : ℕ) (hlen : 0 < len) (start i : ℕ) (f : Poly) : Poly × ℕ :=
  if start < 256 then
    let z := zeta ^ bitRev7 i
    let f := (List.range' start len).foldl (fipsInvStep z len) f
    fipsInvStartLoop len hlen (start + 2 * len) (i - 1) f
  else (f, i)
termination_by 256 - start
decreasing_by omega

/-- FIPS 203 Algorithm 10, lines 3–12: `for (len ← 2; len ≤ 128; len ← 2·len)`. -/
def fipsInvLenLoop (len : ℕ) (hlen : 0 < len) (i : ℕ) (f : Poly) : Poly :=
  if len ≤ 128 then
    let r := fipsInvStartLoop len hlen 0 i f
    fipsInvLenLoop (2 * len) (by omega) r.2 r.1
  else f
termination_by 129 - len
decreasing_by omega

/-- FIPS 203 Algorithm 10, `NTT⁻¹(f̂)`: `i ← 127`, the loops, then
    `f ← f·3303 mod q` (line 13). -/
def fipsNttInv (f : Poly) : Poly :=
  let f := fipsInvLenLoop 2 (by norm_num) 127 f
  fun k => f k * 3303

/-! ## Algorithms 11 and 12 -/

/-- FIPS 203 Algorithm 12, `BaseCaseMultiply(a₀, a₁, b₀, b₁, γ)`. -/
def fipsBaseCaseMultiply (a0 a1 b0 b1 γ : Zq) : Zq × Zq :=
  (a0 * b0 + a1 * b1 * γ, a0 * b1 + a1 * b0)

/-- FIPS 203 Algorithm 11, line 2 (body of the `for i` loop):
    `(ĥ[2i], ĥ[2i+1]) ← BaseCaseMultiply(f̂[2i], f̂[2i+1], ĝ[2i], ĝ[2i+1],
    ζ^(2BitRev7(i)+1))`. -/
def fipsMultiplyStep (f g : Poly) (h : Poly) (i : ℕ) : Poly :=
  let c := fipsBaseCaseMultiply (f (2 * i)) (f (2 * i + 1)) (g (2 * i)) (g (2 * i + 1))
    (zeta ^ (2 * bitRev7 i + 1))
  Function.update (Function.update h (2 * i) c.1) (2 * i + 1) c.2

/-- FIPS 203 Algorithm 11, `MultiplyNTTs(f̂, ĝ)`: `for (i ← 0; i < 128; i++)`.
    The output array starts as zero. -/
def fipsMultiplyNTTs (f g : Poly) : Poly :=
  (List.range 128).foldl (fipsMultiplyStep f g) (fun _ => 0)

/-! ## Semantics of the `j` loops -/

theorem fipsNttStep_apply (z : Zq) (m : ℕ) (hm : 0 < m) (g : Poly) (s q : ℕ) :
    fipsNttStep z m g s q =
      if q = s then g s + z * g (s + m) else if q = s + m then g s - z * g (s + m) else g q := by
  unfold fipsNttStep
  simp only [Function.update_apply]
  have hm0 : m ≠ 0 := by omega
  by_cases h1 : q = s
  · subst h1; simp [hm0]
  · by_cases h2 : q = s + m
    · subst h2; simp [hm0]
    · simp [h1, h2]

/-- The `j` loop of Algorithm 9 over `[s, s + k)` with `k ≤ len`. -/
theorem fipsNtt_jloop_aux (z : Zq) (m : ℕ) (hm : 0 < m) :
    ∀ k s (g : Poly), k ≤ m → (List.range' s k).foldl (fipsNttStep z m) g = fun p =>
      if s ≤ p ∧ p < s + k then g p + z * g (p + m)
      else if s + m ≤ p ∧ p < s + m + k then g (p - m) - z * g p else g p := by
  intro k
  induction k with
  | zero =>
    intro s g _
    funext p
    simp only [List.range'_zero, List.foldl_nil]
    split_ifs <;> first | omega | rfl
  | succ k ih =>
    intro s g hk
    rw [List.range'_succ, List.foldl_cons, ih (s + 1) _ (by omega)]
    funext p
    simp only [fipsNttStep_apply z m hm]
    split_ifs <;> first | omega | (subst_vars; simp_all)

/-- The full `j` loop of Algorithm 9 for one block starting at `base`. -/
theorem fipsNtt_jloop (z : Zq) (m : ℕ) (hm : 0 < m) (base : ℕ) (g : Poly) :
    (List.range' base m).foldl (fipsNttStep z m) g = fun p =>
      if base ≤ p ∧ p < base + m then g p + z * g (p + m)
      else if base + m ≤ p ∧ p < base + 2 * m then g (p - m) - z * g p else g p := by
  rw [fipsNtt_jloop_aux z m hm m base g le_rfl]
  funext p
  simp only [show base + m + m = base + 2 * m by ring]

theorem fipsInvStep_apply (z : Zq) (m : ℕ) (hm : 0 < m) (g : Poly) (s q : ℕ) :
    fipsInvStep z m g s q =
      if q = s then g s + g (s + m) else if q = s + m then z * (g (s + m) - g s) else g q := by
  unfold fipsInvStep
  simp only [Function.update_apply]
  have hm0 : m ≠ 0 := by omega
  by_cases h1 : q = s
  · subst h1; simp [hm0]
  · by_cases h2 : q = s + m
    · subst h2; simp [hm0]
    · simp [h1, h2]

theorem fipsInv_jloop_aux (z : Zq) (m : ℕ) (hm : 0 < m) :
    ∀ k s (g : Poly), k ≤ m → (List.range' s k).foldl (fipsInvStep z m) g = fun p =>
      if s ≤ p ∧ p < s + k then g p + g (p + m)
      else if s + m ≤ p ∧ p < s + m + k then z * (g p - g (p - m)) else g p := by
  intro k
  induction k with
  | zero =>
    intro s g _
    funext p
    simp only [List.range'_zero, List.foldl_nil]
    split_ifs <;> first | omega | rfl
  | succ k ih =>
    intro s g hk
    rw [List.range'_succ, List.foldl_cons, ih (s + 1) _ (by omega)]
    funext p
    simp only [fipsInvStep_apply z m hm]
    split_ifs <;> first | omega | (subst_vars; simp_all)

/-- The full `j` loop of Algorithm 10 for one block starting at `base`. -/
theorem fipsInv_jloop (z : Zq) (m : ℕ) (hm : 0 < m) (base : ℕ) (g : Poly) :
    (List.range' base m).foldl (fipsInvStep z m) g = fun p =>
      if base ≤ p ∧ p < base + m then g p + g (p + m)
      else if base + m ≤ p ∧ p < base + 2 * m then z * (g p - g (p - m)) else g p := by
  rw [fipsInv_jloop_aux z m hm m base g le_rfl]
  funext p
  simp only [show base + m + m = base + 2 * m by ring]

/-! ## Semantics of the `start` loops -/

/-- One run of the `start` loop of Algorithm 9 from block `s` (of `B` blocks
    of size `2·len`): the final `i`, untouched entries, and the butterfly of
    block `b` with `zeta = ζ^BitRev7(i + (b − s))`. -/
theorem fipsNttStartLoop_spec (m B : ℕ) (hm : 0 < m) (hB : B * (2 * m) = 256) :
    ∀ k s i (g : Poly), B - s = k → s ≤ B →
      (fipsNttStartLoop m hm (s * (2 * m)) i g).2 = i + (B - s) ∧
      (∀ p, (p < s * (2 * m) ∨ 256 ≤ p) → (fipsNttStartLoop m hm (s * (2 * m)) i g).1 p = g p) ∧
      (∀ b r, s ≤ b → b < B → r < 2 * m →
        (fipsNttStartLoop m hm (s * (2 * m)) i g).1 (b * (2 * m) + r) =
          if r < m then
            g (b * (2 * m) + r) + zeta ^ bitRev7 (i + (b - s)) * g (b * (2 * m) + r + m)
          else
            g (b * (2 * m) + r - m) - zeta ^ bitRev7 (i + (b - s)) * g (b * (2 * m) + r)) := by
  intro k
  induction k with
  | zero =>
    intro s i g hk hs
    have hsB : s = B := by omega
    subst hsB
    rw [fipsNttStartLoop, ite_eq_right (by omega)]
    exact ⟨by simp, fun p _ => rfl, fun b r h1 h2 _ => absurd h2 (by omega)⟩
  | succ k ih =>
    intro s i g hk hs
    have hsB : s < B := by omega
    have hmul : (s + 1) * (2 * m) ≤ B * (2 * m) := Nat.mul_le_mul_right _ hsB
    have hsucc : (s + 1) * (2 * m) = s * (2 * m) + 2 * m := by ring
    rw [fipsNttStartLoop, ite_eq_left (by omega)]
    simp only
    rw [show s * (2 * m) + 2 * m = (s + 1) * (2 * m) by ring]
    have hg1 := fipsNtt_jloop (zeta ^ bitRev7 i) m hm (s * (2 * m)) g
    set g1 := (List.range' (s * (2 * m)) m).foldl (fipsNttStep (zeta ^ bitRev7 i) m) g
    obtain ⟨ih1, ih2, ih3⟩ := ih (s + 1) (i + 1) g1 (by omega) (by omega)
    refine ⟨by rw [ih1]; omega, ?_, ?_⟩
    · intro p hp
      rw [ih2 p (by omega), hg1]
      simp only
      split_ifs <;> first | omega | rfl
    · intro b r hb1 hb2 hr
      rcases Nat.eq_or_lt_of_le hb1 with rfl | hb
      · rw [ih2 _ (by left; omega), hg1]
        simp only [Nat.sub_self, Nat.add_zero]
        split_ifs <;> first | omega | rfl
      · have hbm : (s + 1) * (2 * m) ≤ b * (2 * m) := Nat.mul_le_mul_right _ hb
        have hbB : (b + 1) * (2 * m) ≤ B * (2 * m) := Nat.mul_le_mul_right _ hb2
        have hbsucc : (b + 1) * (2 * m) = b * (2 * m) + 2 * m := by ring
        rw [ih3 b r hb hb2 hr, show i + 1 + (b - (s + 1)) = i + (b - s) by omega, hg1]
        simp only
        split_ifs <;> first | omega | rfl

/-- One run of the `start` loop of Algorithm 10 from block `s`: block `b`
    uses `zeta = ζ^BitRev7(i − (b − s))`; requires `B − s ≤ i` so that `i`
    never goes below zero. -/
theorem fipsInvStartLoop_spec (m B : ℕ) (hm : 0 < m) (hB : B * (2 * m) = 256) :
    ∀ k s i (g : Poly), B - s = k → s ≤ B → B - s ≤ i →
      (fipsInvStartLoop m hm (s * (2 * m)) i g).2 = i - (B - s) ∧
      (∀ p, (p < s * (2 * m) ∨ 256 ≤ p) → (fipsInvStartLoop m hm (s * (2 * m)) i g).1 p = g p) ∧
      (∀ b r, s ≤ b → b < B → r < 2 * m →
        (fipsInvStartLoop m hm (s * (2 * m)) i g).1 (b * (2 * m) + r) =
          if r < m then g (b * (2 * m) + r) + g (b * (2 * m) + r + m)
          else zeta ^ bitRev7 (i - (b - s)) *
            (g (b * (2 * m) + r) - g (b * (2 * m) + r - m))) := by
  intro k
  induction k with
  | zero =>
    intro s i g hk hs _
    have hsB : s = B := by omega
    subst hsB
    rw [fipsInvStartLoop, ite_eq_right (by omega)]
    exact ⟨by simp, fun p _ => rfl, fun b r h1 h2 _ => absurd h2 (by omega)⟩
  | succ k ih =>
    intro s i g hk hs hi
    have hsB : s < B := by omega
    have hmul : (s + 1) * (2 * m) ≤ B * (2 * m) := Nat.mul_le_mul_right _ hsB
    have hsucc : (s + 1) * (2 * m) = s * (2 * m) + 2 * m := by ring
    rw [fipsInvStartLoop, ite_eq_left (by omega)]
    simp only
    rw [show s * (2 * m) + 2 * m = (s + 1) * (2 * m) by ring]
    have hg1 := fipsInv_jloop (zeta ^ bitRev7 i) m hm (s * (2 * m)) g
    set g1 := (List.range' (s * (2 * m)) m).foldl (fipsInvStep (zeta ^ bitRev7 i) m) g
    obtain ⟨ih1, ih2, ih3⟩ := ih (s + 1) (i - 1) g1 (by omega) (by omega) (by omega)
    refine ⟨by rw [ih1]; omega, ?_, ?_⟩
    · intro p hp
      rw [ih2 p (by omega), hg1]
      simp only
      split_ifs <;> first | omega | rfl
    · intro b r hb1 hb2 hr
      rcases Nat.eq_or_lt_of_le hb1 with rfl | hb
      · rw [ih2 _ (by left; omega), hg1]
        simp only [Nat.sub_self, Nat.sub_zero]
        split_ifs <;> first | omega | rfl
      · have hbm : (s + 1) * (2 * m) ≤ b * (2 * m) := Nat.mul_le_mul_right _ hb
        have hbB : (b + 1) * (2 * m) ≤ B * (2 * m) := Nat.mul_le_mul_right _ hb2
        have hbsucc : (b + 1) * (2 * m) = b * (2 * m) + 2 * m := by ring
        rw [ih3 b r hb hb2 hr, show i - 1 - (b - (s + 1)) = i - (b - s) by omega, hg1]
        simp only
        split_ifs <;> first | omega | rfl

end OcamlPq.MLKEM
