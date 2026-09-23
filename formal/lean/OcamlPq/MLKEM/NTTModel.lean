import OcamlPq.MLKEM.NTTMath

/-!
# Models of the OCaml NTT, inverse NTT, `ntt_mul`, `poly_add`, `poly_sub`

Models of `lib/mlkem_engine.ml` lines 139–228 over `int array`s
(`Array ℤ`). `Array.unsafe_get` / `Array.unsafe_set` are modelled by
`getA` / `setA`, which return `none` on an out-of-bounds index; a model
returning `some` therefore proves that no out-of-bounds access happens.
`while` loops are well-founded recursions with the OCaml condition and step;
`for` loops are monadic folds over `List.range'`.

Main results (for arrays of 256 canonical coefficients, `Rep a f`):

* `ntt_refines`, `inverseNtt_refines`, `nttMul_refines`, `polyAdd_refines`,
  `polySub_refines`: the model succeeds (all indices in bounds), returns 256
  canonical coefficients, and equals FIPS 203 Algorithm 9 / 10 / 11 /
  coefficient-wise addition / subtraction over `ℤ_q`.
* `ocaml_ntt_mul_correct`: `inverse_ntt (ntt_mul (ntt a) (ntt b))` is the
  product `a·b` in `R_q = ℤ_q[X]/(X^256 + 1)`.
* `ocaml_inverseNtt_ntt`, `ocaml_ntt_inverseNtt`: the two OCaml transforms are
  mutually inverse.

Every `int` computed along the way is either a loop counter or index
(`≤ 256`), a table entry, or an intermediate of a field operation applied to
canonical operands; the latter are `Portable` by the `*_portable` lemmas of
`OcamlPq.MLKEM.Field` (see `butterfly_portable`, `invButterfly_portable`,
`nttMulStep_portable`).
-/

namespace OcamlPq.MLKEM

/-! ## Arrays -/

/-- `Array.unsafe_get a i` with a non-negative index; `none` = out of bounds. -/
def getA (a : Array ℤ) (i : ℕ) : Option ℤ := a[i]?

/-- `Array.unsafe_get a i` with an `int` index (used where the index is
    decremented). -/
def getZ (a : Array ℤ) (i : ℤ) : Option ℤ := if 0 ≤ i then a[i.toNat]? else none

/-- `Array.unsafe_set a i v`; `none` = out of bounds. -/
def setA (a : Array ℤ) (i : ℕ) (v : ℤ) : Option (Array ℤ) :=
  if h : i < a.size then some (a.set i v h) else none

/-- `a : int array` has length 256, canonical entries, and represents `g`. -/
def Rep (a : Array ℤ) (g : Poly) : Prop :=
  a.size = 256 ∧ ∀ i < 256, ∃ v, a[i]? = some v ∧ Canon v ∧ (v : Zq) = g i

theorem Rep.get {a : Array ℤ} {g : Poly} (h : Rep a g) {i : ℕ} (hi : i < 256) :
    ∃ v, getA a i = some v ∧ Canon v ∧ (v : Zq) = g i := h.2 i hi

theorem Rep.set {a : Array ℤ} {g : Poly} (h : Rep a g) {i : ℕ} (hi : i < 256) {v : ℤ}
    (hv : Canon v) : ∃ a', setA a i v = some a' ∧ Rep a' (Function.update g i (v : Zq)) := by
  have hs : i < a.size := by rw [h.1]; exact hi
  refine ⟨a.set i v hs, by simp [setA, hs], by rw [Array.size_set, h.1], fun k hk => ?_⟩
  rw [Array.getElem?_set, Function.update_apply]
  by_cases hik : i = k
  · subst hik; simp [hv]
  · rw [ite_eq_right hik, ite_eq_right (Ne.symm hik)]; exact h.2 k hk

theorem Rep.congr {a : Array ℤ} {g h : Poly} (ha : Rep a g) (hgh : EqOn256 g h) : Rep a h :=
  ⟨ha.1, fun i hi => by rw [← hgh i hi]; exact ha.2 i hi⟩

/-- The value of a representing array is determined on indices `< 256`. -/
theorem Rep.eqOn {a : Array ℤ} {g h : Poly} (hg : Rep a g) (hh : Rep a h) : EqOn256 g h := by
  intro i hi
  obtain ⟨v, e, -, c⟩ := hg.2 i hi
  obtain ⟨w, e', -, c'⟩ := hh.2 i hi
  rw [e] at e'; cases e'; rw [← c, ← c']

/-! ## `ntt` (lines 173–192) -/

/-- Body of the `for j` loop of `ntt` (`lib/mlkem_engine.ml` lines 183–186):
```
let t = field_mul zeta (Array.unsafe_get f (j + !len)) in
let fj = Array.unsafe_get f j in
Array.unsafe_set f (j + !len) (field_sub fj t);
Array.unsafe_set f j (field_add fj t)
``` -/
def nttButterfly (zeta : ℤ) (len : ℕ) (f : Array ℤ) (j : ℕ) : Option (Array ℤ) := do
  let t := fieldMul zeta (← getA f (j + len))
  let fj ← getA f j
  let f ← setA f (j + len) (fieldSub fj t)
  setA f j (fieldAdd fj t)

/-- The `while !start < n` loop of `ntt` (`lib/mlkem_engine.ml`
    lines 179–189), returning the array and `!zeta_index`. -/
def nttStartLoop (len : ℕ) (hlen : 0 < len) (start zetaIndex : ℕ) (f : Array ℤ) :
    Option (Array ℤ × ℕ) :=
  if start < 256 then do
    let zeta ← getA zetasTable zetaIndex
    let f ← (List.range' start len).foldlM (nttButterfly zeta len) f
    nttStartLoop len hlen (start + 2 * len) (zetaIndex + 1) f
  else pure (f, zetaIndex)
termination_by 256 - start
decreasing_by omega

/-- The `while !len >= 2` loop of `ntt` (`lib/mlkem_engine.ml` lines 177–191). -/
def nttLenLoop (len zetaIndex : ℕ) (f : Array ℤ) : Option (Array ℤ) :=
  if h : len ≥ 2 then do
    let r ← nttStartLoop len (by omega) 0 zetaIndex f
    nttLenLoop (len / 2) r.2 r.1
  else pure f
termination_by len
decreasing_by omega

/-- Model of `ntt` (`lib/mlkem_engine.ml` lines 173–192); `Array.copy` is the
    identity on values, `zeta_index` starts at 1 and `len` at 128. -/
def ntt (input : Array ℤ) : Option (Array ℤ) := nttLenLoop 128 1 input

theorem nttButterfly_sim {zeta : ℤ} (hz : Canon zeta) {len j : ℕ} (hlen : 0 < len)
    (hj : j + len < 256) {a : Array ℤ} {g : Poly} (h : Rep a g) :
    ∃ a', nttButterfly zeta len a j = some a' ∧ Rep a' (fipsNttStep (zeta : Zq) len g j) := by
  obtain ⟨v1, g1, c1, e1⟩ := h.get hj
  obtain ⟨v0, g0, c0, e0⟩ := h.get (show j < 256 by omega)
  have ct := fieldMul_canon hz c1
  obtain ⟨a1, s1, h1⟩ := h.set hj (fieldSub_canon c0 ct)
  obtain ⟨a2, s2, h2⟩ := h1.set (show j < 256 by omega) (fieldAdd_canon c0 ct)
  refine ⟨a2, by simp [nttButterfly, g1, g0, s1, s2], h2.congr ?_⟩
  intro k _
  rw [fipsNttStep_apply _ _ hlen, Function.update_apply, Function.update_apply,
    fieldAdd_cast c0 ct, fieldSub_cast c0 ct, fieldMul_cast hz c1, e0, e1]

theorem nttJLoop_sim {zeta : ℤ} (hz : Canon zeta) {len : ℕ} (hlen : 0 < len) :
    ∀ (l : List ℕ) (a : Array ℤ) (g : Poly), (∀ j ∈ l, j + len < 256) → Rep a g →
      ∃ a', l.foldlM (nttButterfly zeta len) a = some a' ∧
        Rep a' (l.foldl (fipsNttStep (zeta : Zq) len) g)
  | [], a, g, _, h => ⟨a, rfl, h⟩
  | j :: l, a, g, hl, h => by
    obtain ⟨a1, e1, h1⟩ := nttButterfly_sim hz hlen (hl j (List.mem_cons_self ..)) h
    obtain ⟨a2, e2, h2⟩ := nttJLoop_sim hz hlen l a1 _
      (fun j hj => hl j (List.mem_cons_of_mem _ hj)) h1
    exact ⟨a2, by simp [List.foldlM_cons, e1, e2], h2⟩

theorem block_range {m B s j : ℕ} (hB : B * (2 * m) = 256) (hs : s < B)
    (hj : j ∈ List.range' (s * (2 * m)) m) : j + m < 256 := by
  rw [List.mem_range'_1] at hj
  have := Nat.mul_le_mul_right (2 * m) hs
  rw [Nat.succ_mul, hB] at this
  omega

theorem nttStartLoop_sim (m B : ℕ) (hm : 0 < m) (hB : B * (2 * m) = 256) :
    ∀ k s zi (a : Array ℤ) (g : Poly), B - s = k → s ≤ B → zi + (B - s) ≤ 128 → Rep a g →
      ∃ a', nttStartLoop m hm (s * (2 * m)) zi a = some (a', zi + (B - s)) ∧
        Rep a' (fipsNttStartLoop m hm (s * (2 * m)) zi g).1 := by
  intro k
  induction k with
  | zero =>
    intro s zi a g hk hs _ h
    have hsB : s = B := by omega
    subst hsB
    refine ⟨a, ?_, ?_⟩
    · rw [nttStartLoop, ite_eq_right (by omega)]; simp
    · rw [fipsNttStartLoop, ite_eq_right (by omega)]; exact h
  | succ k ih =>
    intro s zi a g hk hs hzi h
    have hsB : s < B := by omega
    have hmul := Nat.mul_le_mul_right (2 * m) hsB
    rw [Nat.succ_mul, hB] at hmul
    obtain ⟨zeta, ez, cz, vz⟩ := zetasTable_get (i := zi) (by omega)
    obtain ⟨a1, e1, h1⟩ := nttJLoop_sim cz hm (List.range' (s * (2 * m)) m) a g
      (fun j hj => block_range hB hsB hj) h
    rw [vz] at h1
    obtain ⟨a2, e2, h2⟩ := ih (s + 1) (zi + 1) a1 _ (by omega) (by omega) (by omega) h1
    refine ⟨a2, ?_, ?_⟩
    · rw [nttStartLoop, ite_eq_left (by omega)]
      simp only [getA, ez, Option.bind_eq_bind, Option.bind_some]
      rw [e1, Option.bind_some, show s * (2 * m) + 2 * m = (s + 1) * (2 * m) by ring, e2,
        show zi + 1 + (B - (s + 1)) = zi + (B - s) by omega]
    · rw [fipsNttStartLoop, ite_eq_left (by omega)]
      simp only
      rw [show s * (2 * m) + 2 * m = (s + 1) * (2 * m) by ring]
      exact h2

theorem nttLenLoop_sim : ∀ j k (a : Array ℤ) (g : Poly), 7 - k = j → k ≤ 7 → Rep a g →
    ∃ a', nttLenLoop (2 ^ (7 - k)) (2 ^ k) a = some a' ∧
      Rep a' (fipsNttLenLoop (2 ^ (7 - k)) (2 ^ k) g) := by
  intro j
  induction j with
  | zero =>
    intro k a g hj hk h
    refine ⟨a, ?_, ?_⟩
    · rw [nttLenLoop, dite_eq_right (by rw [hj]; norm_num)]; rfl
    · rw [fipsNttLenLoop, dite_eq_right (by rw [hj]; norm_num)]; exact h
  | succ j ih =>
    intro k a g hj hk h
    have hk7 : k < 7 := by omega
    have hge : 2 ^ (7 - k) ≥ 2 := by
      rw [show 7 - k = (6 - k) + 1 by omega, pow_succ]
      have : 1 ≤ 2 ^ (6 - k) := Nat.one_le_two_pow
      omega
    have hB := layer_blocks hk7
    have hzi0 : 2 ^ k + (2 ^ k - 0) ≤ 128 := by
      rw [Nat.sub_zero, ← two_mul, ← pow_succ', show (128 : ℕ) = 2 ^ 7 by norm_num]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨a1, e1, h1⟩ := nttStartLoop_sim (2 ^ (7 - k)) (2 ^ k) (by positivity) hB _ 0
      (2 ^ k) a g rfl (Nat.zero_le _) hzi0 h
    simp only [zero_mul, Nat.sub_zero] at e1 h1
    have hdiv : 2 ^ (7 - k) / 2 = 2 ^ (7 - (k + 1)) := by
      rw [show 7 - k = (7 - (k + 1)) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hzi : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
    obtain ⟨a2, e2, h2⟩ := ih (k + 1) a1 _ (by omega) (by omega) h1
    refine ⟨a2, ?_, ?_⟩
    · rw [nttLenLoop, dite_eq_left hge]
      simp only [Option.bind_eq_bind]
      rw [e1, Option.bind_some]
      simp only
      rw [hdiv, hzi, e2]
    · rw [fipsNttLenLoop, dite_eq_left hge]
      simp only
      rw [nttLayer_snd hk7 g, hdiv]
      exact h2

/-- **`ntt` refines FIPS 203 Algorithm 9.** On an array of 256 canonical
    coefficients, the OCaml `ntt` performs only in-bounds accesses (the
    model returns `some`), and its output is 256 canonical coefficients equal
    to `NTT(f)` over `ℤ_q`. -/
theorem ntt_refines {a : Array ℤ} {g : Poly} (h : Rep a g) :
    ∃ out, ntt a = some out ∧ Rep out (fipsNtt g) := by
  have := nttLenLoop_sim 7 0 a g rfl (by norm_num) h
  simpa [ntt, fipsNtt] using this

/-! ## `inverse_ntt` (lines 194–216) -/

/-- Body of the `for j` loop of `inverse_ntt` (`lib/mlkem_engine.ml` lines 204–207):
```
let t = Array.unsafe_get f j in
let upper = Array.unsafe_get f (j + !len) in
Array.unsafe_set f j (field_add t upper);
Array.unsafe_set f (j + !len) (field_mul_sub zeta upper t)
``` -/
def invButterfly (zeta : ℤ) (len : ℕ) (f : Array ℤ) (j : ℕ) : Option (Array ℤ) := do
  let t ← getA f j
  let upper ← getA f (j + len)
  let f ← setA f j (fieldAdd t upper)
  setA f (j + len) (fieldMulSub zeta upper t)

/-- The `while !start < n` loop of `inverse_ntt` (`lib/mlkem_engine.ml`
    lines 200–210). The `zeta_index` counter is decremented (`decr`), so it
    is an `int` (`ℤ`). -/
def invStartLoop (len : ℕ) (hlen : 0 < len) (start : ℕ) (zetaIndex : ℤ) (f : Array ℤ) :
    Option (Array ℤ × ℤ) :=
  if start < 256 then do
    let zeta ← getZ zetasTable zetaIndex
    let f ← (List.range' start len).foldlM (invButterfly zeta len) f
    invStartLoop len hlen (start + 2 * len) (zetaIndex - 1) f
  else pure (f, zetaIndex)
termination_by 256 - start
decreasing_by omega

/-- The `while !len <= 128` loop of `inverse_ntt` (`lib/mlkem_engine.ml`
    lines 198–212). -/
def invLenLoop (len : ℕ) (hlen : 0 < len) (zetaIndex : ℤ) (f : Array ℤ) : Option (Array ℤ) :=
  if len ≤ 128 then do
    let r ← invStartLoop len hlen 0 zetaIndex f
    invLenLoop (len * 2) (by omega) r.2 r.1
  else pure f
termination_by 129 - len
decreasing_by omega

/-- Body of the final `for i` loop (`lib/mlkem_engine.ml` line 214):
    `Array.unsafe_set f i (field_mul (Array.unsafe_get f i) 3303)`. -/
def scaleStep (f : Array ℤ) (i : ℕ) : Option (Array ℤ) := do
  setA f i (fieldMul (← getA f i) 3303)

/-- Model of `inverse_ntt` (`lib/mlkem_engine.ml` lines 194–216): `zeta_index`
    starts at 127, `len` at 2, then every coefficient is multiplied by 3303. -/
def inverseNtt (input : Array ℤ) : Option (Array ℤ) := do
  let f ← invLenLoop 2 (by norm_num) 127 input
  (List.range 256).foldlM scaleStep f

theorem invButterfly_sim {zeta : ℤ} (hz : Canon zeta) {len j : ℕ} (hlen : 0 < len)
    (hj : j + len < 256) {a : Array ℤ} {g : Poly} (h : Rep a g) :
    ∃ a', invButterfly zeta len a j = some a' ∧ Rep a' (fipsInvStep (zeta : Zq) len g j) := by
  obtain ⟨v1, g1, c1, e1⟩ := h.get hj
  obtain ⟨v0, g0, c0, e0⟩ := h.get (show j < 256 by omega)
  obtain ⟨a1, s1, h1⟩ := h.set (show j < 256 by omega) (fieldAdd_canon c0 c1)
  obtain ⟨a2, s2, h2⟩ := h1.set hj (fieldMulSub_canon hz c1 c0)
  refine ⟨a2, by simp [invButterfly, g1, g0, s1, s2], h2.congr ?_⟩
  intro k _
  rw [fipsInvStep_apply _ _ hlen, Function.update_apply, Function.update_apply,
    fieldAdd_cast c0 c1, fieldMulSub_cast hz c1 c0, e0, e1]
  split_ifs <;> first | rfl | omega

theorem invJLoop_sim {zeta : ℤ} (hz : Canon zeta) {len : ℕ} (hlen : 0 < len) :
    ∀ (l : List ℕ) (a : Array ℤ) (g : Poly), (∀ j ∈ l, j + len < 256) → Rep a g →
      ∃ a', l.foldlM (invButterfly zeta len) a = some a' ∧
        Rep a' (l.foldl (fipsInvStep (zeta : Zq) len) g)
  | [], a, g, _, h => ⟨a, rfl, h⟩
  | j :: l, a, g, hl, h => by
    obtain ⟨a1, e1, h1⟩ := invButterfly_sim hz hlen (hl j (List.mem_cons_self ..)) h
    obtain ⟨a2, e2, h2⟩ := invJLoop_sim hz hlen l a1 _
      (fun j hj => hl j (List.mem_cons_of_mem _ hj)) h1
    exact ⟨a2, by simp [List.foldlM_cons, e1, e2], h2⟩

theorem invStartLoop_sim (m B : ℕ) (hm : 0 < m) (hB : B * (2 * m) = 256) :
    ∀ k s (zi : ℕ) (a : Array ℤ) (g : Poly), B - s = k → s ≤ B → B - s ≤ zi → zi < 128 →
      Rep a g →
      ∃ a', invStartLoop m hm (s * (2 * m)) (zi : ℤ) a = some (a', ((zi - (B - s) : ℕ) : ℤ)) ∧
        Rep a' (fipsInvStartLoop m hm (s * (2 * m)) zi g).1 := by
  intro k
  induction k with
  | zero =>
    intro s zi a g hk hs _ _ h
    have hsB : s = B := by omega
    subst hsB
    refine ⟨a, ?_, ?_⟩
    · rw [invStartLoop, ite_eq_right (by omega)]; simp
    · rw [fipsInvStartLoop, ite_eq_right (by omega)]; exact h
  | succ k ih =>
    intro s zi a g hk hs hzi hzi' h
    have hsB : s < B := by omega
    have hmul := Nat.mul_le_mul_right (2 * m) hsB
    rw [Nat.succ_mul, hB] at hmul
    obtain ⟨zeta, ez, cz, vz⟩ := zetasTable_get (i := zi) hzi'
    obtain ⟨a1, e1, h1⟩ := invJLoop_sim cz hm (List.range' (s * (2 * m)) m) a g
      (fun j hj => block_range hB hsB hj) h
    rw [vz] at h1
    obtain ⟨a2, e2, h2⟩ := ih (s + 1) (zi - 1) a1 _ (by omega) (by omega) (by omega) (by omega) h1
    refine ⟨a2, ?_, ?_⟩
    · rw [invStartLoop, ite_eq_left (by omega)]
      have hgz : getZ zetasTable (zi : ℤ) = some zeta := by
        simp only [getZ, Nat.cast_nonneg, ite_true, Int.toNat_natCast, ez]
      have hzc : (zi : ℤ) - 1 = ((zi - 1 : ℕ) : ℤ) := by omega
      simp only [hgz, Option.bind_eq_bind, Option.bind_some]
      rw [e1, Option.bind_some, show s * (2 * m) + 2 * m = (s + 1) * (2 * m) by ring, hzc, e2,
        show zi - 1 - (B - (s + 1)) = zi - (B - s) by omega]
    · rw [fipsInvStartLoop, ite_eq_left (by omega)]
      simp only
      rw [show s * (2 * m) + 2 * m = (s + 1) * (2 * m) by ring]
      exact h2

theorem invLenLoop_sim : ∀ n len1 len2 (h1 : 0 < len1) (h2 : 0 < len2) (a : Array ℤ) (g : Poly),
    len1 = 2 ^ (8 - n) → len2 = len1 → n ≤ 7 → Rep a g →
    ∃ a', invLenLoop len1 h1 ((2 ^ n - 1 : ℕ) : ℤ) a = some a' ∧
      Rep a' (fipsInvLenLoop len2 h2 (2 ^ n - 1) g) := by
  intro n
  induction n with
  | zero =>
    intro len1 len2 h1 h2 a g hl1 hl2 _ h
    subst len2
    refine ⟨a, ?_, ?_⟩
    · rw [invLenLoop, ite_eq_right (by rw [hl1]; norm_num)]; rfl
    · rw [fipsInvLenLoop, ite_eq_right (by rw [hl1]; norm_num)]; exact h
  | succ n ih =>
    intro len1 len2 h1 h2 a g hl1 hl2 hn h
    subst len2
    have hn7 : n < 7 := by omega
    have hlen' : len1 = 2 ^ (7 - n) := by rw [hl1, show 8 - (n + 1) = 7 - n by omega]
    subst hlen'
    have hle : 2 ^ (7 - n) ≤ 128 := by
      rw [show (128 : ℕ) = 2 ^ 7 by norm_num]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hB := layer_blocks hn7
    have hzi : 2 ^ n ≤ 2 ^ (n + 1) - 1 := two_pow_le_pred
    have hzi' : 2 ^ (n + 1) - 1 < 128 := by
      have : 2 ^ (n + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      omega
    obtain ⟨a1, e1, hr1⟩ := invStartLoop_sim (2 ^ (7 - n)) (2 ^ n) h1 hB _ 0 (2 ^ (n + 1) - 1)
      a g rfl (Nat.zero_le _) (by simpa using hzi) hzi' h
    simp only [zero_mul, Nat.sub_zero] at e1 hr1
    have hsub : 2 ^ (n + 1) - 1 - 2 ^ n = 2 ^ n - 1 := by rw [pow_succ]; omega
    rw [hsub] at e1
    obtain ⟨a2, e2, hr2⟩ := ih (2 ^ (7 - n) * 2) (2 * 2 ^ (7 - n)) (by positivity) (by positivity)
      a1 _ (by rw [mul_comm, ← pow_succ']; congr 1; omega) (by ring) (by omega) hr1
    refine ⟨a2, ?_, ?_⟩
    · rw [invLenLoop, ite_eq_left hle]
      simp only [Option.bind_eq_bind]
      rw [e1, Option.bind_some]
      exact e2
    · rw [fipsInvLenLoop, ite_eq_left hle]
      simp only
      rw [invLayer_snd hn7 g]
      exact hr2

theorem scaleLoop_sim (g : Poly) :
    ∀ k s (a : Array ℤ), s + k ≤ 256 → Rep a (fun i => if i < s then g i * 3303 else g i) →
      ∃ a', (List.range' s k).foldlM scaleStep a = some a' ∧
        Rep a' (fun i => if i < s + k then g i * 3303 else g i) := by
  intro k
  induction k with
  | zero => intro s a _ h; exact ⟨a, rfl, by simpa using h⟩
  | succ k ih =>
    intro s a hsk h
    obtain ⟨v, ev, cv, vv⟩ := h.get (show s < 256 by omega)
    have c3303 : Canon 3303 := by unfold Canon q; norm_num
    obtain ⟨a1, e1, h1⟩ := h.set (show s < 256 by omega) (fieldMul_canon cv c3303)
    have h1' : Rep a1 (fun i => if i < s + 1 then g i * 3303 else g i) := by
      refine h1.congr (fun i _ => ?_)
      rw [Function.update_apply, fieldMul_cast cv c3303, vv]
      by_cases his : i = s
      · subst his; simp
      · rw [ite_eq_right his]
        by_cases hi : i < s
        · rw [ite_eq_left hi, ite_eq_left (by omega)]
        · rw [ite_eq_right hi, ite_eq_right (by omega)]
    obtain ⟨a2, e2, h2⟩ := ih (s + 1) a1 (by omega) h1'
    refine ⟨a2, ?_, ?_⟩
    · rw [List.range'_succ, List.foldlM_cons]
      simp only [scaleStep, ev, e1, Option.bind_eq_bind, Option.bind_some]
      exact e2
    · rw [show s + (k + 1) = s + 1 + k by ring]; exact h2

/-- **`inverse_ntt` refines FIPS 203 Algorithm 10.** On an array of 256
    canonical coefficients the OCaml `inverse_ntt` performs only in-bounds
    accesses and returns 256 canonical coefficients equal to `NTT⁻¹(f̂)`. -/
theorem inverseNtt_refines {a : Array ℤ} {g : Poly} (h : Rep a g) :
    ∃ out, inverseNtt a = some out ∧ Rep out (fipsNttInv g) := by
  obtain ⟨a1, e1, h1⟩ := invLenLoop_sim 7 2 2 (by norm_num) (by norm_num) a g (by norm_num) rfl
    le_rfl h
  obtain ⟨a2, e2, h2⟩ := scaleLoop_sim (fipsInvLenLoop 2 (by norm_num) (2 ^ 7 - 1) g) 256 0 a1
    (by norm_num) (h1.congr (fun i _ => by simp))
  refine ⟨a2, ?_, h2.congr (fun i hi => ?_)⟩
  · unfold inverseNtt
    have e1' : invLenLoop 2 (by norm_num) 127 a = some a1 := by simpa using e1
    simp only [Option.bind_eq_bind]
    rw [e1', Option.bind_some, List.range_eq_range']
    exact e2
  · simp only [Nat.zero_add, hi, ite_true]
    rfl

/-! ## `ntt_mul` (lines 218–228) -/

/-- Body of the `for i` loop of `ntt_mul` (`lib/mlkem_engine.ml` lines 221–226):
```
let j = 2 * i in
let a0 = Array.unsafe_get f j and a1 = Array.unsafe_get f (j + 1) in
let b0 = Array.unsafe_get g j and b1 = Array.unsafe_get g (j + 1) in
Array.unsafe_set h j
  (field_add_mul a0 b0 (field_mul a1 b1) (Array.unsafe_get gammas i));
Array.unsafe_set h (j + 1) (field_add_mul a0 b1 a1 b0)
``` -/
def nttMulStep (f g : Array ℤ) (h : Array ℤ) (i : ℕ) : Option (Array ℤ) := do
  let j := 2 * i
  let a0 ← getA f j
  let a1 ← getA f (j + 1)
  let b0 ← getA g j
  let b1 ← getA g (j + 1)
  let gamma ← getA gammasTable i
  let h ← setA h j (fieldAddMul a0 b0 (fieldMul a1 b1) gamma)
  setA h (j + 1) (fieldAddMul a0 b1 a1 b0)

/-- Model of `ntt_mul` (`lib/mlkem_engine.ml` lines 218–228); `poly_zero ()` is
    `Array.replicate 256 0`. -/
def nttMul (f g : Array ℤ) : Option (Array ℤ) :=
  (List.range 128).foldlM (nttMulStep f g) (Array.replicate 256 0)

theorem nttMulStep_sim {f g h : Array ℤ} {F G H : Poly} (hf : Rep f F) (hg : Rep g G)
    (hh : Rep h H) {i : ℕ} (hi : i < 128) :
    ∃ h', nttMulStep f g h i = some h' ∧ Rep h' (fipsMultiplyStep F G H i) := by
  obtain ⟨a0, ea0, ca0, va0⟩ := hf.get (show 2 * i < 256 by omega)
  obtain ⟨a1, ea1, ca1, va1⟩ := hf.get (show 2 * i + 1 < 256 by omega)
  obtain ⟨b0, eb0, cb0, vb0⟩ := hg.get (show 2 * i < 256 by omega)
  obtain ⟨b1, eb1, cb1, vb1⟩ := hg.get (show 2 * i + 1 < 256 by omega)
  obtain ⟨γ, eγ, cγ, vγ⟩ := gammasTable_get hi
  have c11 := fieldMul_canon ca1 cb1
  obtain ⟨h1, s1, r1⟩ := hh.set (show 2 * i < 256 by omega) (fieldAddMul_canon ca0 cb0 c11 cγ)
  obtain ⟨h2, s2, r2⟩ := r1.set (show 2 * i + 1 < 256 by omega) (fieldAddMul_canon ca0 cb1 ca1 cb0)
  refine ⟨h2, ?_, r2.congr (fun k _ => ?_)⟩
  · simp only [nttMulStep, Option.bind_eq_bind]
    rw [ea0, Option.bind_some, ea1, Option.bind_some, eb0, Option.bind_some, eb1, Option.bind_some]
    simp only [getA] at eγ ⊢
    rw [eγ, Option.bind_some, s1, Option.bind_some, s2]
  · rw [fieldAddMul_cast ca0 cb0 c11 cγ, fieldMul_cast ca1 cb1, fieldAddMul_cast ca0 cb1 ca1 cb0,
      va0, va1, vb0, vb1, vγ]
    simp only [fipsMultiplyStep, fipsBaseCaseMultiply]

theorem nttMulLoop_sim {f g : Array ℤ} {F G : Poly} (hf : Rep f F) (hg : Rep g G) :
    ∀ (l : List ℕ) (h : Array ℤ) (H : Poly), (∀ i ∈ l, i < 128) → Rep h H →
      ∃ h', l.foldlM (nttMulStep f g) h = some h' ∧ Rep h' (l.foldl (fipsMultiplyStep F G) H)
  | [], h, H, _, hh => ⟨h, rfl, hh⟩
  | i :: l, h, H, hl, hh => by
    obtain ⟨h1, e1, r1⟩ := nttMulStep_sim hf hg hh (hl i (List.mem_cons_self ..))
    obtain ⟨h2, e2, r2⟩ := nttMulLoop_sim hf hg l h1 _
      (fun j hj => hl j (List.mem_cons_of_mem _ hj)) r1
    exact ⟨h2, by simp [List.foldlM_cons, e1, e2], r2⟩

theorem rep_zero : Rep (Array.replicate 256 0) (fun _ => 0) := by
  refine ⟨Array.size_replicate, fun i hi => ⟨0, ?_, ?_, by simp⟩⟩
  · rw [Array.getElem?_replicate, ite_eq_left hi]
  · unfold Canon q; norm_num

/-- **`ntt_mul` refines FIPS 203 Algorithm 11 (with Algorithm 12).** -/
theorem nttMul_refines {f g : Array ℤ} {F G : Poly} (hf : Rep f F) (hg : Rep g G) :
    ∃ out, nttMul f g = some out ∧ Rep out (fipsMultiplyNTTs F G) :=
  nttMulLoop_sim hf hg (List.range 128) _ _ (fun _ hi => List.mem_range.1 hi) rep_zero

/-! ## `poly_add`, `poly_sub` (lines 141–145) -/

/-- `Array.init n f` for an `f` that may fail (out-of-bounds access). -/
def arrayInit (n : ℕ) (f : ℕ → Option ℤ) : Option (Array ℤ) :=
  ((List.range n).mapM f).map List.toArray

/-- Model of `poly_add` (`lib/mlkem_engine.ml` lines 141–142). -/
def polyAdd (a b : Array ℤ) : Option (Array ℤ) :=
  arrayInit 256 fun i => do return fieldAdd (← getA a i) (← getA b i)

/-- Model of `poly_sub` (`lib/mlkem_engine.ml` lines 144–145). -/
def polySub (a b : Array ℤ) : Option (Array ℤ) :=
  arrayInit 256 fun i => do return fieldSub (← getA a i) (← getA b i)

theorem mapM_range'_some (f : ℕ → Option ℤ) :
    ∀ k s, (∀ i, s ≤ i → i < s + k → ∃ v, f i = some v) →
      ∃ l : List ℤ, (List.range' s k).mapM f = some l ∧ l.length = k ∧
        ∀ i < k, l[i]? = f (s + i) := by
  intro k
  induction k with
  | zero => intro s _; exact ⟨[], rfl, rfl, fun i hi => absurd hi (by omega)⟩
  | succ k ih =>
    intro s hf
    obtain ⟨v, ev⟩ := hf s le_rfl (by omega)
    obtain ⟨l, el, hl, hli⟩ := ih (s + 1) (fun i h1 h2 => hf i (by omega) (by omega))
    refine ⟨v :: l, ?_, by simp [hl], fun i hi => ?_⟩
    · rw [List.range'_succ, List.mapM_cons]
      simp [ev, el]
    · rcases i with _ | i
      · simp [ev]
      · simp only [List.getElem?_cons_succ]
        rw [hli i (by omega)]
        congr 1; ring

theorem arrayInit_rep (f : ℕ → Option ℤ) (F : Poly)
    (hf : ∀ i < 256, ∃ v, f i = some v ∧ Canon v ∧ (v : Zq) = F i) :
    ∃ out, arrayInit 256 f = some out ∧ Rep out F := by
  obtain ⟨l, el, hl, hli⟩ := mapM_range'_some f 256 0
    (fun i _ h2 => by obtain ⟨v, e, -⟩ := hf i (by omega); exact ⟨v, e⟩)
  refine ⟨l.toArray, ?_, by simp [hl], fun i hi => ?_⟩
  · simp [arrayInit, List.range_eq_range', el]
  · obtain ⟨v, e, c, cv⟩ := hf i hi
    refine ⟨v, ?_, c, cv⟩
    rw [List.getElem?_toArray, hli i hi, Nat.zero_add, e]

/-- `poly_add` is coefficient-wise addition in `ℤ_q` with canonical output. -/
theorem polyAdd_refines {a b : Array ℤ} {F G : Poly} (ha : Rep a F) (hb : Rep b G) :
    ∃ out, polyAdd a b = some out ∧ Rep out (F + G) := by
  apply arrayInit_rep
  intro i hi
  obtain ⟨u, eu, cu, vu⟩ := ha.get hi
  obtain ⟨w, ew, cw, vw⟩ := hb.get hi
  exact ⟨fieldAdd u w, by simp [eu, ew], fieldAdd_canon cu cw,
    by rw [fieldAdd_cast cu cw, vu, vw]; rfl⟩

/-- `poly_sub` is coefficient-wise subtraction in `ℤ_q` with canonical output. -/
theorem polySub_refines {a b : Array ℤ} {F G : Poly} (ha : Rep a F) (hb : Rep b G) :
    ∃ out, polySub a b = some out ∧ Rep out (F - G) := by
  apply arrayInit_rep
  intro i hi
  obtain ⟨u, eu, cu, vu⟩ := ha.get hi
  obtain ⟨w, ew, cw, vw⟩ := hb.get hi
  exact ⟨fieldSub u w, by simp [eu, ew], fieldSub_canon cu cw,
    by rw [fieldSub_cast cu cw, vu, vw]; rfl⟩

/-! ## End-to-end statements about the OCaml code -/

/-- The OCaml `ntt` computes the CRT decomposition: output pair `i` is
    `a mod (X² − γ_i)`. -/
theorem ocaml_ntt_crt {a : Array ℤ} {F : Poly} (ha : Rep a F) :
    ∃ out, ntt a = some out ∧ ∃ G, Rep out G ∧
      ∀ i < 128, (Polynomial.X ^ 2 - Polynomial.C (gamma i)) ∣
        polyOf F - (Polynomial.C (G (2 * i)) + Polynomial.C (G (2 * i + 1)) * Polynomial.X) := by
  obtain ⟨out, e, h⟩ := ntt_refines ha
  exact ⟨out, e, _, h, fun i hi => fipsNtt_crt F hi⟩

/-- `inverse_ntt ∘ ntt` is the identity on canonical arrays. -/
theorem ocaml_inverseNtt_ntt {a : Array ℤ} {F : Poly} (ha : Rep a F) :
    ∃ b c, ntt a = some b ∧ inverseNtt b = some c ∧ c = a := by
  obtain ⟨b, eb, hb⟩ := ntt_refines ha
  obtain ⟨c, ec, hc⟩ := inverseNtt_refines hb
  refine ⟨b, c, eb, ec, ?_⟩
  have hc' := hc.congr (fipsNttInv_fipsNtt F)
  apply Array.ext (by rw [hc'.1, ha.1])
  intro i h1 h2
  have hi : i < 256 := by rw [ha.1] at h2; exact h2
  obtain ⟨v, ev, cv, vv⟩ := hc'.2 i hi
  obtain ⟨w, ew, cw, vw⟩ := ha.2 i hi
  rw [Array.getElem?_eq_getElem h1] at ev
  rw [Array.getElem?_eq_getElem h2] at ew
  cases ev; cases ew
  exact Canon.eq_of_cast_eq cv cw (by rw [vv, vw])

/-- `ntt ∘ inverse_ntt` is the identity on canonical arrays. -/
theorem ocaml_ntt_inverseNtt {a : Array ℤ} {F : Poly} (ha : Rep a F) :
    ∃ b c, inverseNtt a = some b ∧ ntt b = some c ∧ c = a := by
  obtain ⟨b, eb, hb⟩ := inverseNtt_refines ha
  obtain ⟨c, ec, hc⟩ := ntt_refines hb
  refine ⟨b, c, eb, ec, ?_⟩
  have hc' := hc.congr (fipsNtt_fipsNttInv F)
  apply Array.ext (by rw [hc'.1, ha.1])
  intro i h1 h2
  have hi : i < 256 := by rw [ha.1] at h2; exact h2
  obtain ⟨v, ev, cv, vv⟩ := hc'.2 i hi
  obtain ⟨w, ew, cw, vw⟩ := ha.2 i hi
  rw [Array.getElem?_eq_getElem h1] at ev
  rw [Array.getElem?_eq_getElem h2] at ew
  cases ev; cases ew
  exact Canon.eq_of_cast_eq cv cw (by rw [vv, vw])

/-- **Polynomial multiplication via the OCaml NTT.** For canonical `a`, `b`,
    `inverse_ntt (ntt_mul (ntt a) (ntt b))` succeeds and returns the
    canonical coefficients of `a·b mod (X^256 + 1)` in `R_q`. -/
theorem ocaml_ntt_mul_correct {a b : Array ℤ} {F G : Poly} (ha : Rep a F) (hb : Rep b G) :
    ∃ na nb m c, ntt a = some na ∧ ntt b = some nb ∧ nttMul na nb = some m ∧
      inverseNtt m = some c ∧ ∃ H, Rep c H ∧
        polyOf H = rqMul (polyOf F) (polyOf G) := by
  obtain ⟨na, ea, ha'⟩ := ntt_refines ha
  obtain ⟨nb, eb, hb'⟩ := ntt_refines hb
  obtain ⟨m, em, hm⟩ := nttMul_refines ha' hb'
  obtain ⟨c, ec, hc⟩ := inverseNtt_refines hm
  refine ⟨na, nb, m, c, ea, eb, em, ec, _, hc, ?_⟩
  exact fipsNttInv_multiplyNTTs_rqMul F G

/-! ## `Portable` intermediates of the loop bodies -/

/-- Every `int` computed by one `ntt` butterfly on canonical data is
    `Portable`: the indices `j + len` (< 256), the product and remainder
    inside `field_mul`, and the operands and results of `field_sub` /
    `field_add`. -/
theorem butterfly_portable {zeta v0 v1 : ℤ} (hz : Canon zeta) (h0 : Canon v0) (h1 : Canon v1)
    {len j : ℕ} (hj : j + len < 256) :
    Portable ((j + len : ℕ) : ℤ) ∧ Portable (zeta * v1) ∧ Portable (barrettRem (zeta * v1)) ∧
      Portable (fieldMul zeta v1) ∧ Portable (v0 - fieldMul zeta v1 + q) ∧
      Portable (v0 + fieldMul zeta v1) ∧ Portable (fieldSub v0 (fieldMul zeta v1)) ∧
      Portable (fieldAdd v0 (fieldMul zeta v1)) := by
  have ht := fieldMul_canon hz h1
  obtain ⟨-, hr, -, -, -, -⟩ := fieldReduce_portable (fieldMul_arg hz h1).1 (fieldMul_arg hz h1).2
  exact ⟨Portable.of_nat_lt (by omega), (fieldMul_portable hz h1).1, hr, ht.portable, (fieldSub_portable h0 ht).2.1, (fieldAdd_portable h0 ht).1,
    (fieldSub_canon h0 ht).portable, (fieldAdd_canon h0 ht).portable⟩

/-- Every `int` computed by one `inverse_ntt` butterfly on canonical data is
    `Portable`. -/
theorem invButterfly_portable {zeta t u : ℤ} (hz : Canon zeta) (ht : Canon t) (hu : Canon u)
    {len j : ℕ} (hj : j + len < 256) :
    Portable ((j + len : ℕ) : ℤ) ∧ Portable (t + u) ∧ Portable (fieldAdd t u) ∧
      Portable (u - t) ∧ Portable (u - t + q) ∧ Portable (zeta * (u - t + q)) ∧
      Portable (fieldMulSub zeta u t) := by
  obtain ⟨p1, p2, p3, p4⟩ := fieldMulSub_portable hz hu ht
  exact ⟨Portable.of_nat_lt (by omega), (fieldAdd_portable ht hu).1,
    (fieldAdd_portable ht hu).2, p1, p2, p3, p4⟩

/-- Every `int` computed by one iteration of `ntt_mul` on canonical data is
    `Portable`. -/
theorem nttMulStep_portable {a0 a1 b0 b1 γ : ℤ} (h0 : Canon a0) (h1 : Canon a1) (h2 : Canon b0)
    (h3 : Canon b1) (hγ : Canon γ) {i : ℕ} (hi : i < 128) :
    Portable ((2 * i + 1 : ℕ) : ℤ) ∧ Portable (a1 * b1) ∧ Portable (fieldMul a1 b1) ∧
      Portable (a0 * b0 + fieldMul a1 b1 * γ) ∧ Portable (fieldAddMul a0 b0 (fieldMul a1 b1) γ) ∧
      Portable (a0 * b1 + a1 * b0) ∧ Portable (fieldAddMul a0 b1 a1 b0) := by
  have c11 := fieldMul_canon h1 h3
  exact ⟨Portable.of_nat_lt (by omega), (fieldMul_portable h1 h3).1, c11.portable,
    (fieldAddMul_portable h0 h2 c11 hγ).2.2.1, (fieldAddMul_portable h0 h2 c11 hγ).2.2.2,
    (fieldAddMul_portable h0 h3 h1 h2).2.2.1, (fieldAddMul_portable h0 h3 h1 h2).2.2.2⟩

end OcamlPq.MLKEM
