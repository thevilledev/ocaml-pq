import OcamlPq.MLDSA.Tables

/-!
# NTT and inverse NTT: models, FIPS 204 specifications, refinement

Models of `ntt`, `inverse_ntt`, `pointwise` and `matrix_vector_ntt`
(mldsa/mldsa_engine.ml:206–260) and transcriptions of FIPS 204
Algorithms 41 (`NTT`), 42 (`NTT⁻¹`), 45 (`MultiplyNTT`) and 48
(`MatrixVectorNTT`) over `ℤ_q`.

An OCaml `int array` of length 256 is modelled by its index function
`ℕ → ℤ`; only indices below 256 are meaningful. `Array.map norm` becomes
`fun i => norm (a i)`; `result.(i) <- v` becomes `Function.update`.
Every `while` loop is a well-founded recursion whose guard is the OCaml
guard (the positivity of `length`, which the OCaml loop needs to terminate,
is threaded through as a proof argument).
-/

namespace OcamlPq.MLDSA

/-! ## `bit_reverse_8` only looks at the low 8 bits -/

theorem bitReverse8_mod (m : ℕ) : bitReverse8 m = bitReverse8 (m % 256) := by
  unfold bitReverse8
  apply List.foldl_ext
  intro result bit hbit
  rw [List.mem_range] at hbit
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod,
    Nat.and_one_is_mod]
  congr 1
  interval_cases bit <;> norm_num <;> omega

theorem bitRev8_mod (m : ℕ) : bitRev8 m = bitRev8 (m % 256) := by
  unfold bitRev8
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  congr 1
  interval_cases i <;> norm_num <;> omega

theorem bitReverse8_eq_bitRev8_all (m : ℕ) : bitReverse8 m = bitRev8 m := by
  rw [bitReverse8_mod, bitRev8_mod]
  exact bitReverse8_eq_bitRev8 _ (Nat.mod_lt _ (by norm_num))

theorem zetas_cast_all (k : ℕ) : ((zetas k : ℤ) : Zq) = zetaSpec k := by
  rw [zetas, powMod_cast, bitReverse8_eq_bitRev8_all, zetaSpec, ζ]; push_cast; rfl

/-! ## Models -/

/-- Model of the innermost `for j = !start to !start + !length - 1` loop of
    `ntt` (mldsa/mldsa_engine.ml:215–220). -/
def nttButterflies (zeta : ℤ) (length start : ℕ) (result : ℕ → ℤ) : ℕ → ℤ :=
  (List.range length).foldl
    (fun result i =>
      let j := start + i
      let t := mulMod zeta (result (j + length))
      let value := result j
      let result := Function.update result j (addMod value t)
      Function.update result (j + length) (subMod value t))
    result

/-- Model of the `while !start < n` loop of `ntt`
    (mldsa/mldsa_engine.ml:212–222); returns the array and `!index`. -/
def nttBlocks (length : ℕ) (hlength : 0 < length) (start index : ℕ) (result : ℕ → ℤ) :
    (ℕ → ℤ) × ℕ :=
  if start < 256 then
    let index := index + 1
    let zeta := zetas index
    nttBlocks length hlength (start + 2 * length) index (nttButterflies zeta length start result)
  else (result, index)
termination_by 256 - start

/-- Model of the `while !length > 0` loop of `ntt`
    (mldsa/mldsa_engine.ml:210–224). -/
def nttLayers (length index : ℕ) (result : ℕ → ℤ) : ℕ → ℤ :=
  if h : length > 0 then
    let r := nttBlocks length h 0 index result
    nttLayers (length / 2) r.2 r.1
  else result
termination_by length

/-- Model of `ntt` (mldsa/mldsa_engine.ml:206–225). -/
def ntt (polynomial : ℕ → ℤ) : ℕ → ℤ := nttLayers 128 0 (fun i => norm (polynomial i))

/-- Model of the innermost loop of `inverse_ntt` (mldsa/mldsa_engine.ml:236–241). -/
def invButterflies (zeta : ℤ) (length start : ℕ) (result : ℕ → ℤ) : ℕ → ℤ :=
  (List.range length).foldl
    (fun result i =>
      let j := start + i
      let left := result j
      let right := result (j + length)
      let result := Function.update result j (addMod left right)
      Function.update result (j + length) (mulMod zeta (subMod left right)))
    result

/-- Model of the `while !start < n` loop of `inverse_ntt`
    (mldsa/mldsa_engine.ml:233–243); `decr index` is `index - 1` (the index
    never drops below 1, see `invSpecMiddle_eq`). -/
def invBlocks (length : ℕ) (hlength : 0 < length) (start index : ℕ) (result : ℕ → ℤ) :
    (ℕ → ℤ) × ℕ :=
  if start < 256 then
    let index := index - 1
    let zeta := norm (-zetas index)
    invBlocks length hlength (start + 2 * length) index (invButterflies zeta length start result)
  else (result, index)
termination_by 256 - start

/-- Model of the `while !length < n` loop of `inverse_ntt`
    (mldsa/mldsa_engine.ml:231–245). -/
def invLayers (length : ℕ) (hlength : 0 < length) (index : ℕ) (result : ℕ → ℤ) : ℕ → ℤ :=
  if length < 256 then
    let r := invBlocks length hlength 0 index result
    invLayers (length * 2) (by omega) r.2 r.1
  else result
termination_by 256 - length

/-- Model of `inverse_ntt` (mldsa/mldsa_engine.ml:227–246). -/
def inverseNtt (polynomial : ℕ → ℤ) : ℕ → ℤ :=
  let result := invLayers 1 (by decide) 256 (fun i => norm (polynomial i))
  fun i => mulMod inverseN (result i)

/-- Model of `pointwise` (mldsa/mldsa_engine.ml:248). -/
def pointwise (left right : ℕ → ℤ) : ℕ → ℤ := fun i => mulMod (left i) (right i)

/-- Model of the body of `matrix_vector_ntt` for one row
    (mldsa/mldsa_engine.ml:250–260): the accumulator starts at zero and, for
    each column, every coefficient is `add_mod`-ed with the pointwise
    product. -/
def matrixVectorRow (l : ℕ) (matrixRow : ℕ → ℕ → ℤ) (vector : ℕ → ℕ → ℤ) : ℕ → ℤ :=
  (List.range l).foldl
    (fun accumulator column =>
      let product := pointwise (matrixRow column) (vector column)
      (List.range 256).foldl
        (fun accumulator coefficient =>
          Function.update accumulator coefficient
            (addMod (accumulator coefficient) (product coefficient)))
        accumulator)
    (fun _ => 0)

/-! ## Specifications (FIPS 204) -/

/-- FIPS 204 Algorithm 41, lines 8–12 (inner `for` loop). -/
def nttSpecInner (z : Zq) (len start : ℕ) (w : ℕ → Zq) : ℕ → Zq :=
  (List.range len).foldl
    (fun w i =>
      let j := start + i
      let t := z * w (j + len)
      let w := Function.update w (j + len) (w j - t)
      Function.update w j (w j + t))
    w

/-- FIPS 204 Algorithm 41, lines 5–14 (`while start < 256`). -/
def nttSpecMiddle (len : ℕ) (hlen : 1 ≤ len) (start m : ℕ) (w : ℕ → Zq) : (ℕ → Zq) × ℕ :=
  if start < 256 then
    let m := m + 1
    let z := zetaSpec m
    nttSpecMiddle len hlen (start + 2 * len) m (nttSpecInner z len start w)
  else (w, m)
termination_by 256 - start

/-- FIPS 204 Algorithm 41, lines 4–16 (`while len ≥ 1`). -/
def nttSpecOuter (len m : ℕ) (w : ℕ → Zq) : ℕ → Zq :=
  if h : len ≥ 1 then
    let r := nttSpecMiddle len h 0 m w
    nttSpecOuter (len / 2) r.2 r.1
  else w
termination_by len

/-- FIPS 204 Algorithm 41, `NTT(w)` (the copy loop of lines 1–2 is the
    identity on the index function). -/
def nttSpec (w : ℕ → Zq) : ℕ → Zq := nttSpecOuter 128 0 w

/-- FIPS 204 Algorithm 42, lines 8–13 (inner `for` loop). -/
def invSpecInner (z : Zq) (len start : ℕ) (w : ℕ → Zq) : ℕ → Zq :=
  (List.range len).foldl
    (fun w i =>
      let j := start + i
      let t := w j
      let w := Function.update w j (t + w (j + len))
      let w := Function.update w (j + len) (t - w (j + len))
      Function.update w (j + len) (z * w (j + len)))
    w

/-- FIPS 204 Algorithm 42, lines 5–15 (`while start < 256`). -/
def invSpecMiddle (len : ℕ) (hlen : 1 ≤ len) (start m : ℕ) (w : ℕ → Zq) : (ℕ → Zq) × ℕ :=
  if start < 256 then
    let m := m - 1
    let z := -zetaSpec m
    invSpecMiddle len hlen (start + 2 * len) m (invSpecInner z len start w)
  else (w, m)
termination_by 256 - start

/-- FIPS 204 Algorithm 42, lines 4–17 (`while len < 256`). -/
def invSpecOuter (len : ℕ) (hlen : 1 ≤ len) (m : ℕ) (w : ℕ → Zq) : ℕ → Zq :=
  if len < 256 then
    let r := invSpecMiddle len hlen 0 m w
    invSpecOuter (2 * len) (by omega) r.2 r.1
  else w
termination_by 256 - len

/-- FIPS 204 Algorithm 42, `NTT⁻¹(ŵ)`, including the final scaling by
    `f = 8347681` (lines 18–21). -/
def invNttSpec (wHat : ℕ → Zq) : ℕ → Zq :=
  let w := invSpecOuter 1 le_rfl 256 wHat
  let f : Zq := 8347681
  (List.range 256).foldl (fun w j => Function.update w j (f * w j)) w

/-- FIPS 204 Algorithm 45, `MultiplyNTT(â, b̂)`. -/
def multiplyNttSpec (a b : ℕ → Zq) : ℕ → Zq := fun i => a i * b i

/-- FIPS 204 Algorithms 44/45/48: row `i` of `MatrixVectorNTT(Â, v̂)` is
    `Σ_j Â[i][j] ∘ v̂[j]`. -/
def matrixVectorRowSpec (l : ℕ) (matrixRow : ℕ → ℕ → Zq) (vector : ℕ → ℕ → Zq) : ℕ → Zq :=
  fun i => ∑ j ∈ Finset.range l, matrixRow j i * vector j i

/-! ## Refinement: the models compute the specifications in `ℤ_q` -/

/-- Casting an `int` array to `ℤ_q`. -/
def castArr (a : ℕ → ℤ) : ℕ → Zq := fun i => (a i : Zq)

theorem castArr_update (a : ℕ → ℤ) (j : ℕ) (v : ℤ) :
    castArr (Function.update a j v) = Function.update (castArr a) j (v : Zq) := by
  funext k
  unfold castArr
  by_cases h : k = j
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem nttButterflies_cast (zeta : ℤ) (len start : ℕ) (hlen : 0 < len) (a : ℕ → ℤ) :
    castArr (nttButterflies zeta len start a) =
      nttSpecInner (zeta : Zq) len start (castArr a) := by
  unfold nttButterflies nttSpecInner
  generalize List.range len = l
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    funext k
    have hne : start + i ≠ start + i + len := by omega
    simp only [castArr, Function.update_apply]
    split_ifs with h1 h2 h2 <;>
      simp_all [addMod_cast, subMod_cast, mulMod_cast]

theorem nttBlocks_cast (len : ℕ) (hlen : 0 < len) (start index : ℕ) (a : ℕ → ℤ) :
    castArr (nttBlocks len hlen start index a).1 =
        (nttSpecMiddle len hlen start index (castArr a)).1 ∧
      (nttBlocks len hlen start index a).2 = (nttSpecMiddle len hlen start index (castArr a)).2 := by
  rw [nttBlocks, nttSpecMiddle]
  split_ifs with h
  · have ih := nttBlocks_cast len hlen (start + 2 * len) (index + 1)
      (nttButterflies (zetas (index + 1)) len start a)
    rw [nttButterflies_cast _ _ _ hlen, zetas_cast_all] at ih
    exact ih
  · exact ⟨rfl, rfl⟩
termination_by 256 - start

theorem nttLayers_cast (len index : ℕ) (a : ℕ → ℤ) :
    castArr (nttLayers len index a) = nttSpecOuter len index (castArr a) := by
  rw [nttLayers, nttSpecOuter]
  split_ifs with h1 h2 h2
  · obtain ⟨e1, e2⟩ := nttBlocks_cast len h1 0 index a
    have ih := nttLayers_cast (len / 2) (nttBlocks len h1 0 index a).2
      (nttBlocks len h1 0 index a).1
    rw [ih, e1, e2]
  · omega
  · omega
  · rfl
termination_by len
decreasing_by omega

/-- **`ntt` refines FIPS 204 Algorithm 41**: casting the output of the OCaml
    `ntt` to `ℤ_q` gives `NTT` of the input's residues (every index). -/
theorem ntt_refines (a : ℕ → ℤ) : castArr (ntt a) = nttSpec (castArr a) := by
  unfold ntt nttSpec
  rw [nttLayers_cast]
  congr 1
  funext i
  exact norm_cast (a i)

theorem invButterflies_cast (zeta : ℤ) (len start : ℕ) (hlen : 0 < len) (a : ℕ → ℤ) :
    castArr (invButterflies zeta len start a) =
      invSpecInner (zeta : Zq) len start (castArr a) := by
  unfold invButterflies invSpecInner
  generalize List.range len = l
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    funext k
    have hne : start + i ≠ start + i + len := by omega
    simp only [castArr, Function.update_apply]
    split_ifs with h1 h2 h2 <;>
      simp_all [addMod_cast, subMod_cast, mulMod_cast]

theorem invBlocks_cast (len : ℕ) (hlen : 0 < len) (start index : ℕ) (a : ℕ → ℤ) :
    castArr (invBlocks len hlen start index a).1 =
        (invSpecMiddle len hlen start index (castArr a)).1 ∧
      (invBlocks len hlen start index a).2 = (invSpecMiddle len hlen start index (castArr a)).2 := by
  rw [invBlocks, invSpecMiddle]
  split_ifs with h
  · have ih := invBlocks_cast len hlen (start + 2 * len) (index - 1)
      (invButterflies (norm (-zetas (index - 1))) len start a)
    rw [invButterflies_cast _ _ _ hlen, norm_cast] at ih
    push_cast at ih
    rw [zetas_cast_all] at ih
    exact ih
  · exact ⟨rfl, rfl⟩
termination_by 256 - start

theorem invSpecOuter_congr {len len' : ℕ} (e : len = len') (h : 1 ≤ len) (h' : 1 ≤ len')
    (m : ℕ) (w : ℕ → Zq) : invSpecOuter len h m w = invSpecOuter len' h' m w := by
  subst e; rfl

theorem invLayers_cast (len : ℕ) (hlen : 0 < len) (index : ℕ) (a : ℕ → ℤ) :
    castArr (invLayers len hlen index a) = invSpecOuter len hlen index (castArr a) := by
  rw [invLayers, invSpecOuter]
  split_ifs with h
  · obtain ⟨e1, e2⟩ := invBlocks_cast len hlen 0 index a
    have ih := invLayers_cast (len * 2) (by omega) (invBlocks len hlen 0 index a).2
      (invBlocks len hlen 0 index a).1
    rw [ih, e1, e2]
    exact invSpecOuter_congr (by omega) _ _ _ _
  · rfl
termination_by 256 - len

/-- The final scaling loop of Algorithm 42 in closed form. -/
theorem scale_loop_eq (f : Zq) (w : ℕ → Zq) :
    (List.range 256).foldl (fun w j => Function.update w j (f * w j)) w =
      fun k => if k < 256 then f * w k else w k := by
  have key : ∀ n, (List.range n).foldl (fun w j => Function.update w j (f * w j)) w =
      fun k => if k < n then f * w k else w k := by
    intro n
    induction n with
    | zero => funext k; simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih]
      funext k
      simp only [List.foldl_cons, List.foldl_nil, Function.update_apply]
      split_ifs <;> first | omega | (subst_vars; rfl)
  exact key 256

/-- **`inverse_ntt` refines FIPS 204 Algorithm 42** on every index below
    256. -/
theorem inverseNtt_refines (a : ℕ → ℤ) (k : ℕ) (hk : k < 256) :
    castArr (inverseNtt a) k = invNttSpec (castArr a) k := by
  unfold inverseNtt invNttSpec
  rw [scale_loop_eq]
  simp only [castArr, hk, ite_true, mulMod_cast]
  have := congrFun (invLayers_cast 1 (by decide) 256 (fun i => norm (a i))) k
  simp only [castArr] at this
  rw [this]
  have h8 : ((inverseN : ℤ) : Zq) = 8347681 := by rw [inverseN_eq]; rfl
  rw [h8]
  congr 2
  funext i
  exact norm_cast (a i)

/-- **`pointwise` refines FIPS 204 Algorithm 45**. -/
theorem pointwise_refines (a b : ℕ → ℤ) :
    castArr (pointwise a b) = multiplyNttSpec (castArr a) (castArr b) := by
  funext i; simp [castArr, pointwise, multiplyNttSpec, mulMod_cast]

/-- **`matrix_vector_ntt` refines FIPS 204 Algorithm 48** on every
    coefficient below 256 (for each row). -/
theorem matrixVectorRow_refines (l : ℕ) (matrixRow vector : ℕ → ℕ → ℤ) (i : ℕ)
    (hi : i < 256) :
    castArr (matrixVectorRow l matrixRow vector) i =
      matrixVectorRowSpec l (fun j => castArr (matrixRow j)) (fun j => castArr (vector j)) i := by
  -- the inner loop adds the product at every coefficient below 256
  have inner : ∀ (acc : ℕ → ℤ) (p : ℕ → ℤ) (n : ℕ),
      castArr ((List.range n).foldl
        (fun accumulator coefficient =>
          Function.update accumulator coefficient
            (addMod (accumulator coefficient) (p coefficient))) acc) =
        fun k => if k < n then castArr acc k + castArr p k else castArr acc k := by
    intro acc p n
    induction n with
    | zero => funext k; simp
    | succ n ih =>
      rw [List.range_succ (n := n), List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have hX := congrFun ih n
      simp only [castArr, lt_irrefl, ite_false] at hX
      rw [castArr_update, ih]
      funext k
      simp only [Function.update_apply, addMod_cast, hX]
      split_ifs <;> first | omega | (subst_vars; simp [castArr])
  unfold matrixVectorRow matrixVectorRowSpec
  have outer : ∀ n, castArr ((List.range n).foldl
      (fun accumulator column =>
        let product := pointwise (matrixRow column) (vector column)
        (List.range 256).foldl
          (fun accumulator coefficient =>
            Function.update accumulator coefficient
              (addMod (accumulator coefficient) (product coefficient)))
          accumulator)
      (fun _ => 0)) i =
      ∑ j ∈ Finset.range n, castArr (matrixRow j) i * castArr (vector j) i := by
    intro n
    induction n with
    | zero => simp [castArr]
    | succ n ih =>
      rw [List.range_succ (n := n), List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [inner, Finset.sum_range_succ, ← ih]
      simp only [hi, ite_true, pointwise_refines, multiplyNttSpec]
  exact outer l

/-! ## Canonical outputs and portability -/

/-- All entries of an array are canonical residues in `[0, q)`. -/
def Canonical (a : ℕ → ℤ) : Prop := ∀ i, 0 ≤ a i ∧ a i < q

theorem nttButterflies_canonical (zeta : ℤ) (len start : ℕ) (a : ℕ → ℤ) (ha : Canonical a) :
    Canonical (nttButterflies zeta len start a) := by
  unfold nttButterflies
  generalize List.range len = l
  induction l generalizing a with
  | nil => exact ha
  | cons i l ih =>
    apply ih
    intro k
    simp only [Function.update_apply]
    split_ifs
    · exact ⟨norm_nonneg _, norm_lt _⟩
    · exact ⟨norm_nonneg _, norm_lt _⟩
    · exact ha k

theorem nttBlocks_canonical (len : ℕ) (hlen : 0 < len) (start index : ℕ) (a : ℕ → ℤ)
    (ha : Canonical a) : Canonical (nttBlocks len hlen start index a).1 := by
  rw [nttBlocks]
  split_ifs
  · exact nttBlocks_canonical len hlen _ _ _ (nttButterflies_canonical _ _ _ _ ha)
  · exact ha
termination_by 256 - start

theorem nttLayers_canonical (len index : ℕ) (a : ℕ → ℤ) (ha : Canonical a) :
    Canonical (nttLayers len index a) := by
  rw [nttLayers]
  split_ifs with h
  · exact nttLayers_canonical _ _ _ (nttBlocks_canonical _ _ _ _ _ ha)
  · exact ha
termination_by len
decreasing_by omega

/-- `ntt` returns canonical coefficients in `[0, q)`. -/
theorem ntt_canonical (a : ℕ → ℤ) : Canonical (ntt a) :=
  nttLayers_canonical _ _ _ (fun _ => ⟨norm_nonneg _, norm_lt _⟩)

/-- `inverse_ntt` returns canonical coefficients in `[0, q)`. -/
theorem inverseNtt_canonical (a : ℕ → ℤ) : Canonical (inverseNtt a) :=
  fun _ => ⟨mulMod_nonneg _ _, mulMod_lt _ _⟩

theorem pointwise_canonical (a b : ℕ → ℤ) : Canonical (pointwise a b) :=
  fun _ => ⟨mulMod_nonneg _ _, mulMod_lt _ _⟩

/-- In a butterfly on canonical inputs, the `int` sum and difference passed
    to `add_mod`/`sub_mod` are portable (they lie in `(-q, 2q)`), and so are
    the ones of the inverse butterfly. -/
theorem butterfly_portable {v t : ℤ} (hv0 : 0 ≤ v) (hv1 : v < q) (ht0 : 0 ≤ t) (ht1 : t < q) :
    Portable (v + t) ∧ Portable (v - t) := by
  simp only [Portable, q] at *; omega

/-- Every array index accessed by `ntt`/`inverse_ntt` is below 256 and every
    `zetas` index lies in `[1, 255]`: for the lengths `2^(7-s)` the loops
    use, block `b < 2^s` starts at `2·len·b`, touches `j` and `j + len` for
    `j < start + len`, and uses `zetas.(2^s + b)` (forward) and
    `zetas.(2^(s+1) - 1 - b)` (inverse). -/
theorem ntt_indices_in_bounds :
    ∀ s < 8, ∀ b < 2 ^ s, ∀ i < 2 ^ (7 - s),
      2 * 2 ^ (7 - s) * b + i + 2 ^ (7 - s) < 256 ∧
      1 ≤ 2 ^ s + b ∧ 2 ^ s + b < 256 ∧
      1 ≤ 2 ^ (s + 1) - 1 - b ∧ 2 ^ (s + 1) - 1 - b < 256 := by
  intro s hs b hb i hi
  interval_cases s <;> norm_num at * <;> omega

end OcamlPq.MLDSA
