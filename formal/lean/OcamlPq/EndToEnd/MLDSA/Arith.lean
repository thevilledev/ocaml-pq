import OcamlPq.EndToEnd.MLDSA.Shake

/-!
# FIPS 204 polynomial arithmetic on `MLDSAAlg.Poly`, and the OCaml models

The arithmetic area proves the OCaml `ntt`, `inverse_ntt`, `pointwise`,
`matrix_vector_ntt`, `add_mod`, `sub_mod` correct modulo `q`
(`MLDSA.ntt_refines`, …: casts to `ℤ_q`) against transcriptions of FIPS 204
Algorithms 41, 42, 45, 48 over `ℕ → ℤ_q`. `MLDSAAlg` needs *equalities* of
functions `Poly → Poly` (`Poly = ℕ → ℤ`). This file transports the FIPS
transcriptions to `Poly` through the adapter `ofZq ∘ … ∘ toZq` (canonical
representatives) and proves the OCaml models equal to them on every input:
the OCaml outputs are canonical (`MLDSA.ntt_canonical`, …) and congruent to
the FIPS outputs, hence equal to their canonical representatives.

`inverse_ntt` and the FIPS `NTT⁻¹` leave different values at the meaningless
indices `≥ 256` (the OCaml model scales every index, Algorithm 42 only the
first 256), so both are composed with the `trunc` adapter.
-/

namespace OcamlPq.EndToEnd.MLDSA

open OcamlPq.MLDSAAlg

/-! ## FIPS 204 operations -/

/-- FIPS 204 Algorithm 41, `NTT(w)` (the arithmetic area's `nttSpec`), on
    canonical representatives. -/
def fipsNTT (p : Poly) : Poly := ofZq (MLDSA.nttSpec (toZq p))

/-- FIPS 204 Algorithm 42, `NTT⁻¹(ŵ)` (`invNttSpec`), on canonical
    representatives of the 256 coefficients. -/
def fipsNTTinv (p : Poly) : Poly := trunc (ofZq (MLDSA.invNttSpec (toZq p)))

/-- FIPS 204 Algorithm 48, `MatrixVectorNTT(M̂, v̂)` with `ℓ` columns
    (`matrixVectorRowSpec`: row `r` is `Σ_{j<ℓ} M̂[r][j] ∘ v̂[j]`). -/
def fipsMulMatVec (l : ℕ) (A : PolyMat) (v : PolyVec) : PolyVec :=
  fun r => trunc (ofZq (MLDSA.matrixVectorRowSpec l (fun j => toZq (A r j)) (fun j => toZq (v j))))

/-- FIPS 204 Algorithm 45, `MultiplyNTT(â, b̂)` (`multiplyNttSpec`). -/
def fipsMulNTT (a b : Poly) : Poly := ofZq (MLDSA.multiplyNttSpec (toZq a) (toZq b))

/-- Addition in `R_q`. -/
def fipsAddPoly (a b : Poly) : Poly := ofZq (toZq a + toZq b)

/-- Subtraction in `R_q`. -/
def fipsSubPoly (a b : Poly) : Poly := ofZq (toZq a - toZq b)

/-! ## OCaml models with the `trunc` adapter -/

/-- `inverse_ntt` (arithmetic area's model), truncated to 256 entries. -/
def ocamlInverseNtt (p : Poly) : Poly := trunc (MLDSA.inverseNtt p)

/-- `matrix_vector_ntt matrix vector` (`mldsa_engine.ml` lines 250–260): row
    `r` is the arithmetic area's `matrixVectorRow P.l matrix.(r) vector`. -/
def ocamlMatVec (l : ℕ) (A : PolyMat) (v : PolyVec) : PolyVec :=
  fun r => MLDSA.matrixVectorRow l (A r) v

/-! ## Equalities -/

/-- **`ntt` is FIPS 204 Algorithm 41** on every input and index. -/
theorem ntt_eq_fips : MLDSA.ntt = fipsNTT := by
  funext p
  exact eq_ofZq (MLDSA.ntt_canonical p) (MLDSA.ntt_refines p)

/-- **`inverse_ntt` is FIPS 204 Algorithm 42.** -/
theorem inverseNtt_eq_fips : ocamlInverseNtt = fipsNTTinv := by
  funext p i
  unfold ocamlInverseNtt fipsNTTinv trunc
  split_ifs with hi
  · rw [ofZq_apply, toZq, ← MLDSA.inverseNtt_refines p i hi]
    exact (val_cast_of_canonical (MLDSA.inverseNtt_canonical p i).1
      (MLDSA.inverseNtt_canonical p i).2).symm
  · rfl

/-- **`pointwise` is FIPS 204 Algorithm 45.** -/
theorem pointwise_eq_fips : MLDSA.pointwise = fipsMulNTT := by
  funext a b
  exact eq_ofZq (MLDSA.pointwise_canonical a b) (MLDSA.pointwise_refines a b)

theorem addMod_eq_fips (a b : Poly) : (fun i => MLDSA.addMod (a i) (b i)) = fipsAddPoly a b := by
  funext i
  unfold fipsAddPoly ofZq toZq MLDSA.castArr
  rw [MLDSA.addMod_eq, ← val_cast]; push_cast; rfl

theorem subMod_eq_fips (a b : Poly) : (fun i => MLDSA.subMod (a i) (b i)) = fipsSubPoly a b := by
  funext i
  unfold fipsSubPoly ofZq toZq MLDSA.castArr
  rw [MLDSA.subMod_eq, ← val_cast]; push_cast; rfl

/-- The inner loop of `matrix_vector_ntt` adds the product at every index
    below `n`. -/
theorem mvr_inner (acc p : ℕ → ℤ) (n : ℕ) :
    (List.range n).foldl (fun accumulator coefficient =>
        Function.update accumulator coefficient
          (MLDSA.addMod (accumulator coefficient) (p coefficient))) acc =
      fun k => if k < n then MLDSA.addMod (acc k) (p k) else acc k := by
  induction n with
  | zero => funext k; simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    funext k
    simp only [List.foldl_cons, List.foldl_nil, Function.update_apply, lt_irrefl, ite_false]
    by_cases hk : k = n
    · subst hk; simp
    · simp only [hk, ite_false]
      split_ifs <;> first | rfl | omega

/-- `matrix_vector_ntt` rows are canonical and zero beyond index 255. -/
theorem matrixVectorRow_canonical (l : ℕ) (A v : ℕ → ℕ → ℤ) (i : ℕ) :
    (0 ≤ MLDSA.matrixVectorRow l A v i ∧ MLDSA.matrixVectorRow l A v i < MLDSA.q) ∧
      (256 ≤ i → MLDSA.matrixVectorRow l A v i = 0) := by
  unfold MLDSA.matrixVectorRow
  induction l generalizing i with
  | zero => simp [MLDSA.q]
  | succ l ih =>
    rw [List.range_succ (n := l), List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [mvr_inner]
    beta_reduce
    split_ifs with hi
    · exact ⟨⟨MLDSA.norm_nonneg _, MLDSA.norm_lt _⟩, fun h => by omega⟩
    · exact ih i

/-- **`matrix_vector_ntt` is FIPS 204 Algorithm 48.** -/
theorem matVec_eq_fips (l : ℕ) : ocamlMatVec l = fipsMulMatVec l := by
  funext A v r i
  unfold ocamlMatVec fipsMulMatVec trunc
  split_ifs with hi
  · rw [ofZq_apply]
    have h := MLDSA.matrixVectorRow_refines l (A r) v i hi
    unfold MLDSA.castArr at h
    have hc := (matrixVectorRow_canonical l (A r) v i).1
    rw [← val_cast_of_canonical hc.1 hc.2, h]
    rfl
  · exact (matrixVectorRow_canonical l (A r) v i).2 (by omega)

/-- `MatrixVectorNTT` with `ℓ` columns only reads columns `< ℓ`. -/
theorem fipsMulMatVec_local (l : ℕ) (A A' : PolyMat) (v v' : PolyVec) (r : ℕ)
    (hA : ∀ s < l, A r s = A' r s) (hv : ∀ s < l, v s = v' s) :
    fipsMulMatVec l A v r = fipsMulMatVec l A' v' r := by
  unfold fipsMulMatVec MLDSA.matrixVectorRowSpec
  congr 2
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  beta_reduce
  rw [hA j hj, hv j hj]

theorem fipsNTTinv_lt (p : Poly) (i : ℕ) : 0 ≤ fipsNTTinv p i ∧ fipsNTTinv p i < MLDSA.q := by
  unfold fipsNTTinv trunc
  split_ifs
  · exact ⟨ofZq_nonneg _ _, ofZq_lt _ _⟩
  · simp [MLDSA.q]

end OcamlPq.EndToEnd.MLDSA
