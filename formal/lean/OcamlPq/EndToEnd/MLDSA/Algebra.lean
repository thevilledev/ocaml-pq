import OcamlPq.EndToEnd.MLDSA.Verify

/-!
# The verifier's `w′_approx` for an honest signature

For a key `t = A·s1 + s2 = t1·2^d + t0` and a signature with
`z = y + c·s1`, the verifier's
`w′_approx = NTT⁻¹(Â ∘ NTT(z) − NTT(c) ∘ NTT(t1·2^d))` is congruent modulo `q`
to the signer's `w − c·s2 + c·t0` (with `w = NTT⁻¹(Â ∘ NTT(y))`), coefficient
by coefficient. This is the algebraic hypothesis `happrox` of the arithmetic
area's `verify_recovers_w1_of_accepted`, proved here for the OCaml models
(`verifier_approx`) from the arithmetic area's NTT theorems: the NTT is
evaluation at the 256 odd powers of `ζ` (`nttSpec_eq_eval`), hence additive
and injective on the first 256 coefficients, `NTT ∘ NTT⁻¹ = id`
(`nttSpec_invNttSpec`), and the OCaml `ntt`, `inverse_ntt`, `pointwise`,
`matrix_vector_ntt`, `add_mod`, `sub_mod`, `center` refine them modulo `q`.
The whole computation happens in the NTT domain, where it is a ring identity.
-/

namespace OcamlPq.EndToEnd.MLDSA

open OcamlPq.MLDSAAlg
open Polynomial

/-! ## The NTT as evaluation -/

/-- NTT coordinate `k` of the residues of an integer array. -/
def nttAt (a : Poly) (k : ℕ) : MLDSA.Zq := MLDSA.nttSpec (MLDSA.castArr a) k

theorem toPoly_add (v w : ℕ → MLDSA.Zq) :
    MLDSA.toPoly (fun i => v i + w i) = MLDSA.toPoly v + MLDSA.toPoly w := by
  unfold MLDSA.toPoly
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [C_add, add_mul]

theorem toPoly_sub (v w : ℕ → MLDSA.Zq) :
    MLDSA.toPoly (fun i => v i - w i) = MLDSA.toPoly v - MLDSA.toPoly w := by
  unfold MLDSA.toPoly
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [C_sub, sub_mul]

theorem nttAt_congr {a b : Poly} (h : ∀ i < 256, (a i : MLDSA.Zq) = (b i : MLDSA.Zq)) (k : ℕ)
    (hk : k < 256) : nttAt a k = nttAt b k :=
  MLDSA.nttSpec_congr (fun i hi => h i hi) k hk

theorem nttAt_add (a b : Poly) (k : ℕ) (hk : k < 256) :
    nttAt (fun i => a i + b i) k = nttAt a k + nttAt b k := by
  unfold nttAt
  rw [MLDSA.nttSpec_eq_eval _ k hk, MLDSA.nttSpec_eq_eval _ k hk, MLDSA.nttSpec_eq_eval _ k hk,
    ← eval_add, ← toPoly_add]
  congr 2
  funext i
  simp [MLDSA.castArr]

theorem nttAt_sub (a b : Poly) (k : ℕ) (hk : k < 256) :
    nttAt (fun i => a i - b i) k = nttAt a k - nttAt b k := by
  unfold nttAt
  rw [MLDSA.nttSpec_eq_eval _ k hk, MLDSA.nttSpec_eq_eval _ k hk, MLDSA.nttSpec_eq_eval _ k hk,
    ← eval_sub, ← toPoly_sub]
  congr 2
  funext i
  simp [MLDSA.castArr]

/-- `NTT(inverse_ntt x) = x` in `ℤ_q` (first 256 coordinates). -/
theorem nttAt_inverseNtt (x : Poly) (k : ℕ) (hk : k < 256) :
    nttAt (ocamlInverseNtt x) k = (x k : MLDSA.Zq) := by
  unfold nttAt
  rw [MLDSA.nttSpec_congr (w := MLDSA.invNttSpec (MLDSA.castArr x)) (fun i hi => by
    rw [← MLDSA.inverseNtt_refines x i hi]; simp [MLDSA.castArr, ocamlInverseNtt, trunc, hi]) k hk,
    MLDSA.nttSpec_invNttSpec]
  rfl

theorem castArr_ntt (a : Poly) (k : ℕ) : (MLDSA.ntt a k : MLDSA.Zq) = nttAt a k :=
  congrFun (MLDSA.ntt_refines a) k

set_option maxRecDepth 20000 in
/-- The NTT is injective on the first 256 coefficients (a polynomial of
    degree `< 256` is determined by its values at the 256 roots `ω_k`). -/
theorem nttAt_inj {a b : Poly} (h : ∀ k < 256, nttAt a k = nttAt b k) (i : ℕ) (hi : i < 256) :
    a i % MLDSA.q = b i % MLDSA.q := by
  have hp : MLDSA.toPoly (MLDSA.castArr a) = MLDSA.toPoly (MLDSA.castArr b) := by
    apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq ((Finset.range 256).image MLDSA.ω)
    · have hcard : ((Finset.range 256).image MLDSA.ω).card = 256 := by
        rw [Finset.card_image_of_injOn]
        · exact Finset.card_range 256
        · intro x hx y hy hxy
          simp only [Finset.coe_range, Set.mem_Iio] at hx hy
          exact MLDSA.ω_injOn x y hx hy hxy
      rw [hcard]
      calc (MLDSA.toPoly (MLDSA.castArr a) - MLDSA.toPoly (MLDSA.castArr b)).degree
          ≤ max (MLDSA.toPoly (MLDSA.castArr a)).degree (MLDSA.toPoly (MLDSA.castArr b)).degree :=
            degree_sub_le _ _
        _ < ((256 : ℕ) : WithBot ℕ) := max_lt (MLDSA.toPoly_degree _) (MLDSA.toPoly_degree _)
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_range] at hk
      rw [← MLDSA.nttSpec_eq_eval _ k hk, ← MLDSA.nttSpec_eq_eval _ k hk]
      exact h k hk
  have := MLDSA.toPoly_inj hp i hi
  simp only [MLDSA.castArr] at this
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
  simp only [MLDSA.q]
  omega

/-! ## Row `r` of `matrix_vector_ntt` in the NTT domain -/

theorem nttAt_matVec (l : ℕ) (A : PolyMat) (v : PolyVec) (r k : ℕ) (hk : k < 256) :
    nttAt (ocamlInverseNtt (ocamlMatVec l A (fun j => MLDSA.ntt (v j)) r)) k =
      ∑ j ∈ Finset.range l, (A r j k : MLDSA.Zq) * nttAt (v j) k := by
  rw [nttAt_inverseNtt _ k hk]
  have : ((ocamlMatVec l A (fun j => MLDSA.ntt (v j)) r k : ℤ) : MLDSA.Zq) =
      ∑ j ∈ Finset.range l, (A r j k : MLDSA.Zq) * (MLDSA.ntt (v j) k : MLDSA.Zq) :=
    MLDSA.matrixVectorRow_refines l (A r) (fun j => MLDSA.ntt (v j)) k hk
  rw [this]
  apply Finset.sum_congr rfl
  intro j _
  rw [castArr_ntt]

/-- `center (inverse_ntt (pointwise (ntt c) (ntt s)))` in the NTT domain is
    `NTT(c) · NTT(s)`. -/
theorem nttAt_centeredProduct (c s : Poly) (k : ℕ) (hk : k < 256) :
    nttAt (ocamlCenteredProduct (MLDSA.ntt c) (MLDSA.ntt s)) k = nttAt c k * nttAt s k := by
  rw [nttAt_congr (b := ocamlInverseNtt (MLDSA.pointwise (MLDSA.ntt c) (MLDSA.ntt s)))
    (fun i hi => by
      simp only [ocamlCenteredProduct, ocamlInverseNtt, trunc, hi, ite_true, MLDSA.center_cast])
    k hk, nttAt_inverseNtt _ k hk]
  simp only [MLDSA.pointwise]
  rw [MLDSA.mulMod_cast, castArr_ntt, castArr_ntt]

/-! ## The verifier's approximation -/

/-- **`w′_approx ≡ w − c·s2 + c·t0 (mod q)`** for the OCaml models. Row `r`:
    the signer's `w = inverse_ntt (Â·ntt y)`, `cs2 = center (inverse_ntt (ĉ ∘
    ntt s2))`, `ct0` likewise; the verifier's `z` agrees with `y + cs1` and
    its `t1` with the key's, and `t1·2^13 + t0 ≡ t = inverse_ntt (Â·ntt s1) +
    s2`. -/
theorem verifier_approx (l : ℕ) (A : PolyMat) (r : ℕ) (s1 y zD : PolyVec) (s2r t0r t1D : Poly)
    (c : Poly)
    (hz : ∀ s < l, ∀ i < 256,
      zD s i = y s i + ocamlCenteredProduct (MLDSA.ntt c) (MLDSA.ntt (s1 s)) i)
    (ht : ∀ i < 256, (t1D i * 2 ^ 13 + t0r i) % MLDSA.q =
      MLDSA.addMod (ocamlInverseNtt (ocamlMatVec l A (fun j => MLDSA.ntt (s1 j)) r) i) (s2r i) %
        MLDSA.q)
    (i : ℕ) (hi : i < 256) :
    ocamlInverseNtt (fun idx => MLDSA.subMod (ocamlMatVec l A (fun j => MLDSA.ntt (zD j)) r idx)
        (MLDSA.pointwise (MLDSA.ntt c) (MLDSA.ntt (fun i => t1D i * 2 ^ 13)) idx)) i % MLDSA.q =
      (ocamlInverseNtt (ocamlMatVec l A (fun j => MLDSA.ntt (y j)) r) i
        - ocamlCenteredProduct (MLDSA.ntt c) (MLDSA.ntt s2r) i
        + ocamlCenteredProduct (MLDSA.ntt c) (MLDSA.ntt t0r) i) % MLDSA.q := by
  apply nttAt_inj _ i hi
  intro k hk
  -- left side
  rw [nttAt_inverseNtt _ k hk]
  simp only [MLDSA.subMod_cast, MLDSA.pointwise, MLDSA.mulMod_cast, castArr_ntt]
  have hM : ((ocamlMatVec l A (fun j => MLDSA.ntt (zD j)) r k : ℤ) : MLDSA.Zq) =
      ∑ j ∈ Finset.range l, (A r j k : MLDSA.Zq) * (MLDSA.ntt (zD j) k : MLDSA.Zq) :=
    MLDSA.matrixVectorRow_refines l (A r) (fun j => MLDSA.ntt (zD j)) k hk
  rw [hM]
  -- `NTT(zD) = NTT(y) + NTT(c)·NTT(s1)`
  have hzD : ∀ s < l, nttAt (zD s) k = nttAt (y s) k + nttAt c k * nttAt (s1 s) k := by
    intro s hs
    rw [nttAt_congr (b := fun i => y s i + ocamlCenteredProduct (MLDSA.ntt c) (MLDSA.ntt (s1 s)) i)
      (fun i hi => by rw [hz s hs i hi]) k hk, nttAt_add _ _ k hk, nttAt_centeredProduct _ _ k hk]
  -- `NTT(t1·2^13) = NTT(t) − NTT(t0)`
  have hT : nttAt (fun i => t1D i * 2 ^ 13) k =
      (∑ j ∈ Finset.range l, (A r j k : MLDSA.Zq) * nttAt (s1 j) k) + nttAt s2r k - nttAt t0r k := by
    rw [nttAt_congr (b := fun i =>
        MLDSA.addMod (ocamlInverseNtt (ocamlMatVec l A (fun j => MLDSA.ntt (s1 j)) r) i) (s2r i) -
          t0r i) (fun i hi => by
        push_cast
        rw [← MLDSA.cast_emod_q (MLDSA.addMod _ _), ← ht i hi, MLDSA.cast_emod_q]
        push_cast; ring) k hk,
      nttAt_sub _ _ k hk,
      nttAt_congr (b := fun i => ocamlInverseNtt (ocamlMatVec l A (fun j => MLDSA.ntt (s1 j)) r) i +
        s2r i) (fun i _ => by rw [MLDSA.addMod_cast]; push_cast; ring) k hk,
      nttAt_add _ _ k hk, nttAt_matVec _ _ _ _ _ hk]
  -- right side
  rw [nttAt_add _ _ k hk, nttAt_sub _ _ k hk, nttAt_matVec _ _ _ _ _ hk,
    nttAt_centeredProduct _ _ k hk, nttAt_centeredProduct _ _ k hk]
  rw [Finset.sum_congr rfl (fun s hs => by rw [castArr_ntt, hzD s (Finset.mem_range.mp hs)]), hT]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [show (∑ j ∈ Finset.range l, (A r j k : MLDSA.Zq) * (nttAt c k * nttAt (s1 j) k)) =
      nttAt c k * ∑ j ∈ Finset.range l, (A r j k : MLDSA.Zq) * nttAt (s1 j) k by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring]
  ring

end OcamlPq.EndToEnd.MLDSA
