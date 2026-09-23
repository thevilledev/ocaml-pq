import OcamlPq.EndToEnd.MLDSA.Sign

/-!
# Key import end to end

`MLDSAAlg.buildSigningKey_ok_iff` (the consistency checks of
`build_signing_key`) instantiated with the concrete OCaml bundle: for an
expanded key whose secrets are in `[−η, η]` and whose `t0` is in
`(−2^12, 2^12]` (both guaranteed by `decode_expanded_signing_key`:
`decodeSk_secretsInRange`, the Encoding area's `unpackT0_range`),
`build_signing_key` accepts exactly the keys whose `tr` and `t0` are the ones
FIPS 204 Algorithm 6 derives from `(ρ, K, s1, s2)`.
-/

namespace OcamlPq.EndToEnd.MLDSA

open OcamlPq.MLDSAAlg

/-- On keys with secrets and `t0` in range, `build_signing_key` with the OCaml
    bundle equals it with the ideal bundle. -/
theorem buildSigningKey_ideal {P : Params} (hP : P.Valid) (H : XOF) (w : ℕ) (matrix : PolyMat)
    (seed : Option Bytes) (e : ExpandedKey) (hkey : SecretsInRange P e)
    (ht0 : ∀ r < P.k, ∀ i < 256, -(2 ^ 12 : ℤ) < e.t0 r i ∧ e.t0 r i ≤ 2 ^ 12) :
    buildSigningKey (keyOps P) P H w matrix seed e =
      buildSigningKey (keyOpsIdeal P) P H w matrix seed e := by
  have hcpp : ∀ m e, computePublicParts (keyOpsIdeal P) m e = computePublicParts (keyOps P) m e :=
    fun m e => by unfold computePublicParts; rfl
  have hr := computePublicParts_range (keyOps P) rfl
  unfold buildSigningKey
  simp only [hcpp]
  rw [← encodeVerificationKey_ideal hP _ _ (fun r _ i _ => (hr _ _ r i).1),
    ← encodeExpandedSigningKey_ideal hP e hkey.1 hkey.2 ht0]

/-- **`build_signing_key`, end to end.** For a valid parameter set, an
    expanded key `e` with secrets in `[−η, η]` and `t0 ∈ (−2^12, 2^12]`, the
    matrix `A` returned by `expand_matrix e.rho`, and an `int` of at least 31
    bits: the OCaml `build_signing_key` (OCaml SHAKE) accepts `e` iff `e.tr`
    and `e.t0` (rows `< k`, coefficients `< 256`) are those of FIPS 204
    Algorithm 6 on `(ρ, K, s1, s2)` (FIPS 202 SHAKE). -/
theorem buildSigningKey_e2e {P : Params} (hP : P.Valid) {w : ℕ} (hw : 31 ≤ w) (A : PolyMat)
    (seed : Option Bytes) (e : ExpandedKey) (hkey : SecretsInRange P e)
    (ht0 : ∀ r < P.k, ∀ i < 256, -(2 ^ 12 : ℤ) < e.t0 r i ∧ e.t0 r i ≤ 2 ^ 12)
    (hA : ExpandMatrixReturns ocamlShake128 P e.rho A) :
    (∃ key, buildSigningKey (keyOps P) P ocamlShake256 w A seed e = .ok key) ↔
      (e.tr = (deriveExpanded (keyFips P) P fipsShake256 fipsShake128 e.rho e.key e.s1 e.s2).tr ∧
        ∀ r < P.k, ∀ i < n, e.t0 r i =
          (deriveExpanded (keyFips P) P fipsShake256 fipsShake128 e.rho e.key e.s1 e.s2).t0 r i) := by
  rw [buildSigningKey_ideal hP _ w A seed e hkey ht0, fipsShake128_eq, fipsShake256_eq]
  refine buildSigningKey_ok_iff _ _ (keyOpsIdeal_refines P) _ _ hw A seed e hA hP ?_
  intro r hr i hi
  refine ⟨Portable.of_bounds (lo := -(2 ^ 12)) (hi := 2 ^ 12 + 1) (by norm_num) (by norm_num)
    (by have := ht0 r hr i hi; omega) (by have := ht0 r hr i hi; omega), ?_⟩
  have := MLDSA.power2round_range
    ((keyFips P).addPoly ((keyFips P).NTTinv ((keyFips P).mulMatVec (expandA ocamlShake128 e.rho)
      (fun i => (keyFips P).NTT (e.s1 i)) r)) (e.s2 r) i)
  unfold publicParts
  simp only [keyFips] at this ⊢
  rw [← MLDSA.power2round_eq_spec]
  exact Portable.of_bounds (lo := -(2 ^ 12)) (hi := 2 ^ 12 + 1) (by norm_num) (by norm_num)
    (by omega) (by omega)

end OcamlPq.EndToEnd.MLDSA
