import OcamlPq.EndToEnd.MLDSA.Verify
import OcamlPq.EndToEnd.MLDSA.Consistency
import OcamlPq.EndToEnd.MLDSA.KeyImport

/-!
# ML-DSA end to end: the OCaml models are FIPS 204

This module closes the gap between the four areas that verify
`mldsa/mldsa_engine.ml`: `MLDSAAlg` proves the composition (key generation,
signing loop, sign/verify) against FIPS 204 *parametrically* in bundles of
building blocks (`KeyOps`/`KeyFips`, `SignOps`/`SignFips`,
`VerifyOps`/`VerifyFips`, an abstract `XOF`), under refinement hypotheses
(`*.Refines`) linking the bundles. Here the bundles are instantiated with the
concrete models of the arithmetic (`MLDSA`), encoding (`Encoding`) and hash
(`Hash`) areas, the FIPS bundles with those areas' FIPS 204 transcriptions,
and the refinement hypotheses are discharged from those areas' theorems.

## Files

* `Adapters`: representation adapters (index functions / lists / `ℤ_q`,
  `Fin 256` / `ℕ` / `UInt8`, the `trunc` of 256-entry arrays).
* `Shake`: `ocamlShake128/256` (the Hash area's model of
  `Mldsa_keccak.shake*`, prefix consistency from `shake*_prefix`) and
  `fipsShake128/256` (FIPS 202 `SHAKE128/256`), equal by `shake*_eq`.
* `Arith`: FIPS NTT, NTT⁻¹, `MultiplyNTT`, `MatrixVectorNTT`, `+`, `−` on
  `Poly`, equal to the OCaml models on every input.
* `ParamFacts`: per-parameter-set facts.
* `Pack`: packers and key/signature layouts (range-restricted equalities).
* `KeyGen`, `SignCore`, `Sign`, `Verify`: the bundles, `Refines` proofs,
  bridges, and end-to-end theorems.
* `KeyImport`: `build_signing_key` (key-import consistency checks).
* `Algebra`, `Consistency`: the verifier's `w′_approx ≡ w − c·s2 + c·t0` and
  sign/verify consistency.

## Headline theorems (for every valid parameter set, and instantiated for
ML-DSA-44/65/87 with `λ` from FIPS 204 Table 1 below)

* `keypairFromSeed_e2e`: `keypair_from_seed ξ` = `ML-DSA.KeyGen_internal(ξ)`
  (Algorithm 6); `generate_e2e`: `generate` = `ML-DSA.KeyGen` (Algorithm 1).
* `signMu_e2e`: `sign_mu_with_randomness` = `ML-DSA.Sign_internal`
  (Algorithm 7) within 821 iterations; `sign_e2e`, `signDeterministic_e2e`:
  `sign`, `sign_deterministic` = `ML-DSA.Sign` (Algorithm 2).
* `verify_e2e`: `verify_formatted` = `ML-DSA.Verify_internal` (Algorithm 8),
  `verify` = `ML-DSA.Verify` (Algorithm 3); wrong lengths give `false`.
* `signMu_verifyMu`, `sign_verify`, `signDeterministic_verify`: on a key from
  `keypair_from_seed` (secrets in `[−η, η]`), `verify_mu`/`verify` accept every
  signature `sign_mu_with_randomness`/`sign`/`sign_deterministic` returns
  (FIPS 204 correctness, for the code). The algebraic hypothesis of the
  arithmetic area's `verify_recovers_w1_of_accepted` is `verifier_approx`.
* `buildSigningKey_e2e`: `build_signing_key` accepts an expanded key iff its
  `tr` and `t0` are those Algorithm 6 derives from `(ρ, K, s1, s2)`.

The OCaml side uses the OCaml SHAKE (`ocamlShake*`), the FIPS side FIPS 202
SHAKE (`fipsShake*`, see `fipsShake256_squeeze_bits`).

## Remaining hypotheses (all inherent to the models)

* **Sampler termination.** The OCaml rejection samplers are unbounded
  recursions; the theorems are about the values their calls return
  (`ExpandMatrixReturns`, `ExpandSecretReturns`, `ChallengeReturns`, as in
  `MLDSAAlg`), taken only at the inputs actually used. For signing, where
  one `challenge_polynomial` call is made per iteration, the challenge
  function is required to equal FIPS 204's `SampleInBall`
  (`challengeValue_of_returns` derives this from the "returns" relation, and
  `fun c̃ => sampleInBall τ (H c̃)` satisfies it outright).
* **Signing keys have `s1, s2 ∈ [−η, η]`** (`SecretsInRange`); true for
  generated keys (`keypairFromSeed_secretsInRange`) and for every key
  `decode_expanded_signing_key` returns (`decodeSk_secretsInRange`: `unpack_eta`
  rejects codes above `2η`).

## Statement mismatches found (bridged here; no discrepancy in the OCaml)

* `KeyOps.Refines`, `SignOps.Refines`, `VerifyOps.Refines` do **not hold** for
  the concrete models: the fields `packT1`, `packEta`, `packT0`, `packW1`,
  `candidate_eq`, `encodeSignature`, `useHint` quantify over all inputs, but
  the code and FIPS 204 only agree on the inputs the algorithms produce.
  FIPS 204 leaves `SimpleBitPack`/`BitPack` undefined out of range, and there
  the OCaml packer spills high bits into the next code (a `t1` coefficient
  `2^10`) while the transcription truncates; the signer's shortcuts need
  `‖cs2‖∞ ≤ β` and a mask in `(−γ1, γ1]` (with `ĉ = 0` and a mask coefficient
  `y = q` both accept, the code returning `z = q`, Algorithm 7 `z mod± q = 0`);
  `use_hint` treats a hint `2` as `1`, `UseHint` as `0` (proved:
  `verifyOps_useHint_ne`). Each area's theorem
  holds on the ranges, and the bridge replaces the offending fields by the
  FIPS ones (`keyOpsIdeal`, `signOpsIdeal`, `verifyOpsIdeal`, which satisfy
  `Refines`) and proves the OCaml models unchanged on reachable inputs.
* `MLDSAAlg`'s theorems require the samplers to return on *every* seed
  (`∀ ρ, ExpandMatrixReturns …`, `∀ c̃, ChallengeReturns …`), which cannot be
  proved for SHAKE and would make them vacuous if some input made a sampler
  diverge; they are re-proved here with pointwise/value-form hypotheses
  (`keypairFromSeed_eq_at`, `signMuWithRandomness_eq_at`, `verify_eq_at`, …).
* The FIPS `NTT⁻¹` transcription and the OCaml `inverse_ntt` model disagree
  at the meaningless indices `≥ 256`; both are truncated (`trunc`).
-/

namespace OcamlPq.EndToEnd.MLDSA

open OcamlPq.MLDSAAlg

/-- Generated keys have secrets in `[−η, η]`, so the signing theorems apply
    to them. -/
theorem keypairFromSeed_secretsInRange {P : Params} (hP : P.Valid) (E : KeyOps) (H : XOF)
    (expandMatrix : Bytes → PolyMat) (expandSecret : Bytes → PolyVec × PolyVec) (xi : Bytes)
    (hS : ExpandSecretReturns H P (seedRhoPrime P H xi) (expandSecret (seedRhoPrime P H xi)).1
      (expandSecret (seedRhoPrime P H xi)).2) :
    SecretsInRange P (keypairFromSeed E P H expandMatrix expandSecret xi).expanded := by
  have hf := e2eFacts hP
  have hS' := expandSecret_spec H hP _ _ _ hS
  refine ⟨fun r hr i _ => ?_, fun r hr i _ => ?_⟩
  · show -(P.eta : ℤ) ≤ (expandSecret (seedRhoPrime P H xi)).1 r i ∧
      (expandSecret (seedRhoPrime P H xi)).1 r i ≤ P.eta
    rw [hS'.1 r hr]; exact rejBoundedPoly_range hf.eta _ i
  · show -(P.eta : ℤ) ≤ (expandSecret (seedRhoPrime P H xi)).2 r i ∧
      (expandSecret (seedRhoPrime P H xi)).2 r i ≤ P.eta
    rw [hS'.2 r hr]; exact rejBoundedPoly_range hf.eta _ i

/-- **The end-to-end statement for a parameter set `P`** with FIPS 204
    security strength `lam` (`λ`): the concrete OCaml models (OCaml SHAKE)
    of `keypair_from_seed`, `generate`, `sign_mu_with_randomness`, `sign`,
    `sign_deterministic`, `verify_formatted` and `verify` compute FIPS 204
    Algorithms 6, 1, 7, 2, 2 (`rnd = 0^32`), 8 and 3 with the FIPS building
    blocks and FIPS 202 SHAKE (signing within 821 iterations). -/
def Statement (P : Params) (lam : ℕ) : Prop :=
  -- Algorithm 6, ML-DSA.KeyGen_internal
  (∀ (xi : Bytes) (A : PolyMat) (s1 s2 : PolyVec),
    ExpandMatrixReturns ocamlShake128 P (seedRho P ocamlShake256 xi) A →
    ExpandSecretReturns ocamlShake256 P (seedRhoPrime P ocamlShake256 xi) s1 s2 →
    (keypairFromSeed (keyOps P) P ocamlShake256 (fun _ => A) (fun _ => (s1, s2)) xi).verificationKey =
        (keyGenInternal (keyFips P) P fipsShake256 fipsShake128 xi).1 ∧
      (keypairFromSeed (keyOps P) P ocamlShake256 (fun _ => A) (fun _ => (s1, s2))
        xi).expandedOctets = (keyGenInternal (keyFips P) P fipsShake256 fipsShake128 xi).2) ∧
  -- Algorithm 1, ML-DSA.KeyGen
  (∀ (random : ℕ → Bytes) (A : PolyMat) (s1 s2 : PolyVec),
    ExpandMatrixReturns ocamlShake128 P (seedRho P ocamlShake256 (random 32)) A →
    ExpandSecretReturns ocamlShake256 P (seedRhoPrime P ocamlShake256 (random 32)) s1 s2 →
    (generate (keyOps P) P ocamlShake256 (fun _ => A) (fun _ => (s1, s2)) random).1 = [32] ∧
    ((random 32).length = 32 → ∃ sk pk,
      (generate (keyOps P) P ocamlShake256 (fun _ => A) (fun _ => (s1, s2)) random).2 =
        some (sk, pk) ∧
      pk = (keyGenInternal (keyFips P) P fipsShake256 fipsShake128 (random 32)).1 ∧
      sk.expandedOctets = (keyGenInternal (keyFips P) P fipsShake256 fipsShake128 (random 32)).2 ∧
      signingKeyToSeed sk = some (random 32))) ∧
  -- Algorithm 7, ML-DSA.Sign_internal (from μ)
  (∀ (key : ExpandedKey) (A : PolyMat) (challenge : Bytes → Poly) (mu rnd : Bytes),
    SecretsInRange P key → ExpandMatrixReturns ocamlShake128 P key.rho A →
    (∀ ct, challenge ct = sampleInBall P.tau (ocamlShake256 ct)) →
    mu.length = 64 → rnd.length = 32 →
    (∀ sig, signMuWithRandomness (signOps P key) P ocamlShake256 A challenge key mu rnd = .ok sig ↔
      signInternalMu (signFips P key) P lam fipsShake256 fipsShake128 key.rho key.key mu rnd 821 =
        some sig) ∧
    (∀ e, signMuWithRandomness (signOps P key) P ocamlShake256 A challenge key mu rnd = .error e ↔
      e = .signingFailed ∧
        signInternalMu (signFips P key) P lam fipsShake256 fipsShake128 key.rho key.key mu rnd 821 =
          none)) ∧
  -- Algorithm 2, ML-DSA.Sign
  (∀ (key : ExpandedKey) (A : PolyMat) (challenge : Bytes → Poly) (context message : Bytes)
      (random : ℕ → Bytes),
    SecretsInRange P key → ExpandMatrixReturns ocamlShake128 P key.rho A →
    (∀ ct, challenge ct = sampleInBall P.tau (ocamlShake256 ct)) →
    context.length ≤ 255 → (random 32).length = 32 →
    (sign (signOps P key) P ocamlShake256 A challenge context random key message).1 = [32] ∧
    (∀ sig, (sign (signOps P key) P ocamlShake256 A challenge context random key message).2 =
        some (.ok sig) ↔
      mldsaSign (signFips P key) P lam fipsShake256 fipsShake128 key message context (random 32) =
        some sig) ∧
    (∀ e, (sign (signOps P key) P ocamlShake256 A challenge context random key message).2 =
        some (.error e) ↔
      e = .signingFailed ∧ mldsaSign (signFips P key) P lam fipsShake256 fipsShake128 key message
        context (random 32) = none)) ∧
  -- Algorithm 2 with rnd = {0}^32 (deterministic variant)
  (∀ (key : ExpandedKey) (A : PolyMat) (challenge : Bytes → Poly) (context message : Bytes),
    SecretsInRange P key → ExpandMatrixReturns ocamlShake128 P key.rho A →
    (∀ ct, challenge ct = sampleInBall P.tau (ocamlShake256 ct)) → context.length ≤ 255 →
    (∀ sig, signDeterministic (signOps P key) P ocamlShake256 A challenge context key message =
        .ok sig ↔
      mldsaSign (signFips P key) P lam fipsShake256 fipsShake128 key message context
        (List.replicate 32 0) = some sig) ∧
    (∀ e, signDeterministic (signOps P key) P ocamlShake256 A challenge context key message =
        .error e ↔
      e = .signingFailed ∧ mldsaSign (signFips P key) P lam fipsShake256 fipsShake128 key message
        context (List.replicate 32 0) = none)) ∧
  -- Algorithms 8 and 3, ML-DSA.Verify_internal and ML-DSA.Verify
  (∀ (pk sig context message : Bytes) (A : PolyMat) (c : Poly),
    pk.length = P.verificationKeySize → sig.length = P.signatureSize →
    ExpandMatrixReturns ocamlShake128 P (pk.take 32) A →
    ChallengeReturns P.tau ocamlShake256 (sig.take P.cTildeBytes) 136 c →
    (∀ M', verifyFormatted (verifyOps P) P ocamlShake256 (fun _ => A) (fun _ => c) pk M' sig =
      verifyInternal (verifyFips P) P lam fipsShake256 fipsShake128 pk M' sig) ∧
    verify (verifyOps P) P ocamlShake256 (fun _ => A) (fun _ => c) context pk message sig =
      mldsaVerify (verifyFips P) P lam fipsShake256 fipsShake128 pk message sig context)

/-- **End to end for every valid parameter set.** -/
theorem endToEnd {P : Params} (hP : P.Valid) {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam) :
    Statement P lam :=
  ⟨fun xi A s1 s2 hA hS => keypairFromSeed_e2e hP xi A s1 s2 hA hS,
   fun random A s1 s2 hA hS => generate_e2e hP random A s1 s2 hA hS,
   fun key A challenge mu rnd hkey hA hc hmu hrnd =>
     (signMu_e2e hP hlam key hkey A hA challenge hc mu rnd).2.2 hmu hrnd,
   fun key A challenge context message random hkey hA hc hctx hr =>
     ⟨(sign_e2e hP hlam key hkey A hA challenge hc context message random).2.1 hctx,
      (sign_e2e hP hlam key hkey A hA challenge hc context message random).2.2 hctx hr⟩,
   fun key A challenge context message hkey hA hc hctx =>
     (signDeterministic_e2e hP hlam key hkey A hA challenge hc context message).2 hctx,
   fun pk sig context message A c hpk hsig hA hc =>
     (verify_e2e hP hlam pk sig context message A c).2 hpk hsig hA hc⟩

/-- **ML-DSA-44 end to end** (`λ = 128`, FIPS 204 Table 1). -/
theorem mldsa44_endToEnd : Statement mldsa44 fips44.lambda :=
  endToEnd (Or.inl rfl) mldsa44_implements.2.2.2.1

/-- **ML-DSA-65 end to end** (`λ = 192`, FIPS 204 Table 1). -/
theorem mldsa65_endToEnd : Statement mldsa65 fips65.lambda :=
  endToEnd (Or.inr (Or.inl rfl)) mldsa65_implements.2.2.2.1

/-- **ML-DSA-87 end to end** (`λ = 256`, FIPS 204 Table 1). -/
theorem mldsa87_endToEnd : Statement mldsa87 fips87.lambda :=
  endToEnd (Or.inr (Or.inr rfl)) mldsa87_implements.2.2.2.1

end OcamlPq.EndToEnd.MLDSA
