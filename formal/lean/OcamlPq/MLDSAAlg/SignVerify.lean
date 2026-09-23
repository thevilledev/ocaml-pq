import OcamlPq.MLDSAAlg.KeyGen

/-!
# Signing and verification: composition and external interface

Models of `formatted_prefix`, `sign_mu_with_randomness`,
`sign_formatted_with_randomness`, `sign_with_randomness`, `sign`,
`sign_deterministic`, `verify_mu`, `verify_formatted` and `verify`
(`mldsa_engine.ml`, lines 708–908), against FIPS 204 Algorithms 2, 3, 7
and 8.

As in `KeyGen`, the arithmetic, the rejection conditions of the signer
(`z`, `r0`, `ct0`, hint count: lines 747–797) and the encodings are black
boxes linked to FIPS by explicit hypotheses (`SignOps.Refines`,
`VerifyOps.Refines`). What is verified here: the length checks,
`ρ″ = H(K ‖ rnd ‖ μ, 64)` (argument order), `μ = H(tr ‖ M′, 64)`,
`c̃ = H(μ ‖ w1Encode(w1), λ/4)`, the challenge drawn from the full `c̃`
(via `challengePolynomial_returns_iff`), the mask nonces (via `SignLoop`),
`M′ = IntegerToBytes(0, 1) ‖ IntegerToBytes(|ctx|, 1) ‖ ctx ‖ M`, the
context-length checks (`sign` rejects before calling the randomness
source), the deterministic variant's `rnd = 0^32`, and the structure of
verification.
-/

namespace OcamlPq.MLDSAAlg

/-! ## Signing -/

/-- OCaml building blocks of `sign_mu_with_randomness`. `candidate y w0 w1 ĉ`
    is lines 747–797 (with the key's precomputed `s1_ntt`, `s2_ntt`, `t0_ntt`
    fixed): `some (z, hints)` if the candidate is accepted, `none` if
    `!rejection <> 0`. -/
structure SignOps where
  ntt : Poly → Poly
  inverseNtt : Poly → Poly
  matrixVectorNtt : PolyMat → PolyVec → PolyVec
  decompose : ℤ → ℤ × ℤ
  packW1 : Poly → Bytes
  candidate : PolyVec → PolyVec → PolyVec → Poly → Option (PolyVec × PolyVec)
  encodeSignature : Bytes → PolyVec → PolyVec → Bytes
  unpackZ : Bytes → Poly

/-- FIPS 204 building blocks of Algorithm 7. `finish y w ĉ` is lines 15–30
    of Algorithm 7 (`⟨⟨cs1⟩⟩`, `⟨⟨cs2⟩⟩`, `z`, `r0`, the norm checks,
    `⟨⟨ct0⟩⟩`, `MakeHint`, the hint count) for the fixed key: `some (z, h)` or
    `none` for `⊥`. -/
structure SignFips where
  NTT : Poly → Poly
  NTTinv : Poly → Poly
  mulMatVec : PolyMat → PolyVec → PolyVec
  highBits : ℤ → ℤ
  simpleBitPack : Poly → ℕ → Bytes
  finish : PolyVec → PolyVec → Poly → Option (PolyVec × PolyVec)
  sigEncode : Bytes → PolyVec → PolyVec → Bytes
  bitUnpack : Bytes → ℕ → ℕ → Poly

/-- Hypotheses (from the arithmetic and encoding modules) linking the OCaml
    signer's building blocks to FIPS 204. `candidate_eq` is the equivalence
    of the implementation's rejection shortcuts (`r0` computed as
    `w0 − cs2`, the hint from `r0 + ct0`) with Algorithm 7 lines 15–30. -/
structure SignOps.Refines (E : SignOps) (F : SignFips) (P : Params) : Prop where
  ntt : E.ntt = F.NTT
  inverseNtt : E.inverseNtt = F.NTTinv
  matrixVectorNtt : E.matrixVectorNtt = F.mulMatVec
  highBits : ∀ x, (E.decompose x).1 = F.highBits x
  packW1 : ∀ p, E.packW1 p = F.simpleBitPack p ((q - 1) / (2 * P.gamma2) - 1)
  candidate_eq : ∀ (y : PolyVec) (w : PolyVec) (cHat : Poly),
    E.candidate y (fun r i => (E.decompose (w r i)).2) (fun r i => (E.decompose (w r i)).1) cHat =
      F.finish y w cHat
  encodeSignature : E.encodeSignature = F.sigEncode
  unpackZ : ∀ v : Bytes, v.length = 32 * (1 + bitlen (P.gamma1 - 1)) →
    E.unpackZ v = F.bitUnpack v (P.gamma1 - 1) P.gamma1
  mulMatVec_local : ∀ (A A' : PolyMat) (v v' : PolyVec),
    (∀ r < P.k, ∀ s < P.l, A r s = A' r s) → (∀ s < P.l, v s = v' s) →
    ∀ r < P.k, F.mulMatVec A v r = F.mulMatVec A' v' r
  finish_local : ∀ (y y' w w' : PolyVec) (cHat : Poly), (∀ s < P.l, y s = y' s) →
    (∀ r < P.k, w r = w' r) → F.finish y w cHat = F.finish y' w' cHat

/-- One iteration of `attempt` after `y` is computed (`mldsa_engine.ml`,
    lines 733–800): `matrix` is `expand_matrix expanded.rho` and
    `challenge c̃` the value of `challenge_polynomial c̃ 136`. -/
def signIter (E : SignOps) (P : Params) (H : XOF) (matrix : PolyMat) (challenge : Bytes → Poly)
    (mu : Bytes) (y : PolyVec) : Option Bytes :=
  let wNtt := E.matrixVectorNtt matrix (fun i => E.ntt (y i))
  let w := fun row => E.inverseNtt (wNtt row)
  let w1 := fun row index => (E.decompose (w row index)).1
  let w0 := fun row index => (E.decompose (w row index)).2
  let encodedW1 := concatMap P.k E.packW1 w1
  let cTilde := H.squeeze (mu ++ encodedW1) P.cTildeBytes
  let challengeNtt := E.ntt (challenge cTilde)
  match E.candidate y w0 w1 challengeNtt with
  | some zh => some (E.encodeSignature cTilde zh.1 zh.2)
  | none => none

/-- `sign_mu_with_randomness key ~mu randomness` (`mldsa_engine.ml`,
    lines 713–802). -/
def signMuWithRandomness (E : SignOps) (P : Params) (H : XOF) (matrix : PolyMat)
    (challenge : Bytes → Poly) (key : ExpandedKey) (mu randomness : Bytes) :
    Except MLDSAError Bytes :=
  if mu.length ≠ 64 then .error (.invalidLength "ML-DSA message representative" 64 mu.length)
  else if randomness.length ≠ 32 then
    .error (.invalidLength "ML-DSA signing randomness" 32 randomness.length)
  else
    let rhoPrime := H.squeeze (key.key ++ randomness ++ mu) 64
    attempt P.l (maskPolynomial H P E.unpackZ rhoPrime) (signIter E P H matrix challenge mu) 0

/-- FIPS 204 Algorithm 28, `w1Encode(w1)`. -/
def w1Encode (F : SignFips) (P : Params) (w1 : PolyVec) : Bytes :=
  (List.range P.k).foldl
    (fun acc i => acc ++ F.simpleBitPack (w1 i) ((q - 1) / (2 * P.gamma2) - 1)) []

/-- FIPS 204 Algorithm 7, lines 11–30 and 33 (one iteration of the loop,
    returning the encoded signature if `(z, h) ≠ ⊥`). `lam` is `λ`. -/
noncomputable def alg7Step (F : SignFips) (P : Params) (lam : ℕ) (H : XOF) (A : PolyMat)
    (mu : Bytes) (y : PolyVec) : Option Bytes :=
  let w := fun r => F.NTTinv (F.mulMatVec A (fun i => F.NTT (y i)) r)
  let w1 := fun r i => F.highBits (w r i)
  let cTilde := H.squeeze (mu ++ w1Encode F P w1) (lam / 4)
  let c := sampleInBall P.tau (H cTilde)
  let cHat := F.NTT c
  match F.finish y w cHat with
  | some zh => some (F.sigEncode cTilde zh.1 zh.2)
  | none => none

/-- FIPS 204 Algorithm 7 (`ML-DSA.Sign_internal`) from line 6 on, given the
    decoded key's `ρ`, `K` and `μ`, with the `while` loop bounded by `fuel`
    iterations (`none`: not finished). -/
noncomputable def signInternalMu (F : SignFips) (P : Params) (lam : ℕ) (H G : XOF)
    (rho K mu rnd : Bytes) (fuel : ℕ) : Option Bytes :=
  let A := expandA G rho
  let rhoPP := H.squeeze (K ++ rnd ++ mu) 64
  alg7Loop P.l (fun kappa r => expandMask H P F.bitUnpack rhoPP kappa r)
    (alg7Step F P lam H A mu) fuel 0

theorem concatMap_eq_foldl (len : ℕ) (f : Poly → Bytes) (v : PolyVec) :
    concatMap len f v = (List.range len).foldl (fun acc i => acc ++ f (v i)) [] := by
  rw [foldl_append_eq]; rfl

/-- One iteration of the OCaml loop equals one iteration of Algorithm 7,
    for mask vectors that agree on the rows `< ℓ`. -/
theorem signIter_eq (E : SignOps) (F : SignFips) {P : Params} (hP : P.Valid) (hR : E.Refines F P)
    {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam) (H G : XOF) (rho : Bytes) (matrix : PolyMat)
    (hA : ExpandMatrixReturns G P rho matrix) (challenge : Bytes → Poly)
    (hc : ∀ ct, ChallengeReturns P.tau H ct 136 (challenge ct)) (mu : Bytes) (y y' : PolyVec)
    (hy : ∀ r < P.l, y r = y' r) :
    signIter E P H matrix challenge mu y = alg7Step F P lam H (expandA G rho) mu y' := by
  obtain ⟨-, -, -, -, htau, -⟩ := hP.facts
  have hA' := (expandMatrix_spec G hP rho).1 matrix hA
  have hlam4 : lam / 4 = P.cTildeBytes := by omega
  have hWW : ∀ r < P.k, F.NTTinv (F.mulMatVec matrix (fun i => F.NTT (y i)) r) =
      F.NTTinv (F.mulMatVec (expandA G rho) (fun i => F.NTT (y' i)) r) := by
    intro r hr
    rw [hR.mulMatVec_local matrix (expandA G rho) _ _ hA' (fun s hs => by rw [hy s hs]) r hr]
  have henc : concatMap P.k E.packW1
        (fun row index => (E.decompose (F.NTTinv (F.mulMatVec matrix (fun i => F.NTT (y i)) row)
          index)).1) =
      w1Encode F P (fun r i => F.highBits
        (F.NTTinv (F.mulMatVec (expandA G rho) (fun i => F.NTT (y' i)) r) i)) := by
    rw [concatMap_eq_foldl, w1Encode]
    apply List.foldl_ext
    intro acc i hi
    rw [hR.packW1]
    congr 2
    funext idx
    rw [hR.highBits, hWW i (List.mem_range.mp hi)]
  unfold signIter alg7Step
  simp only [hR.ntt, hR.inverseNtt, hR.matrixVectorNtt]
  rw [henc, hlam4, ← challenge_returns_eq (by omega) (hc _), hR.candidate_eq,
    hR.finish_local y y' _ _ _ hy hWW, hR.encodeSignature]


/-- **Obligation 7 (`sign_mu_with_randomness`).** Given the refinement
    hypotheses, `λ = 4·c_tilde_bytes`, `matrix` returned by `expand_matrix ρ`
    and `challenge` by `challenge_polynomial · 136`:
    * `μ` must have 64 bytes and `rnd` 32 bytes, else `Invalid_length`;
    * otherwise the OCaml result is `Ok σ` iff FIPS 204 Algorithm 7 (with
      `ρ″ = H(K ‖ rnd ‖ μ, 64)`) returns `σ` within 821 iterations, and
      `Error Signing_failed` iff it does not finish within 821 iterations. -/
theorem signMuWithRandomness_eq (E : SignOps) (F : SignFips) {P : Params} (hP : P.Valid)
    (hR : E.Refines F P) {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam) (H G : XOF)
    (key : ExpandedKey) (matrix : PolyMat) (hA : ExpandMatrixReturns G P key.rho matrix)
    (challenge : Bytes → Poly) (hc : ∀ ct, ChallengeReturns P.tau H ct 136 (challenge ct))
    (mu rnd : Bytes) :
    (mu.length ≠ 64 → signMuWithRandomness E P H matrix challenge key mu rnd =
      .error (.invalidLength "ML-DSA message representative" 64 mu.length)) ∧
    (mu.length = 64 → rnd.length ≠ 32 → signMuWithRandomness E P H matrix challenge key mu rnd =
      .error (.invalidLength "ML-DSA signing randomness" 32 rnd.length)) ∧
    (mu.length = 64 → rnd.length = 32 →
      (∀ sig, signMuWithRandomness E P H matrix challenge key mu rnd = .ok sig ↔
        signInternalMu F P lam H G key.rho key.key mu rnd 821 = some sig) ∧
      (∀ e, signMuWithRandomness E P H matrix challenge key mu rnd = .error e ↔
        e = .signingFailed ∧ signInternalMu F P lam H G key.rho key.key mu rnd 821 = none)) := by
  refine ⟨fun h => by simp [signMuWithRandomness, h], fun h1 h2 => by
    simp [signMuWithRandomness, h1, h2], fun h1 h2 => ?_⟩
  have hsig : signMuWithRandomness E P H matrix challenge key mu rnd =
      attempt P.l (maskPolynomial H P E.unpackZ (H.squeeze (key.key ++ rnd ++ mu) 64))
        (signIter E P H matrix challenge mu) 0 := by
    simp [signMuWithRandomness, h1, h2]
  have := attempt_eq_alg7 P.l (maskPolynomial H P E.unpackZ (H.squeeze (key.key ++ rnd ++ mu) 64))
    (signIter E P H matrix challenge mu)
    (fun kappa r => expandMask H P F.bitUnpack (H.squeeze (key.key ++ rnd ++ mu) 64) kappa r)
    (alg7Step F P lam H (expandA G key.rho) mu)
    (fun kappa r _ => maskPolynomial_eq H hP E.unpackZ F.bitUnpack hR.unpackZ _ kappa r)
    (fun y y' hy => signIter_eq E F hP hR hlam H G key.rho matrix hA challenge hc mu y y' hy)
  obtain ⟨hok1, hok2, herr⟩ := this
  rw [hsig]
  refine ⟨fun sig => ⟨fun h => hok2 sig h, fun h => hok1 821 le_rfl sig h⟩, fun e => herr e⟩

/-- `sign_formatted_with_randomness key ~formatted_message randomness`
    (lines 804–809): `μ = H(tr ‖ M′, 64)`. -/
def signFormattedWithRandomness (E : SignOps) (P : Params) (H : XOF) (matrix : PolyMat)
    (challenge : Bytes → Poly) (key : ExpandedKey) (formattedMessage randomness : Bytes) :
    Except MLDSAError Bytes :=
  let mu := H.squeeze (key.tr ++ formattedMessage) 64
  signMuWithRandomness E P H matrix challenge key mu randomness

/-- `formatted_prefix context` (lines 708–711). -/
def formattedPrefix (context : Bytes) : Bytes :=
  byteString 0 ++ byteString context.length ++ context

/-- `sign_with_randomness ?context key ~message randomness` (lines 811–816). -/
def signWithRandomness (E : SignOps) (P : Params) (H : XOF) (matrix : PolyMat)
    (challenge : Bytes → Poly) (context : Bytes) (key : ExpandedKey) (message randomness : Bytes) :
    Except MLDSAError Bytes :=
  if context.length > 255 then .error (.contextTooLong context.length)
  else signFormattedWithRandomness E P H matrix challenge key
    (formattedPrefix context ++ message) randomness

/-- `sign ?context ~random key ~message` (lines 839–843) together with
    `require_random` (lines 824–831). The first component lists the
    lengths requested from the `random` callback, in order; the second is
    `none` if `require_random` raises `Invalid_argument`. -/
def sign (E : SignOps) (P : Params) (H : XOF) (matrix : PolyMat) (challenge : Bytes → Poly)
    (context : Bytes) (random : ℕ → Bytes) (key : ExpandedKey) (message : Bytes) :
    List ℕ × Option (Except MLDSAError Bytes) :=
  if context.length > 255 then ([], some (.error (.contextTooLong context.length)))
  else
    let value := random 32
    if value.length ≠ 32 then ([32], none)
    else ([32], some (signWithRandomness E P H matrix challenge context key message value))

/-- `sign_deterministic ?context key ~message` (lines 845–846). -/
def signDeterministic (E : SignOps) (P : Params) (H : XOF) (matrix : PolyMat)
    (challenge : Bytes → Poly) (context : Bytes) (key : ExpandedKey) (message : Bytes) :
    Except MLDSAError Bytes :=
  signWithRandomness E P H matrix challenge context key message (List.replicate 32 0)

/-- FIPS 204 Algorithm 2, `ML-DSA.Sign(sk, M, ctx)` (and its deterministic
    variant, `rnd = {0}^32`), with the key already decoded, randomness `rnd`
    and Algorithm 7 bounded by 821 iterations; `none` is `⊥`. -/
noncomputable def mldsaSign (F : SignFips) (P : Params) (lam : ℕ) (H G : XOF) (key : ExpandedKey)
    (M ctx rnd : Bytes) : Option Bytes :=
  if ctx.length > 255 then none
  else
    let M' := integerToBytes 0 1 ++ integerToBytes ctx.length 1 ++ ctx ++ M
    let mu := H.squeeze (key.tr ++ M') 64
    signInternalMu F P lam H G key.rho key.key mu rnd 821

/-- `formatted_prefix` is `IntegerToBytes(0, 1) ‖ IntegerToBytes(|ctx|, 1) ‖
    ctx` for `|ctx| ≤ 255`. -/
theorem formattedPrefix_eq {context : Bytes} (h : context.length ≤ 255) :
    formattedPrefix context = integerToBytes 0 1 ++ integerToBytes context.length 1 ++ context := by
  unfold formattedPrefix
  rw [byteString_eq (by norm_num), byteString_eq (by omega)]

/-- **Obligation 7 (external signing, FIPS 204 Algorithm 2).** For a
    context of more than 255 bytes, `sign` returns `Context_too_long`
    without calling the randomness source. Otherwise it requests exactly 32
    bytes; if the callback returns 32 bytes `rnd`, the result is `Ok σ` iff
    Algorithm 2 with that `rnd` returns `σ` (within the 821-iteration bound)
    and otherwise `Signing_failed`. -/
theorem mldsaSign_eq (E : SignOps) (F : SignFips) {P : Params} (hP : P.Valid)
    (hR : E.Refines F P) {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam) (H G : XOF)
    (key : ExpandedKey) (matrix : PolyMat) (hA : ExpandMatrixReturns G P key.rho matrix)
    (challenge : Bytes → Poly) (hc : ∀ ct, ChallengeReturns P.tau H ct 136 (challenge ct))
    (context message : Bytes) (random : ℕ → Bytes) :
    (context.length > 255 → sign E P H matrix challenge context random key message =
      ([], some (.error (.contextTooLong context.length)))) ∧
    (context.length ≤ 255 → (sign E P H matrix challenge context random key message).1 = [32]) ∧
    (context.length ≤ 255 → (random 32).length = 32 →
      (∀ sig, (sign E P H matrix challenge context random key message).2 = some (.ok sig) ↔
        mldsaSign F P lam H G key message context (random 32) = some sig) ∧
      (∀ e, (sign E P H matrix challenge context random key message).2 = some (.error e) ↔
        e = .signingFailed ∧ mldsaSign F P lam H G key message context (random 32) = none)) := by
  refine ⟨fun h => by simp [sign, h], fun h => ?_, fun h hr => ?_⟩
  · unfold sign; rw [ite_eq_right (by omega)]; dsimp only; split_ifs <;> rfl
  · have hmu : (H.squeeze (key.tr ++ (formattedPrefix context ++ message)) 64).length = 64 := by simp
    have := (signMuWithRandomness_eq E F hP hR hlam H G key matrix hA challenge hc
      (H.squeeze (key.tr ++ (formattedPrefix context ++ message)) 64) (random 32)).2.2 hmu hr
    have e1 : (sign E P H matrix challenge context random key message).2 =
        some (signMuWithRandomness E P H matrix challenge key
          (H.squeeze (key.tr ++ (formattedPrefix context ++ message)) 64) (random 32)) := by
      simp [sign, signWithRandomness, signFormattedWithRandomness, hr, show ¬ context.length > 255 by omega]
    have e2 : mldsaSign F P lam H G key message context (random 32) =
        signInternalMu F P lam H G key.rho key.key
          (H.squeeze (key.tr ++ (formattedPrefix context ++ message)) 64) (random 32) 821 := by
      simp [mldsaSign, show ¬ context.length > 255 by omega, formattedPrefix_eq h]
    rw [e1, e2]
    refine ⟨fun sig => ?_, fun e => ?_⟩
    · rw [Option.some.injEq]; exact this.1 sig
    · rw [Option.some.injEq]; exact this.2 e

/-- **Obligation 7 (deterministic signing).** `sign_deterministic` is
    Algorithm 2 with `rnd = {0}^32`. -/
theorem signDeterministic_eq (E : SignOps) (F : SignFips) {P : Params} (hP : P.Valid)
    (hR : E.Refines F P) {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam) (H G : XOF)
    (key : ExpandedKey) (matrix : PolyMat) (hA : ExpandMatrixReturns G P key.rho matrix)
    (challenge : Bytes → Poly) (hc : ∀ ct, ChallengeReturns P.tau H ct 136 (challenge ct))
    (context message : Bytes) :
    (context.length > 255 → signDeterministic E P H matrix challenge context key message =
      .error (.contextTooLong context.length)) ∧
    (context.length ≤ 255 →
      (∀ sig, signDeterministic E P H matrix challenge context key message = .ok sig ↔
        mldsaSign F P lam H G key message context (List.replicate 32 0) = some sig) ∧
      (∀ e, signDeterministic E P H matrix challenge context key message = .error e ↔
        e = .signingFailed ∧ mldsaSign F P lam H G key message context (List.replicate 32 0) = none)) := by
  refine ⟨fun h => by simp [signDeterministic, signWithRandomness, h], fun h => ?_⟩
  have hmu : (H.squeeze (key.tr ++ (formattedPrefix context ++ message)) 64).length = 64 := by simp
  have := (signMuWithRandomness_eq E F hP hR hlam H G key matrix hA challenge hc
    (H.squeeze (key.tr ++ (formattedPrefix context ++ message)) 64) (List.replicate 32 0)).2.2 hmu
    (by simp)
  have e1 : signDeterministic E P H matrix challenge context key message =
      signMuWithRandomness E P H matrix challenge key
        (H.squeeze (key.tr ++ (formattedPrefix context ++ message)) 64) (List.replicate 32 0) := by
    simp [signDeterministic, signWithRandomness, signFormattedWithRandomness,
      show ¬ context.length > 255 by omega]
  have e2 : mldsaSign F P lam H G key message context (List.replicate 32 0) =
      signInternalMu F P lam H G key.rho key.key
        (H.squeeze (key.tr ++ (formattedPrefix context ++ message)) 64) (List.replicate 32 0) 821 := by
    simp [mldsaSign, show ¬ context.length > 255 by omega, formattedPrefix_eq h]
  rw [e1, e2]
  exact this

/-! ## Verification -/

/-- OCaml building blocks of `verify_mu`. -/
structure VerifyOps where
  decodeVerificationKey : Bytes → Option (Bytes × PolyVec)
  decodeSignature : Bytes → Option (Bytes × PolyVec × PolyVec)
  /-- `vector_norm_violation_flag z (P.gamma1 - beta) <> 0`. -/
  normViolation : PolyVec → Bool
  ntt : Poly → Poly
  inverseNtt : Poly → Poly
  matrixVectorNtt : PolyMat → PolyVec → PolyVec
  /-- `pointwise` (used by `poly_product_ntt`). -/
  pointwise : Poly → Poly → Poly
  subMod : ℤ → ℤ → ℤ
  /-- `use_hint value hint`. -/
  useHint : ℤ → ℤ → ℤ
  packW1 : Poly → Bytes

/-- FIPS 204 building blocks of Algorithm 8. -/
structure VerifyFips where
  pkDecode : Bytes → Bytes × PolyVec
  /-- `sigDecode`, with `none` when the hint decodes to `⊥`. -/
  sigDecode : Bytes → Option (Bytes × PolyVec × PolyVec)
  /-- `‖z‖∞ < γ1 − β`. -/
  zNormOk : PolyVec → Bool
  NTT : Poly → Poly
  NTTinv : Poly → Poly
  mulMatVec : PolyMat → PolyVec → PolyVec
  /-- `∘` on NTT representations. -/
  mulNTT : Poly → Poly → Poly
  subPoly : Poly → Poly → Poly
  /-- `UseHint(h, r)` (Algorithm 40). -/
  useHint : ℤ → ℤ → ℤ
  simpleBitPack : Poly → ℕ → Bytes

/-- Hypotheses linking the verifier's building blocks to FIPS 204. Decoding
    succeeds exactly on inputs of the right length (and, for signatures,
    canonical hints). -/
structure VerifyOps.Refines (E : VerifyOps) (F : VerifyFips) (P : Params) : Prop where
  decodeVerificationKey : ∀ pk, E.decodeVerificationKey pk =
    if pk.length = P.verificationKeySize then some (F.pkDecode pk) else none
  decodeSignature : ∀ sig, E.decodeSignature sig =
    if sig.length = P.signatureSize then F.sigDecode sig else none
  normViolation : ∀ z, E.normViolation z = !F.zNormOk z
  ntt : E.ntt = F.NTT
  inverseNtt : E.inverseNtt = F.NTTinv
  matrixVectorNtt : E.matrixVectorNtt = F.mulMatVec
  pointwise : E.pointwise = F.mulNTT
  subMod : ∀ a b : Poly, (fun i => E.subMod (a i) (b i)) = F.subPoly a b
  useHint : ∀ r h, E.useHint r h = F.useHint h r
  packW1 : ∀ p, E.packW1 p = F.simpleBitPack p ((q - 1) / (2 * P.gamma2) - 1)
  mulMatVec_local : ∀ (A A' : PolyMat) (v : PolyVec),
    (∀ r < P.k, ∀ s < P.l, A r s = A' r s) → ∀ r < P.k, F.mulMatVec A v r = F.mulMatVec A' v r

/-- `verify_mu verification_key ~mu signature` (lines 848–891).
    `expandMatrix ρ` and `challenge c̃` are the values of `expand_matrix ρ`
    and `challenge_polynomial c̃ 136`; `value lsl d` on `t1 ∈ [0, 1023]` is
    `value · 2^d`. -/
def verifyMu (E : VerifyOps) (P : Params) (H : XOF) (expandMatrix : Bytes → PolyMat)
    (challenge : Bytes → Poly) (verificationKey mu signature : Bytes) : Bool :=
  if mu.length ≠ 64 then false
  else
    match E.decodeVerificationKey verificationKey, E.decodeSignature signature with
    | some (rho, t1), some (cTilde, z, hint) =>
      if E.normViolation z then false
      else
        let matrix := expandMatrix rho
        let az := E.matrixVectorNtt matrix (fun i => E.ntt (z i))
        let challengeNtt := E.ntt (challenge cTilde)
        let shiftedT1 : PolyVec := fun row index => t1 row index * 2 ^ d
        let ct1 : PolyVec := fun row => E.pointwise challengeNtt (E.ntt (shiftedT1 row))
        let wApprox : PolyVec := fun row =>
          E.inverseNtt (fun index => E.subMod (az row index) (ct1 row index))
        let reconstructedW1 : PolyVec := fun row index =>
          E.useHint (wApprox row index) (hint row index)
        let encodedW1 := concatMap P.k E.packW1 reconstructedW1
        let expected := H.squeeze (mu ++ encodedW1) P.cTildeBytes
        equalString cTilde expected
    | _, _ => false

/-- `verify_formatted verification_key ~formatted_message signature`
    (lines 893–901). -/
def verifyFormatted (E : VerifyOps) (P : Params) (H : XOF) (expandMatrix : Bytes → PolyMat)
    (challenge : Bytes → Poly) (verificationKey formattedMessage signature : Bytes) : Bool :=
  let tr := H.squeeze verificationKey 64
  let mu := H.squeeze (tr ++ formattedMessage) 64
  verifyMu E P H expandMatrix challenge verificationKey mu signature

/-- `verify ?context verification_key ~message signature` (lines 903–908). -/
def verify (E : VerifyOps) (P : Params) (H : XOF) (expandMatrix : Bytes → PolyMat)
    (challenge : Bytes → Poly) (context verificationKey message signature : Bytes) : Bool :=
  if context.length > 255 then false
  else verifyFormatted E P H expandMatrix challenge verificationKey
    (formattedPrefix context ++ message) signature

/-- `value lsl d` on a decoded `t1` coefficient (`< 2^10`) is exact and
    `Portable`: it equals `value · 2^13 < 2^23`. -/
theorem shifted_t1_portable {value : ℕ} (h : value < 2 ^ 10) :
    value <<< d = value * 2 ^ d ∧ Portable ((value <<< d : ℕ) : ℤ) := by
  rw [Nat.shiftLeft_eq]
  exact ⟨rfl, Portable.of_nat_lt (by unfold d; omega)⟩

/-- FIPS 204 Algorithm 8, `ML-DSA.Verify_internal(pk, M′, σ)`. -/
noncomputable def verifyInternal (F : VerifyFips) (P : Params) (lam : ℕ) (H G : XOF)
    (pk M' sig : Bytes) : Bool :=
  let rho := (F.pkDecode pk).1
  let t1 := (F.pkDecode pk).2
  match F.sigDecode sig with
  | none => false
  | some (cTilde, z, h) =>
    let A := expandA G rho
    let tr := H.squeeze pk 64
    let mu := H.squeeze (tr ++ M') 64
    let c := sampleInBall P.tau (H cTilde)
    let wApprox : PolyVec := fun r => F.NTTinv (F.subPoly
      (F.mulMatVec A (fun i => F.NTT (z i)) r)
      (F.mulNTT (F.NTT c) (F.NTT (fun i => t1 r i * 2 ^ d))))
    let w1' : PolyVec := fun r i => F.useHint (h r i) (wApprox r i)
    let cTilde' := H.squeeze (mu ++ (List.range P.k).foldl
      (fun acc i => acc ++ F.simpleBitPack (w1' i) ((q - 1) / (2 * P.gamma2) - 1)) []) (lam / 4)
    F.zNormOk z && decide (cTilde = cTilde')

/-- FIPS 204 Algorithm 3, `ML-DSA.Verify(pk, M, σ, ctx)`. -/
noncomputable def mldsaVerify (F : VerifyFips) (P : Params) (lam : ℕ) (H G : XOF)
    (pk M sig ctx : Bytes) : Bool :=
  if ctx.length > 255 then false
  else verifyInternal F P lam H G pk
    (integerToBytes 0 1 ++ integerToBytes ctx.length 1 ++ ctx ++ M) sig

/-- A verification key or signature of the wrong length is rejected
    (FIPS 204 only defines Algorithm 8 on inputs of the right lengths). -/
theorem verify_wrong_length (E : VerifyOps) (F : VerifyFips) {P : Params} (hR : E.Refines F P)
    (H : XOF) (expandMatrix : Bytes → PolyMat) (challenge : Bytes → Poly) (pk M' sig : Bytes)
    (h : pk.length ≠ P.verificationKeySize ∨ sig.length ≠ P.signatureSize) :
    verifyFormatted E P H expandMatrix challenge pk M' sig = false := by
  unfold verifyFormatted verifyMu
  simp only [XOF.length_squeeze, ne_eq, not_true_eq_false, ite_false,
    hR.decodeVerificationKey, hR.decodeSignature]
  rcases h with h | h
  · simp [h]
  · by_cases hpk : pk.length = P.verificationKeySize <;> simp [h, hpk]

/-- **Obligation 7 (verification, Algorithms 8 and 3).** For a verification
    key and a signature of the right lengths, `verify_formatted` is
    Algorithm 8 and `verify` is Algorithm 3 (a context longer than 255 bytes
    gives `false`), given the refinement hypotheses, `λ = 4·c_tilde_bytes`,
    and that the `expand_matrix`/`challenge_polynomial` calls return. -/
theorem verify_eq (E : VerifyOps) (F : VerifyFips) {P : Params} (hP : P.Valid)
    (hR : E.Refines F P) {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam) (H G : XOF)
    (expandMatrix : Bytes → PolyMat) (hA : ∀ rho, ExpandMatrixReturns G P rho (expandMatrix rho))
    (challenge : Bytes → Poly) (hc : ∀ ct, ChallengeReturns P.tau H ct 136 (challenge ct))
    (pk : Bytes) (hpk : pk.length = P.verificationKeySize) (context message sig : Bytes)
    (hsig : sig.length = P.signatureSize) :
    (∀ M', verifyFormatted E P H expandMatrix challenge pk M' sig =
      verifyInternal F P lam H G pk M' sig) ∧
    verify E P H expandMatrix challenge context pk message sig =
      mldsaVerify F P lam H G pk message sig context := by
  obtain ⟨-, -, -, -, htau, -⟩ := hP.facts
  have hlam4 : lam / 4 = P.cTildeBytes := by omega
  have hdec : ∀ a b : Bytes, equalString a b = decide (a = b) := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp [(equalString_iff a a).mpr rfl]
    · simp only [hab, decide_false]
      cases he : equalString a b
      · rfl
      · exact absurd ((equalString_iff a b).mp he) hab
  have hvf : ∀ M', verifyFormatted E P H expandMatrix challenge pk M' sig =
      verifyInternal F P lam H G pk M' sig := by
    intro M'
    unfold verifyFormatted verifyMu verifyInternal
    simp only [XOF.length_squeeze, ne_eq, not_true_eq_false, ite_false,
      hR.decodeVerificationKey, hpk, ite_true, hR.decodeSignature]
    set rho := (F.pkDecode pk).1 with hrho
    set t1 := (F.pkDecode pk).2 with ht1
    · simp only [hsig, ite_true]
      cases hsd : F.sigDecode sig with
      | none => rfl
      | some ctzh =>
        obtain ⟨cTilde, z, h⟩ := ctzh
        simp only [hR.normViolation]
        have hA' := (expandMatrix_spec G hP rho).1 _ (hA rho)
        cases hz : F.zNormOk z
        · simp
        · simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.true_and, hdec, hlam4]
          rw [← challenge_returns_eq (by omega) (hc cTilde)]
          have hB : concatMap P.k E.packW1 (fun row index =>
                E.useHint (E.inverseNtt (fun index =>
                  E.subMod (E.matrixVectorNtt (expandMatrix rho) (fun i => E.ntt (z i)) row index)
                    (E.pointwise (E.ntt (challenge cTilde))
                      (E.ntt fun index => t1 row index * 2 ^ d) index)) index) (h row index)) =
              (List.range P.k).foldl (fun acc i => acc ++ F.simpleBitPack
                (fun i_1 => F.useHint (h i i_1) (F.NTTinv (F.subPoly
                  (F.mulMatVec (expandA G rho) (fun i => F.NTT (z i)) i)
                  (F.mulNTT (F.NTT (challenge cTilde)) (F.NTT fun i_2 => t1 i i_2 * 2 ^ d))) i_1))
                ((q - 1) / (2 * P.gamma2) - 1)) [] := by
            rw [concatMap_eq_foldl]
            apply List.foldl_ext
            intro acc row hrow
            have hrow' := List.mem_range.mp hrow
            rw [hR.packW1]
            congr 2
            funext index
            rw [hR.useHint]
            congr 1
            rw [show (fun index =>
                E.subMod (E.matrixVectorNtt (expandMatrix rho) (fun i => E.ntt (z i)) row index)
                  (E.pointwise (E.ntt (challenge cTilde))
                    (E.ntt fun index => t1 row index * 2 ^ d) index)) =
                F.subPoly (E.matrixVectorNtt (expandMatrix rho) (fun i => E.ntt (z i)) row)
                  (E.pointwise (E.ntt (challenge cTilde)) (E.ntt fun index => t1 row index * 2 ^ d))
                from hR.subMod _ _]
            rw [hR.inverseNtt, hR.matrixVectorNtt, hR.ntt, hR.pointwise,
              hR.mulMatVec_local _ _ _ hA' row hrow']
          rw [hB]
  refine ⟨hvf, ?_⟩
  unfold verify mldsaVerify
  split_ifs with h
  · rfl
  · rw [hvf, formattedPrefix_eq (by omega)]

end OcamlPq.MLDSAAlg
