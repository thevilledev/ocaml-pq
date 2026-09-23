import OcamlPq.EndToEnd.MLDSA.SignCore

/-!
# Signing end to end

* `signOps P key`: the `MLDSAAlg.SignOps` bundle of the concrete OCaml
  models for the signing key `key` (arithmetic area; `pack_w1`, `unpack_z`,
  `encode_signature` from the Encoding area; the candidate of
  `SignCore.lean`).
* `signFips P key`: the `SignFips` bundle of FIPS 204 transcriptions
  (Algorithms 41, 42, 48, 37, 16, 7 lines 15–30, 26, 19).

**`SignOps.Refines (signOps P key) (signFips P key) P` is false** as stated:
`packW1`, `candidate_eq` and `encodeSignature` quantify over all inputs, and
the code equals FIPS 204 only on the inputs signing produces (`w1` in
`[0, (q−1)/(2γ2))`, masks in `(−γ1, γ1]`, challenges of weight `τ`, accepted
`(z, h)` in range). `signOpsIdeal` replaces those three fields by FIPS's and
satisfies `Refines` (`signOpsIdeal_refines`); `signMu_ideal` shows the OCaml
`sign_mu_with_randomness` is unchanged by the replacement for keys with
`s1, s2 ∈ [−η, η]`.

`MLDSAAlg.signMuWithRandomness_eq` (and `mldsaSign_eq`,
`signDeterministic_eq`) takes `∀ c̃, ChallengeReturns τ H c̃ 136 (challenge
c̃)`, i.e. that `challenge_polynomial` terminates on *every* input; the
`*_at` versions below take the weaker `∀ c̃, challenge c̃ = SampleInBall(c̃)`
(implied by the former through `challenge_returns_eq`, and satisfied by
`fun c̃ => sampleInBall τ (H c̃)` itself), and the matrix in value form.
-/

namespace OcamlPq.EndToEnd.MLDSA

open OcamlPq.MLDSAAlg

/-! ## The bundles -/

/-- **The OCaml building blocks of `sign_mu_with_randomness`** for the
    signing key `key` (`SignOps`). -/
def signOps (P : Params) (key : ExpandedKey) : SignOps where
  ntt := MLDSA.ntt
  inverseNtt := ocamlInverseNtt
  matrixVectorNtt := ocamlMatVec P.l
  decompose := MLDSA.decompose P.gamma2
  packW1 := ocamlPackW1 P.gamma2
  candidate := ocamlCandidate P key
  encodeSignature := ocamlEncodeSig P
  unpackZ := ocamlUnpackZ P.gamma1

/-- **The FIPS 204 building blocks of Algorithm 7** for the decoded key
    `key` (`SignFips`). -/
def signFips (P : Params) (key : ExpandedKey) : SignFips where
  NTT := fipsNTT
  NTTinv := fipsNTTinv
  mulMatVec := fipsMulMatVec P.l
  highBits := MLDSA.highBits P.gamma2
  simpleBitPack := fipsSimpleBitPack
  finish := fipsFinish P key
  sigEncode := fipsSigEncode P
  bitUnpack := fipsBitUnpack

/-- `signOps` with `pack_w1`, the candidate and `encode_signature` replaced by
    FIPS's (used only in proofs). The candidate rebuilds `w ≡ w1·2γ2 + w0`. -/
def signOpsIdeal (P : Params) (key : ExpandedKey) : SignOps where
  ntt := MLDSA.ntt
  inverseNtt := ocamlInverseNtt
  matrixVectorNtt := ocamlMatVec P.l
  decompose := MLDSA.decompose P.gamma2
  packW1 := fun p => fipsSimpleBitPack p ((q - 1) / (2 * P.gamma2) - 1)
  candidate := fun y w0 w1 cHat =>
    fipsFinish P key y (fun r i => w1 r i * (2 * (P.gamma2 : ℤ)) + w0 r i) cHat
  encodeSignature := fipsSigEncode P
  unpackZ := ocamlUnpackZ P.gamma1

/-- `fipsFinish` on `w1·2γ2 + w0` with `(w1, w0) = Decompose(w)` is
    `fipsFinish` on `w`. -/
theorem fipsFinish_decompose {P : Params} (hP : P.Valid) (key : ExpandedKey) (y w : PolyVec)
    (cHat : Poly) :
    fipsFinish P key y (fun r i => (MLDSA.decompose P.gamma2 (w r i)).1 * (2 * (P.gamma2 : ℤ)) +
      (MLDSA.decompose P.gamma2 (w r i)).2) cHat = fipsFinish P key y w cHat := by
  have hf := e2eFacts hP
  apply fipsFinish_congr_w
  intro r _ i _
  have := (MLDSA.decomposeSpec_range hf.gamma2Ok (w r i)).2.2.2.2
  rw [MLDSA.decompose_eq_spec hf.gamma2Ok]
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr this

/-- The `pack_w1` field of `SignOps.Refines` on the range of `Decompose`. -/
theorem decompose_high_range {P : Params} (hP : P.Valid) (x : ℤ) :
    0 ≤ (MLDSA.decompose P.gamma2 x).1 ∧ (MLDSA.decompose P.gamma2 x).1 < (w1Count P : ℤ) := by
  have hf := e2eFacts hP
  have := MLDSA.decomposeSpec_range hf.gamma2Ok x
  rw [MLDSA.decompose_eq_spec hf.gamma2Ok]
  unfold w1Count
  rw [hf.w1Count_int]
  exact ⟨this.1, this.2.1⟩

/-- **`signOpsIdeal P key` refines `signFips P key`** (every field of
    `SignOps.Refines`). The fields shared with `signOps` are the arithmetic
    and Encoding areas' theorems (`ntt_eq_fips`, …, `decompose_eq_spec`,
    `unpackZ_eq`). -/
theorem signOpsIdeal_refines {P : Params} (hP : P.Valid) (key : ExpandedKey) :
    (signOpsIdeal P key).Refines (signFips P key) P where
  ntt := by simp only [signOpsIdeal, signFips]; exact ntt_eq_fips
  inverseNtt := by simp only [signOpsIdeal, signFips]; exact inverseNtt_eq_fips
  matrixVectorNtt := by simp only [signOpsIdeal, signFips]; exact matVec_eq_fips P.l
  highBits := fun x => by
    simp only [signOpsIdeal, signFips]
    unfold MLDSA.highBits
    rw [MLDSA.decompose_eq_spec (e2eFacts hP).gamma2Ok]
  packW1 := fun p => by simp only [signOpsIdeal, signFips]
  candidate_eq := fun y w cHat => by
    simp only [signOpsIdeal, signFips]
    exact fipsFinish_decompose hP key y w cHat
  encodeSignature := by simp only [signOpsIdeal, signFips]
  unpackZ := fun v hv => by
    simp only [signOpsIdeal, signFips]
    exact unpackZ_eq_fips (e2eFacts hP).gamma1 v (by rw [hv, (e2eFacts hP).zBits])
  mulMatVec_local := fun A A' v v' hA hv r hr => by
    simp only [signFips]
    exact fipsMulMatVec_local P.l A A' v v' r (hA r hr) hv
  finish_local := fun y y' w w' cHat hy hw => by
    simp only [signFips]
    exact fipsFinish_local P key y y' w w' cHat hy hw

/-! ## The OCaml loop versus the ideal one -/

/-- `attempt` only depends on the per-iteration function at the mask
    vectors it computes. -/
theorem attempt_congr {σ : Type} (l : ℕ) (mask : ℕ → Poly) (iter iter' : (ℕ → Poly) → Option σ)
    (h : ∀ i, iter (maskVector l mask i) = iter' (maskVector l mask i)) :
    attempt l mask iter 0 = attempt l mask iter' 0 := by
  cases ha : attempt l mask iter 0 with
  | error e =>
    obtain ⟨rfl, hall⟩ := (attempt_error_iff l mask iter e).mp ha
    exact ((attempt_error_iff l mask iter' _).mpr ⟨rfl, fun i hi => (h i) ▸ hall i hi⟩).symm
  | ok sig =>
    obtain ⟨i, hi, h1, h2⟩ := (attempt_ok_iff l mask iter sig).mp ha
    exact ((attempt_ok_iff l mask iter' sig).mpr
      ⟨i, hi, (h i) ▸ h1, fun j hj => (h j) ▸ h2 j hj⟩).symm

/-- The OCaml candidate is FIPS's for the challenges `SampleInBall` produces. -/
theorem ocamlCandidate_eq_fipsFinish_sib {P : Params} (hP : P.Valid) (key : ExpandedKey)
    (hs1 : ∀ r < P.l, ∀ i < 256, -(P.eta : ℤ) ≤ key.s1 r i ∧ key.s1 r i ≤ P.eta)
    (hs2 : ∀ r < P.k, ∀ i < 256, -(P.eta : ℤ) ≤ key.s2 r i ∧ key.s2 r i ≤ P.eta)
    (y w : PolyVec) (hy : ∀ r < P.l, ∀ i < 256, -(P.gamma1 : ℤ) < y r i ∧ y r i ≤ P.gamma1)
    (s : ℕ → Byte) :
    ocamlCandidate P key y (fun r i => (MLDSA.decompose P.gamma2 (w r i)).2)
        (fun r i => (MLDSA.decompose P.gamma2 (w r i)).1) (MLDSA.ntt (sampleInBall P.tau s)) =
      fipsFinish P key y w (fipsNTT (sampleInBall P.tau s)) := by
  have hb := sampleInBall_ball (tau := P.tau) (by have := (e2eFacts hP).tau_le; omega) s
  exact ocamlCandidate_eq_fipsFinish hP key hs1 hs2 y w hy _ hb.1 hb.2

/-- `pack_w1` on every row is FIPS's `SimpleBitPack` for `w1` in
    `[0, (q − 1)/(2γ2))`. -/
theorem concatMap_packW1_eq_fips {P : Params} (hP : P.Valid) (w1 : PolyVec)
    (h : ∀ r < P.k, ∀ i < 256, 0 ≤ w1 r i ∧ w1 r i < (w1Count P : ℤ)) :
    concatMap P.k (ocamlPackW1 P.gamma2) w1 =
      concatMap P.k (fun p => fipsSimpleBitPack p ((q - 1) / (2 * P.gamma2) - 1)) w1 := by
  unfold concatMap
  rw [List.map_congr_left (fun r hr => packW1_eq_fips hP _ (h r (List.mem_range.mp hr)))]

/-- **One iteration: the OCaml bundle equals the ideal one** on masks in
    `(−γ1, γ1]`. -/
theorem signIter_ideal {P : Params} (hP : P.Valid) (key : ExpandedKey)
    (hs1 : ∀ r < P.l, ∀ i < 256, -(P.eta : ℤ) ≤ key.s1 r i ∧ key.s1 r i ≤ P.eta)
    (hs2 : ∀ r < P.k, ∀ i < 256, -(P.eta : ℤ) ≤ key.s2 r i ∧ key.s2 r i ≤ P.eta)
    (H : XOF) (matrix : PolyMat) (challenge : Bytes → Poly)
    (hc : ∀ ct, challenge ct = sampleInBall P.tau (H ct)) (mu : Bytes) (y : PolyVec)
    (hy : ∀ r < P.l, ∀ i < 256, -(P.gamma1 : ℤ) < y r i ∧ y r i ≤ P.gamma1) :
    signIter (signOps P key) P H matrix challenge mu y =
      signIter (signOpsIdeal P key) P H matrix challenge mu y := by
  unfold signIter
  simp only [signOps, signOpsIdeal]
  rw [concatMap_packW1_eq_fips hP _ (fun r _ i _ => decompose_high_range hP _), hc,
    ocamlCandidate_eq_fipsFinish_sib hP key hs1 hs2 y _ hy, ntt_eq_fips, fipsFinish_decompose hP]
  split
  · next zh hfin =>
    simp only [Option.some.injEq]
    obtain ⟨z, h⟩ := zh
    exact encodeSig_eq_fips hP _ z h (by simp) (fipsFinish_accepted hP hfin).1
      (fipsFinish_accepted hP hfin).2
  · rfl

/-- **`sign_mu_with_randomness` with the OCaml bundle equals it with the
    ideal bundle**, for keys with `s1, s2 ∈ [−η, η]`. -/
theorem signMu_ideal {P : Params} (hP : P.Valid) (key : ExpandedKey)
    (hs1 : ∀ r < P.l, ∀ i < 256, -(P.eta : ℤ) ≤ key.s1 r i ∧ key.s1 r i ≤ P.eta)
    (hs2 : ∀ r < P.k, ∀ i < 256, -(P.eta : ℤ) ≤ key.s2 r i ∧ key.s2 r i ≤ P.eta)
    (H : XOF) (matrix : PolyMat) (challenge : Bytes → Poly)
    (hc : ∀ ct, challenge ct = sampleInBall P.tau (H ct)) (mu rnd : Bytes) :
    signMuWithRandomness (signOps P key) P H matrix challenge key mu rnd =
      signMuWithRandomness (signOpsIdeal P key) P H matrix challenge key mu rnd := by
  have hf := e2eFacts hP
  have hu : (signOpsIdeal P key).unpackZ = (signOps P key).unpackZ := by
    simp only [signOps, signOpsIdeal]
  unfold signMuWithRandomness
  rw [hu]
  split_ifs
  · rfl
  · rfl
  · apply attempt_congr
    intro i
    apply signIter_ideal hP key hs1 hs2 H matrix challenge hc mu
    intro r _ j _
    simp only [maskVector, maskPolynomial, signOps]
    exact unpackZ_range hf.gamma1 _ (by simp [hf.zPacked]) j

/-! ## `MLDSAAlg`'s signing theorems with value-form hypotheses -/

/-- `MLDSAAlg.signIter_eq` with `challenge = SampleInBall ∘ H` and the matrix
    in value form. (Same proof.) -/
theorem signIter_eq_at (E : SignOps) (F : SignFips) {P : Params}
    (hR : E.Refines F P) {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam) (H G : XOF) (rho : Bytes)
    (matrix : PolyMat) (hA' : ∀ r < P.k, ∀ s < P.l, matrix r s = expandA G rho r s)
    (challenge : Bytes → Poly) (hc : ∀ ct, challenge ct = sampleInBall P.tau (H ct))
    (mu : Bytes) (y y' : PolyVec) (hy : ∀ r < P.l, y r = y' r) :
    signIter E P H matrix challenge mu y = alg7Step F P lam H (expandA G rho) mu y' := by
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
  rw [henc, hlam4, hc, hR.candidate_eq, hR.finish_local y y' _ _ _ hy hWW, hR.encodeSignature]

/-- `MLDSAAlg.signMuWithRandomness_eq` with value-form hypotheses. -/
theorem signMuWithRandomness_eq_at (E : SignOps) (F : SignFips) {P : Params} (hP : P.Valid)
    (hR : E.Refines F P) {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam) (H G : XOF)
    (key : ExpandedKey) (matrix : PolyMat)
    (hA' : ∀ r < P.k, ∀ s < P.l, matrix r s = expandA G key.rho r s)
    (challenge : Bytes → Poly) (hc : ∀ ct, challenge ct = sampleInBall P.tau (H ct))
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
    (fun y y' hy => signIter_eq_at E F hR hlam H G key.rho matrix hA' challenge hc mu y y' hy)
  obtain ⟨hok1, hok2, herr⟩ := this
  rw [hsig]
  refine ⟨fun sig => ⟨fun h => hok2 sig h, fun h => hok1 821 le_rfl sig h⟩, fun e => herr e⟩

/-- `MLDSAAlg.mldsaSign_eq` with value-form hypotheses. -/
theorem mldsaSign_eq_at (E : SignOps) (F : SignFips) {P : Params} (hP : P.Valid)
    (hR : E.Refines F P) {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam) (H G : XOF)
    (key : ExpandedKey) (matrix : PolyMat)
    (hA' : ∀ r < P.k, ∀ s < P.l, matrix r s = expandA G key.rho r s)
    (challenge : Bytes → Poly) (hc : ∀ ct, challenge ct = sampleInBall P.tau (H ct))
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
    have := (signMuWithRandomness_eq_at E F hP hR hlam H G key matrix hA' challenge hc
      (H.squeeze (key.tr ++ (formattedPrefix context ++ message)) 64) (random 32)).2.2 hmu hr
    have e1 : (sign E P H matrix challenge context random key message).2 =
        some (signMuWithRandomness E P H matrix challenge key
          (H.squeeze (key.tr ++ (formattedPrefix context ++ message)) 64) (random 32)) := by
      simp [sign, signWithRandomness, signFormattedWithRandomness, hr,
        show ¬ context.length > 255 by omega]
    have e2 : mldsaSign F P lam H G key message context (random 32) =
        signInternalMu F P lam H G key.rho key.key
          (H.squeeze (key.tr ++ (formattedPrefix context ++ message)) 64) (random 32) 821 := by
      simp [mldsaSign, show ¬ context.length > 255 by omega, formattedPrefix_eq h]
    rw [e1, e2]
    refine ⟨fun sig => ?_, fun e => ?_⟩
    · rw [Option.some.injEq]; exact this.1 sig
    · rw [Option.some.injEq]; exact this.2 e

/-- `MLDSAAlg.signDeterministic_eq` with value-form hypotheses. -/
theorem signDeterministic_eq_at (E : SignOps) (F : SignFips) {P : Params} (hP : P.Valid)
    (hR : E.Refines F P) {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam) (H G : XOF)
    (key : ExpandedKey) (matrix : PolyMat)
    (hA' : ∀ r < P.k, ∀ s < P.l, matrix r s = expandA G key.rho r s)
    (challenge : Bytes → Poly) (hc : ∀ ct, challenge ct = sampleInBall P.tau (H ct))
    (context message : Bytes) :
    (context.length > 255 → signDeterministic E P H matrix challenge context key message =
      .error (.contextTooLong context.length)) ∧
    (context.length ≤ 255 →
      (∀ sig, signDeterministic E P H matrix challenge context key message = .ok sig ↔
        mldsaSign F P lam H G key message context (List.replicate 32 0) = some sig) ∧
      (∀ e, signDeterministic E P H matrix challenge context key message = .error e ↔
        e = .signingFailed ∧
          mldsaSign F P lam H G key message context (List.replicate 32 0) = none)) := by
  refine ⟨fun h => by simp [signDeterministic, signWithRandomness, h], fun h => ?_⟩
  have hmu : (H.squeeze (key.tr ++ (formattedPrefix context ++ message)) 64).length = 64 := by simp
  have := (signMuWithRandomness_eq_at E F hP hR hlam H G key matrix hA' challenge hc
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

/-! ## End to end -/

/-- The signing key's secrets are in `[−η, η]` (true for every key the OCaml
    API produces: by `RejBoundedPoly` for generated keys, by `unpack_eta`'s
    range check for imported ones). -/
def SecretsInRange (P : Params) (key : ExpandedKey) : Prop :=
  (∀ r < P.l, ∀ i < 256, -(P.eta : ℤ) ≤ key.s1 r i ∧ key.s1 r i ≤ P.eta) ∧
  (∀ r < P.k, ∀ i < 256, -(P.eta : ℤ) ≤ key.s2 r i ∧ key.s2 r i ≤ P.eta)

theorem unpackEta_some_range {eta : ℕ} {v : List ℕ} {p : List ℤ}
    (h : Encoding.Mldsa.unpackEta eta v = some p) : ∀ w ∈ p, -(eta : ℤ) ≤ w ∧ w ≤ eta := by
  unfold Encoding.Mldsa.unpackEta at h
  simp only at h
  split_ifs at h with hany
  cases h
  simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and, not_lt] at hany
  intro w hw
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
  have := hany c hc
  omega

theorem listsToVec_range {L : List (List ℤ)} {lo hi : ℤ} (h0 : lo ≤ 0) (h1 : 0 ≤ hi)
    (h : ∀ row ∈ L, ∀ x ∈ row, lo ≤ x ∧ x ≤ hi) (r i : ℕ) :
    lo ≤ listsToVec L r i ∧ listsToVec L r i ≤ hi := by
  unfold listsToVec
  by_cases hr : r < L.length
  · rw [List.getD_eq_getElem _ _ hr]
    exact listToPoly_range h0 h1 (h _ (List.getElem_mem hr)) i
  · rw [List.getD_eq_default _ _ (by omega)]
    exact listToPoly_range h0 h1 (by simp) i

/-- **Imported keys have secrets in `[−η, η]`.** Whatever
    `decode_expanded_signing_key` (Encoding model) returns, its `s1` and `s2`
    come from `unpack_eta`, which rejects codes above `2η`. -/
theorem decodeSk_secretsInRange (P : Params) (octets : List ℕ) {rho key tr : List ℕ}
    {s1 s2 t0 : List (List ℤ)}
    (h : Encoding.Mldsa.decodeSk (encParams P) octets = some (rho, key, tr, s1, s2, t0)) :
    SecretsInRange P ⟨natToBytes rho, natToBytes key, natToBytes tr, listsToVec s1,
      listsToVec s2, listsToVec t0⟩ := by
  have hrow : ∀ (len pos : ℕ) (L : List (List ℤ)) (pos' : ℕ),
      Encoding.Mldsa.decodeEtaVector (encParams P) octets len pos = (some L, pos') →
      ∀ row ∈ L, ∀ x ∈ row, -(P.eta : ℤ) ≤ x ∧ x ≤ P.eta := by
    intro len pos L pos' hd row hr x hx
    rw [Encoding.Mldsa.decodeEtaVector_eq] at hd
    simp only [Prod.mk.injEq] at hd
    obtain ⟨hd, -⟩ := hd
    split_ifs at hd
    cases hd
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
    cases hu : Encoding.Mldsa.unpackEta (encParams P).eta
        (Encoding.Mldsa.etaBlock (encParams P) octets pos i) with
    | none => rw [hu] at hx; simp at hx
    | some p => rw [hu] at hx; exact unpackEta_some_range hu x hx
  unfold Encoding.Mldsa.decodeSk at h
  split_ifs at h
  simp only at h
  split at h
  · cases h
  · rename_i s1' pos1 hd1
    split at h
    · cases h
    · rename_i s2' pos2 hd2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, -, rfl, rfl, -⟩ := h
      exact ⟨fun r _ i _ => listsToVec_range (by omega) (by omega) (hrow _ _ _ _ hd1) r i,
        fun r _ i _ => listsToVec_range (by omega) (by omega) (hrow _ _ _ _ hd2) r i⟩

/-- **`sign_mu_with_randomness`, end to end (FIPS 204 Algorithm 7).** For a
    valid parameter set, a key with secrets in `[−η, η]`, the matrix `A`
    returned by `expand_matrix key.rho`, and `challenge` the values of
    `challenge_polynomial · 136` (`= SampleInBall`; see
    `challengeValue_of_returns`): `μ` must have 64 bytes and `rnd` 32, else
    `Invalid_length`; otherwise the OCaml result (OCaml SHAKE) is `Ok σ` iff
    FIPS 204 `ML-DSA.Sign_internal` (FIPS 202 SHAKE, `ρ″ = H(K ‖ rnd ‖ μ,
    64)`) returns `σ` within 821 iterations, and `Error Signing_failed` iff it
    does not finish within 821 iterations. -/
theorem signMu_e2e {P : Params} (hP : P.Valid) {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam)
    (key : ExpandedKey) (hkey : SecretsInRange P key)
    (A : PolyMat) (hA : ExpandMatrixReturns ocamlShake128 P key.rho A)
    (challenge : Bytes → Poly) (hc : ∀ ct, challenge ct = sampleInBall P.tau (ocamlShake256 ct))
    (mu rnd : Bytes) :
    (mu.length ≠ 64 → signMuWithRandomness (signOps P key) P ocamlShake256 A challenge key mu rnd =
      .error (.invalidLength "ML-DSA message representative" 64 mu.length)) ∧
    (mu.length = 64 → rnd.length ≠ 32 →
      signMuWithRandomness (signOps P key) P ocamlShake256 A challenge key mu rnd =
        .error (.invalidLength "ML-DSA signing randomness" 32 rnd.length)) ∧
    (mu.length = 64 → rnd.length = 32 →
      (∀ sig, signMuWithRandomness (signOps P key) P ocamlShake256 A challenge key mu rnd =
          .ok sig ↔
        signInternalMu (signFips P key) P lam fipsShake256 fipsShake128 key.rho key.key mu rnd 821 =
          some sig) ∧
      (∀ e, signMuWithRandomness (signOps P key) P ocamlShake256 A challenge key mu rnd =
          .error e ↔
        e = .signingFailed ∧
          signInternalMu (signFips P key) P lam fipsShake256 fipsShake128 key.rho key.key mu rnd
            821 = none)) := by
  rw [signMu_ideal hP key hkey.1 hkey.2 _ A challenge hc, fipsShake128_eq, fipsShake256_eq]
  exact signMuWithRandomness_eq_at _ _ hP (signOpsIdeal_refines hP key) hlam _ _ key A
    ((expandMatrix_spec _ hP _).1 A hA) challenge hc mu rnd

/-- **`sign`, end to end (FIPS 204 Algorithm 2, `ML-DSA.Sign`).** A context
    over 255 bytes gives `Context_too_long` without calling the randomness
    source; otherwise exactly 32 bytes are requested, and if the callback
    returns 32 bytes `rnd` the result is `Ok σ` iff Algorithm 2 with `rnd`
    (FIPS 202 SHAKE) returns `σ` within 821 iterations, and otherwise
    `Signing_failed`. -/
theorem sign_e2e {P : Params} (hP : P.Valid) {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam)
    (key : ExpandedKey) (hkey : SecretsInRange P key)
    (A : PolyMat) (hA : ExpandMatrixReturns ocamlShake128 P key.rho A)
    (challenge : Bytes → Poly) (hc : ∀ ct, challenge ct = sampleInBall P.tau (ocamlShake256 ct))
    (context message : Bytes) (random : ℕ → Bytes) :
    (context.length > 255 → sign (signOps P key) P ocamlShake256 A challenge context random key
      message = ([], some (.error (.contextTooLong context.length)))) ∧
    (context.length ≤ 255 →
      (sign (signOps P key) P ocamlShake256 A challenge context random key message).1 = [32]) ∧
    (context.length ≤ 255 → (random 32).length = 32 →
      (∀ sig, (sign (signOps P key) P ocamlShake256 A challenge context random key message).2 =
          some (.ok sig) ↔
        mldsaSign (signFips P key) P lam fipsShake256 fipsShake128 key message context
          (random 32) = some sig) ∧
      (∀ e, (sign (signOps P key) P ocamlShake256 A challenge context random key message).2 =
          some (.error e) ↔
        e = .signingFailed ∧ mldsaSign (signFips P key) P lam fipsShake256 fipsShake128 key message
          context (random 32) = none)) := by
  have hsame : sign (signOps P key) P ocamlShake256 A challenge context random key message =
      sign (signOpsIdeal P key) P ocamlShake256 A challenge context random key message := by
    simp only [sign, signWithRandomness, signFormattedWithRandomness,
      signMu_ideal hP key hkey.1 hkey.2 _ A challenge hc]
  rw [hsame, fipsShake128_eq, fipsShake256_eq]
  exact mldsaSign_eq_at _ _ hP (signOpsIdeal_refines hP key) hlam _ _ key A
    ((expandMatrix_spec _ hP _).1 A hA) challenge hc context message random

/-- **`sign_deterministic`, end to end (FIPS 204 Algorithm 2 with
    `rnd = {0}^32`).** -/
theorem signDeterministic_e2e {P : Params} (hP : P.Valid) {lam : ℕ}
    (hlam : P.cTildeBytes * 4 = lam) (key : ExpandedKey) (hkey : SecretsInRange P key)
    (A : PolyMat) (hA : ExpandMatrixReturns ocamlShake128 P key.rho A)
    (challenge : Bytes → Poly) (hc : ∀ ct, challenge ct = sampleInBall P.tau (ocamlShake256 ct))
    (context message : Bytes) :
    (context.length > 255 → signDeterministic (signOps P key) P ocamlShake256 A challenge context
      key message = .error (.contextTooLong context.length)) ∧
    (context.length ≤ 255 →
      (∀ sig, signDeterministic (signOps P key) P ocamlShake256 A challenge context key message =
          .ok sig ↔
        mldsaSign (signFips P key) P lam fipsShake256 fipsShake128 key message context
          (List.replicate 32 0) = some sig) ∧
      (∀ e, signDeterministic (signOps P key) P ocamlShake256 A challenge context key message =
          .error e ↔
        e = .signingFailed ∧ mldsaSign (signFips P key) P lam fipsShake256 fipsShake128 key message
          context (List.replicate 32 0) = none)) := by
  have hsame : signDeterministic (signOps P key) P ocamlShake256 A challenge context key message =
      signDeterministic (signOpsIdeal P key) P ocamlShake256 A challenge context key message := by
    simp only [signDeterministic, signWithRandomness, signFormattedWithRandomness,
      signMu_ideal hP key hkey.1 hkey.2 _ A challenge hc]
  rw [hsame, fipsShake128_eq, fipsShake256_eq]
  exact signDeterministic_eq_at _ _ hP (signOpsIdeal_refines hP key) hlam _ _ key A
    ((expandMatrix_spec _ hP _).1 A hA) challenge hc context message

/-- Every function describing the values returned by the OCaml
    `challenge_polynomial · 136` on all inputs satisfies the challenge
    hypothesis of the end-to-end theorems (`challenge_returns_eq`); so does
    `fun c̃ => sampleInBall τ (H c̃)` itself. -/
theorem challengeValue_of_returns {P : Params} (hP : P.Valid) (H : XOF)
    (challenge : Bytes → Poly) (hc : ∀ ct, ChallengeReturns P.tau H ct 136 (challenge ct)) :
    ∀ ct, challenge ct = sampleInBall P.tau (H ct) :=
  fun ct => challenge_returns_eq (by have := (e2eFacts hP).tau_le; omega) (hc ct)

end OcamlPq.EndToEnd.MLDSA
