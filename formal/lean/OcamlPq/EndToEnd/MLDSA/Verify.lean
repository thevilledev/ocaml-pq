import OcamlPq.EndToEnd.MLDSA.Sign

/-!
# Verification end to end

* `verifyOps P`: the `MLDSAAlg.VerifyOps` bundle of the concrete OCaml models
  (`decode_verification_key`, `decode_signature`, the `z` norm check,
  `ntt`, `inverse_ntt`, `matrix_vector_ntt`, `pointwise`, `sub_mod`,
  `use_hint`, `pack_w1`).
* `verifyFips P`: the `VerifyFips` bundle of FIPS 204 transcriptions
  (`pkDecode` (Algorithm 23, `Pack.lean`), `sigDecode` (27), `‖z‖∞ < γ1 − β`,
  Algorithms 41, 42, 48, 45, subtraction in `R_q`, `UseHint` (40),
  `SimpleBitPack` (16)).

**`VerifyOps.Refines (verifyOps P) (verifyFips P) P` is false**: its field
`useHint : ∀ r h, E.useHint r h = F.useHint h r` fails for hint values other
than 0 and 1 (`verifyOps_useHint_ne`: the code treats every nonzero hint as
1, FIPS 204's `UseHint` every value other than 1 as 0; decoded hints are
always 0/1), and `packW1` fails outside `[0, (q − 1)/(2γ2))`. The other
fields hold. `verifyOpsIdeal` replaces the two; it satisfies `Refines`, and
`verifyMu_ideal` shows the OCaml `verify_mu` unchanged.

`MLDSAAlg.verify_eq` asks for `expand_matrix` and `challenge_polynomial` to
return on *every* input; `verify_eq_at` re-proves it with hypotheses only at
the `ρ` and `c̃` decoded from the key and signature.
-/

namespace OcamlPq.EndToEnd.MLDSA

open OcamlPq.MLDSAAlg

/-! ## The bundles -/

/-- **The OCaml building blocks of `verify_mu`** (`VerifyOps`). -/
def verifyOps (P : Params) : VerifyOps where
  decodeVerificationKey := ocamlDecodeVk P
  decodeSignature := ocamlDecodeSig P
  normViolation := ocamlZNormViolation P
  ntt := MLDSA.ntt
  inverseNtt := ocamlInverseNtt
  matrixVectorNtt := ocamlMatVec P.l
  pointwise := MLDSA.pointwise
  subMod := MLDSA.subMod
  useHint := MLDSA.useHint P.gamma2
  packW1 := ocamlPackW1 P.gamma2

/-- **The FIPS 204 building blocks of Algorithm 8** (`VerifyFips`). -/
def verifyFips (P : Params) : VerifyFips where
  pkDecode := fipsPkDecode P
  sigDecode := fipsSigDecode P
  zNormOk := fipsZNormOk P
  NTT := fipsNTT
  NTTinv := fipsNTTinv
  mulMatVec := fipsMulMatVec P.l
  mulNTT := fipsMulNTT
  subPoly := fipsSubPoly
  useHint := MLDSA.useHintSpec P.gamma2
  simpleBitPack := fipsSimpleBitPack

/-- `verifyOps` with `use_hint` and `pack_w1` replaced by FIPS's (used only in
    proofs). -/
def verifyOpsIdeal (P : Params) : VerifyOps where
  decodeVerificationKey := ocamlDecodeVk P
  decodeSignature := ocamlDecodeSig P
  normViolation := ocamlZNormViolation P
  ntt := MLDSA.ntt
  inverseNtt := ocamlInverseNtt
  matrixVectorNtt := ocamlMatVec P.l
  pointwise := MLDSA.pointwise
  subMod := MLDSA.subMod
  useHint := fun r h => MLDSA.useHintSpec P.gamma2 h r
  packW1 := fun p => fipsSimpleBitPack p ((q - 1) / (2 * P.gamma2) - 1)

/-- **The `useHint` field of `VerifyOps.Refines` is false for the concrete
    models**: with hint value 2 at `r = 1` the code adjusts the high part
    (it tests `hint = 0`), FIPS 204's `UseHint` does not (it tests `h = 1`).
    Decoded hints are always 0 or 1, so this never matters in `verify`. -/
theorem verifyOps_useHint_ne {P : Params} (hP : P.Valid) :
    (verifyOps P).useHint 1 2 ≠ (verifyFips P).useHint 2 1 := by
  simp only [verifyOps, verifyFips]
  rcases hP with rfl | rfl | rfl <;> decide

/-- **`verifyOpsIdeal P` refines `verifyFips P`** (every field of
    `VerifyOps.Refines`). -/
theorem verifyOpsIdeal_refines {P : Params} (hP : P.Valid) :
    (verifyOpsIdeal P).Refines (verifyFips P) P where
  decodeVerificationKey := fun pk => by
    simp only [verifyOpsIdeal, verifyFips]; exact decodeVk_eq_fips hP pk
  decodeSignature := fun sig => by
    simp only [verifyOpsIdeal, verifyFips]; exact decodeSig_eq_fips hP sig
  normViolation := fun z => by
    simp only [verifyOpsIdeal, verifyFips]; exact zNorm_eq_fips P z
  ntt := by simp only [verifyOpsIdeal, verifyFips]; exact ntt_eq_fips
  inverseNtt := by simp only [verifyOpsIdeal, verifyFips]; exact inverseNtt_eq_fips
  matrixVectorNtt := by simp only [verifyOpsIdeal, verifyFips]; exact matVec_eq_fips P.l
  pointwise := by simp only [verifyOpsIdeal, verifyFips]; exact pointwise_eq_fips
  subMod := fun a b => by simp only [verifyOpsIdeal, verifyFips]; exact subMod_eq_fips a b
  useHint := fun r h => by simp only [verifyOpsIdeal, verifyFips]
  packW1 := fun p => by simp only [verifyOpsIdeal, verifyFips]
  mulMatVec_local := fun A A' v hA r hr => by
    simp only [verifyFips]
    exact fipsMulMatVec_local P.l A A' v v r (hA r hr) (fun _ _ => rfl)

/-! ## The OCaml verifier versus the ideal one -/

/-- `UseHint` outputs lie in `[0, (q − 1)/(2γ2))`. -/
theorem useHintSpec_range {P : Params} (hP : P.Valid) (h r : ℤ) :
    0 ≤ MLDSA.useHintSpec P.gamma2 h r ∧ MLDSA.useHintSpec P.gamma2 h r < (w1Count P : ℤ) := by
  have hf := e2eFacts hP
  have hd := MLDSA.decomposeSpec_range hf.gamma2Ok r
  have hm : (0 : ℤ) < (w1Count P : ℤ) := by exact_mod_cast hf.w1Count_pos
  have hmi := hf.w1Count_int
  unfold w1Count at hm
  unfold MLDSA.useHintSpec w1Count
  rw [hmi] at hm ⊢
  dsimp only
  split_ifs
  · exact ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩
  · exact ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩
  · exact ⟨hd.1, hd.2.1⟩

/-- **`verify_mu` with the OCaml bundle equals it with the ideal bundle.** -/
theorem verifyMu_ideal {P : Params} (hP : P.Valid) (H : XOF) (expandMatrix : Bytes → PolyMat)
    (challenge : Bytes → Poly) (pk mu sig : Bytes) :
    verifyMu (verifyOps P) P H expandMatrix challenge pk mu sig =
      verifyMu (verifyOpsIdeal P) P H expandMatrix challenge pk mu sig := by
  have hf := e2eFacts hP
  unfold verifyMu
  simp only [verifyOps, verifyOpsIdeal]
  split_ifs
  · rfl
  cases hd : ocamlDecodeSig P sig with
  | none => cases ocamlDecodeVk P pk <;> rfl
  | some x =>
    obtain ⟨ct, z, h⟩ := x
    have h01 : ∀ r c, h r c = 0 ∨ h r c = 1 := by
      rw [decodeSig_eq_fips hP] at hd
      split_ifs at hd
      exact fipsSigDecode_hint01 hd
    cases ocamlDecodeVk P pk with
    | none => rfl
    | some y =>
      obtain ⟨rho, t1⟩ := y
      simp only
      by_cases hz : ocamlZNormViolation P z = true
      · simp only [hz, ite_true]
      · simp only [hz, Bool.false_eq_true, ite_false]
        simp only [MLDSA.useHint_eq_spec hf.gamma2Ok _ _ (h01 _ _)]
        rw [concatMap_packW1_eq_fips hP _ (fun r _ i _ => useHintSpec_range hP _ _)]

/-! ## `MLDSAAlg.verify_eq` with pointwise hypotheses -/

/-- `MLDSAAlg.verify_eq` with the matrix hypothesis only at the decoded `ρ`
    and the challenge hypothesis only at the decoded `c̃`, both in value form.
    (Same proof.) -/
theorem verify_eq_at (E : VerifyOps) (F : VerifyFips) {P : Params}
    (hR : E.Refines F P) {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam) (H G : XOF)
    (expandMatrix : Bytes → PolyMat) (challenge : Bytes → Poly)
    (pk : Bytes) (hpk : pk.length = P.verificationKeySize) (context message sig : Bytes)
    (hsig : sig.length = P.signatureSize)
    (hA' : ∀ r < P.k, ∀ s < P.l,
      expandMatrix (F.pkDecode pk).1 r s = expandA G (F.pkDecode pk).1 r s)
    (hc : ∀ ct z h, F.sigDecode sig = some (ct, z, h) → challenge ct = sampleInBall P.tau (H ct)) :
    (∀ M', verifyFormatted E P H expandMatrix challenge pk M' sig =
      verifyInternal F P lam H G pk M' sig) ∧
    verify E P H expandMatrix challenge context pk message sig =
      mldsaVerify F P lam H G pk message sig context := by
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
        cases hz : F.zNormOk z
        · simp
        · simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.true_and, hdec, hlam4]
          rw [hc cTilde z h hsd]
          have hB : concatMap P.k E.packW1 (fun row index =>
                E.useHint (E.inverseNtt (fun index =>
                  E.subMod (E.matrixVectorNtt (expandMatrix rho) (fun i => E.ntt (z i)) row index)
                    (E.pointwise (E.ntt (sampleInBall P.tau (H cTilde)))
                      (E.ntt fun index => t1 row index * 2 ^ d) index)) index) (h row index)) =
              (List.range P.k).foldl (fun acc i => acc ++ F.simpleBitPack
                (fun i_1 => F.useHint (h i i_1) (F.NTTinv (F.subPoly
                  (F.mulMatVec (expandA G rho) (fun i => F.NTT (z i)) i)
                  (F.mulNTT (F.NTT (sampleInBall P.tau (H cTilde)))
                    (F.NTT fun i_2 => t1 i i_2 * 2 ^ d))) i_1))
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
                  (E.pointwise (E.ntt (sampleInBall P.tau (H cTilde)))
                    (E.ntt fun index => t1 row index * 2 ^ d) index)) =
                F.subPoly (E.matrixVectorNtt (expandMatrix rho) (fun i => E.ntt (z i)) row)
                  (E.pointwise (E.ntt (sampleInBall P.tau (H cTilde)))
                    (E.ntt fun index => t1 row index * 2 ^ d))
                from hR.subMod _ _]
            rw [hR.inverseNtt, hR.matrixVectorNtt, hR.ntt, hR.pointwise,
              hR.mulMatVec_local _ _ _ hA' row hrow']
          rw [hB]
  refine ⟨hvf, ?_⟩
  unfold verify mldsaVerify
  split_ifs with h
  · rfl
  · rw [hvf, formattedPrefix_eq (by omega)]

/-! ## End to end -/

/-- **Verification, end to end (FIPS 204 Algorithms 8 and 3).** For a valid
    parameter set, a verification key `pk` and a signature `σ`:
    * if either has the wrong length, the OCaml `verify` returns `false`
      (FIPS 204 defines Algorithm 8 only on the right lengths);
    * otherwise, if the OCaml calls `expand_matrix ρ` (ρ = `pk[0:32]`) and
      `challenge_polynomial c̃ 136` (c̃ = `σ[0:λ/4]`) return `A` and `c`,
      `verify_formatted pk M′ σ` is `ML-DSA.Verify_internal(pk, M′, σ)` for
      every `M′` and `verify ~context pk ~message σ` is
      `ML-DSA.Verify(pk, M, σ, ctx)` (FIPS 202 SHAKE on the FIPS side). -/
theorem verify_e2e {P : Params} (hP : P.Valid) {lam : ℕ} (hlam : P.cTildeBytes * 4 = lam)
    (pk sig context message : Bytes) (A : PolyMat) (c : Poly) :
    ((pk.length ≠ P.verificationKeySize ∨ sig.length ≠ P.signatureSize) →
      ∀ M', verifyFormatted (verifyOps P) P ocamlShake256 (fun _ => A) (fun _ => c) pk M' sig =
        false) ∧
    (pk.length = P.verificationKeySize → sig.length = P.signatureSize →
      ExpandMatrixReturns ocamlShake128 P (pk.take 32) A →
      ChallengeReturns P.tau ocamlShake256 (sig.take P.cTildeBytes) 136 c →
      (∀ M', verifyFormatted (verifyOps P) P ocamlShake256 (fun _ => A) (fun _ => c) pk M' sig =
        verifyInternal (verifyFips P) P lam fipsShake256 fipsShake128 pk M' sig) ∧
      verify (verifyOps P) P ocamlShake256 (fun _ => A) (fun _ => c) context pk message sig =
        mldsaVerify (verifyFips P) P lam fipsShake256 fipsShake128 pk message sig context) := by
  have hf := e2eFacts hP
  have hvf : ∀ M', verifyFormatted (verifyOps P) P ocamlShake256 (fun _ => A) (fun _ => c) pk M'
      sig = verifyFormatted (verifyOpsIdeal P) P ocamlShake256 (fun _ => A) (fun _ => c) pk M' sig :=
    fun M' => by unfold verifyFormatted; exact verifyMu_ideal hP _ _ _ _ _ _
  refine ⟨fun hlen M' => ?_, fun hpk hsig hA hc => ?_⟩
  · rw [hvf]
    exact verify_wrong_length _ _ (verifyOpsIdeal_refines hP) _ _ _ pk M' sig hlen
  · have hv : verify (verifyOps P) P ocamlShake256 (fun _ => A) (fun _ => c) context pk message sig =
        verify (verifyOpsIdeal P) P ocamlShake256 (fun _ => A) (fun _ => c) context pk message sig := by
      unfold verify; split_ifs
      · rfl
      · exact hvf _
    rw [hv, fipsShake128_eq, fipsShake256_eq]
    simp only [hvf]
    refine verify_eq_at _ _ (verifyOpsIdeal_refines hP) hlam _ _ _ _ pk hpk context message sig
      hsig ((expandMatrix_spec _ hP _).1 A hA) ?_
    intro ct z h hd
    have hct := fipsSigDecode_cTilde hd
    subst hct
    exact challenge_returns_eq (by have := hf.tau_le; omega) hc

end OcamlPq.EndToEnd.MLDSA
