import OcamlPq.EndToEnd.MLDSA.Algebra

/-!
# Sign/verify consistency for the OCaml models

`signMu_verifyMu`: for a key produced by `keypair_from_seed` (secrets in
`[−η, η]`), every signature `sign_mu_with_randomness` returns is accepted by
`verify_mu` on the key's verification key and the same `μ`, provided the
signer's and verifier's `expand_matrix ρ` return the same matrix (it is a
function of `ρ`) and `challenge_polynomial` returns FIPS 204's `SampleInBall`.
Composed with the end-to-end theorems this is FIPS 204's correctness
(`ML-DSA.Verify` accepts `ML-DSA.Sign`), now proved for the code.

Ingredients: the Encoding area's round trips (`decodeVk_encodeVk`,
`decodeSig_encodeSig`), the arithmetic area's `verify_recovers_w1_of_accepted`
and `verify_z_check_of_accepted`, whose algebraic hypothesis
`w′_approx ≡ w − cs2 + ct0` is `verifier_approx`, and `center_cs` for
`‖cs2‖∞ ≤ β`.
-/

namespace OcamlPq.EndToEnd.MLDSA

open OcamlPq.MLDSAAlg

/-! ## Byte-level round trips -/

theorem packT1_bytes_lt (p : Poly) (h : ∀ i < 256, 0 ≤ p i ∧ p i < 2 ^ 10) :
    ∀ x ∈ Encoding.Mldsa.packT1 (polyToNatList p), x < 256 := by
  have hc : ∀ v ∈ polyToNatList p, v < 2 ^ 10 := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := mem_polyToNatList.mp hv
    have := h i hi; omega
  exact (Encoding.Packer.packCodes_regroup hc (by simp)).right_lt

theorem bytesToNat_encodeVerificationKey (P : Params) (rho : Bytes) (t1 : PolyVec)
    (ht : ∀ r < P.k, ∀ i < 256, 0 ≤ t1 r i ∧ t1 r i < 2 ^ 10) :
    bytesToNat (encodeVerificationKey (keyOps P) P rho t1) =
      Encoding.Mldsa.encodeVk (bytesToNat rho) ((List.range P.k).map fun r => polyToNatList (t1 r)) := by
  unfold encodeVerificationKey concatMap Encoding.Mldsa.encodeVk
  simp only [keyOps, ocamlPackT1, bytesToNat_append, List.map_map]
  congr 1
  simp only [bytesToNat, List.map_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r hr
  simp only [Function.comp, natToBytes, List.map_map]
  conv_rhs => rw [← List.map_id (Encoding.Mldsa.packT1 _)]
  apply List.map_congr_left
  intro x hx
  exact byteOfNat_val_of_lt (packT1_bytes_lt _ (ht r (List.mem_range.mp hr)) x hx)

/-- **`decode_verification_key (encode_verification_key ρ t1)`** returns `ρ`
    and `t1` (on the `k × 256` entries), for `t1 ∈ [0, 2^10)`. -/
theorem ocamlDecodeVk_encode (P : Params) (rho : Bytes) (hrho : rho.length = 32)
    (t1 : PolyVec) (ht : ∀ r < P.k, ∀ i < 256, 0 ≤ t1 r i ∧ t1 r i < 2 ^ 10) :
    ∃ t1D : PolyVec, ocamlDecodeVk P (encodeVerificationKey (keyOps P) P rho t1) = some (rho, t1D) ∧
      ∀ r < P.k, ∀ i < 256, t1D r i = t1 r i := by
  refine ⟨fun r => natListToPoly
    (((List.range P.k).map fun r => polyToNatList (t1 r)).getD r []), ?_, ?_⟩
  · unfold ocamlDecodeVk
    rw [bytesToNat_encodeVerificationKey P rho t1 ht,
      Encoding.Mldsa.decodeVk_encodeVk (encParams P) _ _ (by simpa using hrho) (by simp [encParams])]
    · simp only [Option.map_some, natToBytes_bytesToNat]
    · intro p hp
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
      refine ⟨by simp, fun x hx => ?_⟩
      obtain ⟨i, hi, rfl⟩ := mem_polyToNatList.mp hx
      have := ht r (List.mem_range.mp hr) i hi; omega
  · intro r hr i hi
    have e1 : ((List.range P.k).map fun r => polyToNatList (t1 r)).getD r [] =
        polyToNatList (t1 r) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hr)]; simp
    have e2 : (polyToNatList (t1 r)).getD i 0 = (t1 r i).toNat := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp [polyToNatList]
    simp only [natListToPoly, e1, e2]
    have := ht r hr i hi
    omega

/-- Every byte `encode_signature` writes is below 256. -/
theorem encodeSig_bytes_lt {P : Params} (hP : P.Valid) (ct : List ℕ) (zL : List (List ℤ))
    (hv : Encoding.Hint.HintVec) (hin : Encoding.Mldsa.SigInput (encParams P) ct zL hv) :
    ∀ x ∈ Encoding.Mldsa.encodeSig (encParams P) ct zL hv, x < 256 := by
  have hf := e2eFacts hP
  rw [Encoding.Mldsa.encodeSig_eq _ _ _ _ hin, Encoding.Hint.hintBitPack_eq _ _ _ hin.weight]
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with (hx | hx) | ((hx | hx) | hx)
  · exact hin.cTilde_lt x hx
  · obtain ⟨b, hb, hx⟩ := List.mem_flatten.mp hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact Encoding.Mldsa.packZ_lt _ hf.encValid p (hin.z_poly p hp).1 (hin.z_poly p hp).2 x hx
  · unfold Encoding.Hint.allList at hx
    obtain ⟨r, -, hr⟩ := List.mem_flatMap.mp hx
    exact ((Encoding.Hint.mem_rowList _ _ _).mp hr).1
  · rw [List.eq_of_mem_replicate hx]; norm_num
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have h1 := Encoding.Hint.allList_length_mono hv (show i + 1 ≤ (encParams P).k by
      simp only [List.mem_range] at hi; omega)
    have h2 := hin.weight
    have h3 : (encParams P).omega ≤ 80 := by
      rcases hP with rfl | rfl | rfl <;> decide
    unfold Encoding.Hint.weight at h2
    omega

/-- **`decode_signature (encode_signature c̃ z h)`** returns `(c̃, z, h)` (on
    the `ℓ × 256` / `k × 256` entries) for `|c̃| = λ/4`, `z ∈ (−γ1, γ1]` and
    a hint of weight at most `ω`. -/
theorem ocamlDecodeSig_encode {P : Params} (hP : P.Valid) (ct : Bytes)
    (hct : ct.length = P.cTildeBytes) (z h : PolyVec)
    (hz : ∀ r < P.l, ∀ i < 256, -(P.gamma1 : ℤ) < z r i ∧ z r i ≤ P.gamma1)
    (hw : Encoding.Hint.weight P.k (hintToVec P.k h) ≤ P.omega) :
    ocamlDecodeSig P (ocamlEncodeSig P ct z h) =
      some (ct, listsToVec (vecToLists P.l z), hintToPoly (hintToVec P.k h)) := by
  have hf := e2eFacts hP
  have hin : Encoding.Mldsa.SigInput (encParams P) (bytesToNat ct) (vecToLists P.l z)
      (hintToVec P.k h) := by
    refine ⟨by simpa [encParams] using hct, bytesToNat_lt ct, by simp [encParams], ?_, ?_, ?_, hw⟩
    · intro p hp
      obtain ⟨r, hr, rfl⟩ := mem_vecToLists.mp hp
      refine ⟨by simp, fun v hv => ?_⟩
      obtain ⟨i, hi, rfl⟩ := mem_polyToList.mp hv
      exact hz r hr i hi
    · intro r c; unfold hintToVec; split_ifs <;> simp
    · intro r c hrc; unfold hintToVec; rw [ite_eq_right]; intro h'
      simp only [encParams] at hrc; omega
  unfold ocamlDecodeSig ocamlEncodeSig
  rw [bytesToNat_natToBytes (encodeSig_bytes_lt hP _ _ _ hin),
    Encoding.Mldsa.decodeSig_encodeSig _ hf.encValid _ _ _ hin]
  simp only [Option.map_some, natToBytes_bytesToNat]

/-! ## One accepted candidate -/

/-- The signer's `cs1`, `cs2`, `ct0` of the OCaml candidate. -/
abbrev csOf (c : Poly) (s : PolyVec) : PolyVec :=
  fun r => ocamlCenteredProduct (MLDSA.ntt c) (MLDSA.ntt (s r))

/-- An accepted OCaml candidate: `signAttempt` accepted `z = y + cs1` with the
    `(w, cs2, ct0)` rows, and returned `z` and the hint list `hL`. -/
theorem ocamlCandidate_accept (P : Params) (key : ExpandedKey) (y w : PolyVec) (c : Poly)
    (zV hV : PolyVec)
    (h : ocamlCandidate P key y (fun r i => (MLDSA.decompose P.gamma2 (w r i)).2)
      (fun r i => (MLDSA.decompose P.gamma2 (w r i)).1) (MLDSA.ntt c) = some (zV, hV)) :
    ∃ hL, MLDSA.signAttempt P.gamma1 P.gamma2 P.beta P.omega
        (mkRows P.l fun r i => y r i + csOf c key.s1 r i)
        (mkRows P.k fun r i => (w r i, csOf c key.s2 r i, csOf c key.t0 r i)) =
      some (mkRows P.l (fun r i => y r i + csOf c key.s1 r i), hL) ∧
      zV = listsToVec (mkRows P.l fun r i => y r i + csOf c key.s1 r i) ∧ hV = listsToVec hL := by
  unfold ocamlCandidate at h
  simp only at h
  rw [codeTail_eq_signAttempt] at h
  obtain ⟨zh, hs, he⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨zs, hL⟩ := zh
  have := (MLDSA.verify_z_check_of_accepted (γ2 := (P.gamma2 : ℤ)) (β := (P.beta : ℤ)) _ _ _ _ hs).1
  subst this
  simp only [Prod.mk.injEq] at he
  exact ⟨hL, hs, he.1.symm, he.2.symm⟩

/-- What acceptance by the code's `signAttempt` gives: the returned `z` is
    the input, the hints are the code's, `‖z‖∞ < γ1 − β`, and the hint count
    is at most `ω`. -/
theorem signAttempt_accepted {γ1 γ2 β ω : ℤ} {z : List (List ℤ)} {rows : List (List MLDSA.WCoeff)}
    {zs hs : List (List ℤ)} (h : MLDSA.signAttempt γ1 γ2 β ω z rows = some (zs, hs)) :
    zs = z ∧ hs = rows.map (List.map (MLDSA.codeHint γ2)) ∧ ¬ MLDSA.infNormGe z (γ1 - β) ∧
      (hs.map List.sum).sum ≤ ω := by
  unfold MLDSA.signAttempt at h
  simp only [MLDSA.vectorNormViolationFlag_eq, MLDSA.foldl_add_eq_sum, MLDSA.ite_or_ite,
    MLDSA.ite_one_zero_ne_zero] at h
  split_ifs at h with hrej
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [not_or] at hrej
  exact ⟨rfl, rfl, hrej.1.1.1, le_of_not_gt hrej.2⟩

theorem mkRows_eq_apply {k : ℕ} {f g : ℕ → ℕ → ℤ} (h : mkRows k f = mkRows k g) (r i : ℕ)
    (hr : r < k) (hi : i < 256) : f r i = g r i := by
  have := congrArg (fun L => listsToVec L r i) h
  simp only [listsToVec_mkRows _ _ r i hr hi] at this
  exact this

/-- **One accepted iteration verifies.** If an iteration of the OCaml signer
    (key `key` with secrets in `[−η, η]`, mask `y ∈ (−γ1, γ1]`) returns `σ`,
    and the verification key decodes to a `t1` with `t1·2^13 + t0 ≡ t =
    inverse_ntt (Â·ntt s1) + s2`, then `verify_mu` accepts `σ` (same `Â`, same
    challenge function). -/
theorem iteration_verifies {P : Params} (hP : P.Valid) (H : XOF) (A : PolyMat) (key : ExpandedKey)
    (hkey : SecretsInRange P key) (vk rho : Bytes) (t1D : PolyVec)
    (hvk : ocamlDecodeVk P vk = some (rho, t1D))
    (ht : ∀ r < P.k, ∀ i < 256, (t1D r i * 2 ^ 13 + key.t0 r i) % MLDSA.q =
      MLDSA.addMod (ocamlInverseNtt (ocamlMatVec P.l A (fun j => MLDSA.ntt (key.s1 j)) r) i)
        (key.s2 r i) % MLDSA.q)
    (challenge : Bytes → Poly) (hc : ∀ ct, challenge ct = sampleInBall P.tau (H ct))
    (mu : Bytes) (hmu : mu.length = 64) (y : PolyVec)
    (hy : ∀ r < P.l, ∀ i < 256, -(P.gamma1 : ℤ) < y r i ∧ y r i ≤ P.gamma1)
    (sig : Bytes) (hsig : signIter (signOps P key) P H A challenge mu y = some sig) :
    verifyMu (verifyOps P) P H (fun _ => A) challenge vk mu sig = true := by
  have hf := e2eFacts hP
  have hpo : MLDSA.ParamOk (P.gamma2 : ℤ) (P.beta : ℤ) := by
    have := hf.paramOk; unfold Params.beta; exact_mod_cast this
  unfold signIter at hsig
  simp only [signOps] at hsig
  split at hsig
  swap
  · cases hsig
  rename_i zh hcand
  obtain ⟨zV, hV⟩ := zh
  simp only [Option.some.injEq] at hsig
  subst hsig
  -- the signer's quantities
  obtain ⟨hL, hacc, hzV, hhV⟩ := ocamlCandidate_accept P key y
    (fun row => ocamlInverseNtt (ocamlMatVec P.l A (fun i => MLDSA.ntt (y i)) row)) _ zV hV hcand
  generalize hct : H.squeeze (mu ++ concatMap P.k (ocamlPackW1 P.gamma2) fun row index =>
    (MLDSA.decompose P.gamma2 (ocamlInverseNtt (ocamlMatVec P.l A (fun i => MLDSA.ntt (y i)) row)
      index)).1) P.cTildeBytes = ct at hacc hzV hhV ⊢
  obtain ⟨-, hL_eq, hznorm, hcount⟩ := signAttempt_accepted hacc
  -- the challenge has FIPS shape, so `‖c·s‖∞ ≤ β`
  have hball := sampleInBall_ball (tau := P.tau) (by have := hf.tau_le; omega) (H ct)
  have hsmall : (P.tau : ℤ) * P.eta ≤ 4190208 := by
    rcases hf.tauEta with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> norm_num
  have hcs : ∀ (s : Poly), (∀ j < 256, -(P.eta : ℤ) ≤ s j ∧ s j ≤ P.eta) → ∀ i < 256,
      |ocamlCenteredProduct (MLDSA.ntt (challenge ct)) (MLDSA.ntt s) i| ≤ (P.beta : ℤ) := by
    intro s hs i hi
    rw [hc]
    have := (MLDSA.center_cs _ s P.tau P.eta hball.1 hball.2
      (fun j hj => abs_le.mpr (hs j hj)) hsmall i hi).2
    unfold ocamlCenteredProduct; unfold Params.beta; push_cast; exact this
  -- `z` is in `(−γ1, γ1]`
  have hz : ∀ r < P.l, ∀ i < 256, -(P.gamma1 : ℤ) < zV r i ∧ zV r i ≤ P.gamma1 := by
    intro r hr i hi
    rw [hzV, listsToVec_mkRows _ _ r i hr hi]
    have h1 := hcs (key.s1 r) (hkey.1 r hr) i hi
    have h2 := hy r hr i hi
    have hn : ¬ MLDSA.coeffNorm (y r i + csOf (challenge ct) key.s1 r i) ≥ P.gamma1 - P.beta :=
      fun h' => hznorm ((infNormGe_mkRows _ _ _).mpr ⟨r, hr, i, hi, h'⟩)
    have hb : (P.beta : ℤ) ≤ 196 := by unfold Params.beta; exact_mod_cast hf.beta_small
    have hg : (P.gamma1 : ℤ) ≤ 2 ^ 19 := by rcases hf.gamma1 with h | h <;> rw [h] <;> norm_num
    rw [abs_le] at h1
    rw [MLDSA.coeffNorm_eq, MLDSA.center_of_small (by simp only [csOf] at *; omega)
      (by simp only [csOf] at *; omega)] at hn
    have hlt := lt_of_not_ge hn
    rw [abs_lt] at hlt
    have hb0 : (0 : ℤ) ≤ P.beta := by positivity
    constructor <;> linarith [hlt.1, hlt.2]
  -- the hints: the code's, 0/1, weight = count ≤ ω
  have hLm : hL = mkRows P.k fun r i => MLDSA.codeHint P.gamma2
      (ocamlInverseNtt (ocamlMatVec P.l A (fun i => MLDSA.ntt (y i)) r) i,
        csOf (challenge ct) key.s2 r i, csOf (challenge ct) key.t0 r i) := by
    rw [hL_eq, mkRows_map]
  have hV01 : ∀ r < P.k, ∀ i < 256, hV r i = 0 ∨ hV r i = 1 := by
    intro r hr i hi
    rw [hhV, hLm, listsToVec_mkRows _ _ r i hr hi]
    exact MLDSA.codeHint_zero_or_one _ _
  have hw : Encoding.Hint.weight P.k (hintToVec P.k hV) ≤ P.omega := by
    have h1 := weight_hintToVec P.k hV hV01
    rw [hhV, hLm, ← sum_mkRows, ← hLm] at h1
    rw [hhV]
    exact_mod_cast h1.trans_le hcount
  -- the verifier decodes the signature
  have hdec := ocamlDecodeSig_encode hP ct (by rw [← hct]; simp) zV hV hz hw
  have hzD : ∀ s < P.l, ∀ i < 256, listsToVec (vecToLists P.l zV) s i =
      y s i + ocamlCenteredProduct (MLDSA.ntt (challenge ct)) (MLDSA.ntt (key.s1 s)) i := by
    intro s hs i hi
    rw [vecToLists_eq_mkRows, listsToVec_mkRows _ _ s i hs hi, hzV, listsToVec_mkRows _ _ s i hs hi]
  have hD : ∀ r < P.k, ∀ i < 256, hintToPoly (hintToVec P.k hV) r i = MLDSA.codeHint P.gamma2
      (ocamlInverseNtt (ocamlMatVec P.l A (fun i => MLDSA.ntt (y i)) r) i,
        csOf (challenge ct) key.s2 r i, csOf (challenge ct) key.t0 r i) := by
    intro r hr i hi
    have e : hV r i = MLDSA.codeHint P.gamma2
        (ocamlInverseNtt (ocamlMatVec P.l A (fun i => MLDSA.ntt (y i)) r) i,
          csOf (challenge ct) key.s2 r i, csOf (challenge ct) key.t0 r i) := by
      rw [hhV, hLm, listsToVec_mkRows _ _ r i hr hi]
    rw [← e]
    unfold hintToPoly hintToVec
    rcases hV01 r hr i hi with h0 | h1
    · rw [ite_eq_right (by simp [h0])]; simp [h0]
    · rw [ite_eq_left (by simp [hr, hi, h1])]; simp [h1]
  -- the verifier's `w′_approx` and the recovered `w1`
  have hrec : ∀ r < P.k, ∀ i < 256,
      MLDSA.useHint P.gamma2 (ocamlInverseNtt (fun idx => MLDSA.subMod
        (ocamlMatVec P.l A (fun j => MLDSA.ntt (listsToVec (vecToLists P.l zV) j)) r idx)
        (MLDSA.pointwise (MLDSA.ntt (challenge ct)) (MLDSA.ntt (fun i => t1D r i * 2 ^ 13)) idx)) i)
        (hintToPoly (hintToVec P.k hV) r i) =
      (MLDSA.decompose P.gamma2 (ocamlInverseNtt (ocamlMatVec P.l A (fun i => MLDSA.ntt (y i)) r)
        i)).1 := by
    have hr := (MLDSA.verify_recovers_w1_of_accepted hpo
      (mkRows P.l fun r i => y r i + csOf (challenge ct) key.s1 r i)
      (mkRows P.k fun r i =>
        ((ocamlInverseNtt (ocamlMatVec P.l A (fun i => MLDSA.ntt (y i)) r) i,
          csOf (challenge ct) key.s2 r i, csOf (challenge ct) key.t0 r i),
          ocamlInverseNtt (fun idx => MLDSA.subMod
            (ocamlMatVec P.l A (fun j => MLDSA.ntt (listsToVec (vecToLists P.l zV) j)) r idx)
            (MLDSA.pointwise (MLDSA.ntt (challenge ct))
              (MLDSA.ntt (fun i => t1D r i * 2 ^ 13)) idx)) i))
      _ hL (by rw [mkRows_map]; exact hacc) ?_ ?_).2
    · rw [mkRows_map, mkRows_map] at hr
      intro r hr' i hi
      rw [hD r hr' i hi]
      exact mkRows_eq_apply hr r i hr' hi
    · intro row hrow e he
      obtain ⟨r, hr', rfl⟩ := mem_mkRows.mp hrow
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
      rw [List.mem_range] at hi
      simp only [csOf, ocamlCenteredProduct, MLDSA.center_center]
      exact hcs (key.s2 r) (hkey.2 r hr') i hi
    · intro row hrow e he
      obtain ⟨r, hr', rfl⟩ := mem_mkRows.mp hrow
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
      rw [List.mem_range] at hi
      exact verifier_approx P.l A r key.s1 y _ (key.s2 r) (key.t0 r) (t1D r) (challenge ct)
        hzD (ht r hr') i hi
  -- verification
  unfold verifyMu
  simp only [verifyOps]
  rw [ite_eq_right (by simp [hmu]), hvk, hdec]
  simp only
  have hnv : ocamlZNormViolation P (listsToVec (vecToLists P.l zV)) = false := by
    unfold ocamlZNormViolation
    rw [vecToLists_listsToVec (by simp) (fun p hp => by
      obtain ⟨r, _, rfl⟩ := mem_vecToLists.mp hp; simp), hzV, vecToLists_eq_mkRows,
      mkRows_congr (f' := fun r i => y r i + csOf (challenge ct) key.s1 r i)
        (fun r hr i hi => listsToVec_mkRows _ _ r i hr hi), MLDSA.vectorNormViolationFlag_eq]
    rw [ite_eq_right (by unfold Params.beta at hznorm; exact_mod_cast hznorm)]
    decide
  simp only [hnv, Bool.false_eq_true, ite_false]
  rw [show (2 : ℤ) ^ d = 2 ^ 13 from rfl]
  have hsame : concatMap P.k (ocamlPackW1 P.gamma2) (fun row index =>
      MLDSA.useHint P.gamma2 (ocamlInverseNtt (fun idx => MLDSA.subMod
        (ocamlMatVec P.l A (fun j => MLDSA.ntt (listsToVec (vecToLists P.l zV) j)) row idx)
        (MLDSA.pointwise (MLDSA.ntt (challenge ct)) (MLDSA.ntt (fun i => t1D row i * 2 ^ 13)) idx))
          index) (hintToPoly (hintToVec P.k hV) row index)) =
      concatMap P.k (ocamlPackW1 P.gamma2) (fun row index =>
        (MLDSA.decompose P.gamma2 (ocamlInverseNtt (ocamlMatVec P.l A (fun i => MLDSA.ntt (y i)) row)
          index)).1) := by
    unfold concatMap
    apply congrArg
    apply List.map_congr_left
    intro r hr
    unfold ocamlPackW1
    rw [polyToNatList_congr (fun i hi => hrec r (List.mem_range.mp hr) i hi)]
  rw [hsame, hct]
  exact (equalString_iff ct ct).mpr rfl

/-! ## Sign then verify -/

/-- **Sign/verify consistency for the OCaml models.** For every seed `ξ`,
    matrix `A`, secrets `s1, s2 ∈ [−η, η]` (the values `expand_matrix`,
    `expand_secret` return in `keypair_from_seed ξ`), challenge values of
    FIPS shape, and every `μ`, `rnd`: if `sign_mu_with_randomness` on the
    generated key returns `Ok σ`, then `verify_mu` on the generated
    verification key accepts `σ` for the same `μ` (with the same `A` from
    `expand_matrix ρ`). -/
theorem signMu_verifyMu {P : Params} (hP : P.Valid) (H : XOF) (xi : Bytes) (A : PolyMat)
    (s1 s2 : PolyVec)
    (hs1 : ∀ r < P.l, ∀ i < 256, -(P.eta : ℤ) ≤ s1 r i ∧ s1 r i ≤ P.eta)
    (hs2 : ∀ r < P.k, ∀ i < 256, -(P.eta : ℤ) ≤ s2 r i ∧ s2 r i ≤ P.eta)
    (challenge : Bytes → Poly) (hc : ∀ ct, challenge ct = sampleInBall P.tau (H ct))
    (mu rnd sig : Bytes)
    (hsign : signMuWithRandomness
      (signOps P (keypairFromSeed (keyOps P) P H (fun _ => A) (fun _ => (s1, s2)) xi).expanded)
      P H A challenge (keypairFromSeed (keyOps P) P H (fun _ => A) (fun _ => (s1, s2)) xi).expanded
      mu rnd = .ok sig) :
    verifyMu (verifyOps P) P H (fun _ => A) challenge
      (keypairFromSeed (keyOps P) P H (fun _ => A) (fun _ => (s1, s2)) xi).verificationKey mu sig =
        true := by
  have hf := e2eFacts hP
  set sk := keypairFromSeed (keyOps P) P H (fun _ => A) (fun _ => (s1, s2)) xi with hsk
  have hmu : mu.length = 64 := by
    by_contra h
    unfold signMuWithRandomness at hsign
    rw [ite_eq_left h] at hsign
    cases hsign
  have hrnd : rnd.length = 32 := by
    by_contra h
    unfold signMuWithRandomness at hsign
    rw [ite_eq_right (by simp [hmu]), ite_eq_left h] at hsign
    cases hsign
  unfold signMuWithRandomness at hsign
  rw [ite_eq_right (by simp [hmu]), ite_eq_right (by simp [hrnd])] at hsign
  obtain ⟨i, -, hiter, -⟩ := (attempt_ok_iff _ _ _ _).mp hsign
  -- the key's parts
  have hs1' : sk.expanded.s1 = s1 := rfl
  have hs2' : sk.expanded.s2 = s2 := rfl
  have hvk_def : sk.verificationKey = encodeVerificationKey (keyOps P) P sk.expanded.rho
      (computePublicParts (keyOps P) A sk.expanded).1 := rfl
  have ht0_def : sk.expanded.t0 = (computePublicParts (keyOps P) A sk.expanded).2 := rfl
  have hrho : sk.expanded.rho.length = 32 := by
    show (sub _ 0 32).length = 32
    rw [length_sub (by simp)]
  have hrange := computePublicParts_range (keyOps P) rfl A sk.expanded
  obtain ⟨t1D, hvk, ht1D⟩ := ocamlDecodeVk_encode P sk.expanded.rho hrho
    (computePublicParts (keyOps P) A sk.expanded).1 (fun r _ i _ => (hrange r i).1)
  rw [← hvk_def] at hvk
  refine iteration_verifies hP H A sk.expanded ⟨hs1' ▸ hs1, hs2' ▸ hs2⟩ sk.verificationKey
    sk.expanded.rho t1D hvk ?_ challenge hc mu hmu _ ?_ sig hiter
  · intro r hr j hj
    rw [ht1D r hr j hj, ht0_def]
    have := MLDSA.power2round_range
      (MLDSA.addMod (ocamlInverseNtt (ocamlMatVec P.l A (fun j => MLDSA.ntt (sk.expanded.s1 j)) r) j)
        (sk.expanded.s2 r j))
    unfold computePublicParts
    simp only [keyOps]
    rw [this.2.2.2.2, Int.emod_emod_of_dvd _ (dvd_refl _)]
  · intro r _ j _
    simp only [maskVector, maskPolynomial, signOps]
    exact unpackZ_range hf.gamma1 _ (by simp [hf.zPacked]) j

/-- **`verify` accepts every signature `sign_with_randomness` produces** on a
    generated key (FIPS 204 correctness, for the OCaml models): same context
    and message, `tr = H(pk, 64)` recomputed by the verifier. -/
theorem signWithRandomness_verify {P : Params} (hP : P.Valid) (H : XOF) (xi : Bytes)
    (A : PolyMat) (s1 s2 : PolyVec)
    (hs1 : ∀ r < P.l, ∀ i < 256, -(P.eta : ℤ) ≤ s1 r i ∧ s1 r i ≤ P.eta)
    (hs2 : ∀ r < P.k, ∀ i < 256, -(P.eta : ℤ) ≤ s2 r i ∧ s2 r i ≤ P.eta)
    (challenge : Bytes → Poly) (hc : ∀ ct, challenge ct = sampleInBall P.tau (H ct))
    (context message rnd sig : Bytes)
    (hsign : signWithRandomness
      (signOps P (keypairFromSeed (keyOps P) P H (fun _ => A) (fun _ => (s1, s2)) xi).expanded)
      P H A challenge context
      (keypairFromSeed (keyOps P) P H (fun _ => A) (fun _ => (s1, s2)) xi).expanded message rnd =
        .ok sig) :
    verify (verifyOps P) P H (fun _ => A) challenge context
      (keypairFromSeed (keyOps P) P H (fun _ => A) (fun _ => (s1, s2)) xi).verificationKey message
      sig = true := by
  have hctx : ¬ context.length > 255 := by
    intro h; unfold signWithRandomness at hsign; rw [ite_eq_left h] at hsign; cases hsign
  unfold signWithRandomness signFormattedWithRandomness at hsign
  rw [ite_eq_right hctx] at hsign
  have := signMu_verifyMu hP H xi A s1 s2 hs1 hs2 challenge hc _ rnd sig hsign
  unfold verify verifyFormatted
  rw [ite_eq_right hctx]
  exact this

/-- **`verify` accepts every signature `sign` produces** on a generated key. -/
theorem sign_verify {P : Params} (hP : P.Valid) (H : XOF) (xi : Bytes) (A : PolyMat)
    (s1 s2 : PolyVec)
    (hs1 : ∀ r < P.l, ∀ i < 256, -(P.eta : ℤ) ≤ s1 r i ∧ s1 r i ≤ P.eta)
    (hs2 : ∀ r < P.k, ∀ i < 256, -(P.eta : ℤ) ≤ s2 r i ∧ s2 r i ≤ P.eta)
    (challenge : Bytes → Poly) (hc : ∀ ct, challenge ct = sampleInBall P.tau (H ct))
    (context message sig : Bytes) (random : ℕ → Bytes)
    (hsign : (sign
      (signOps P (keypairFromSeed (keyOps P) P H (fun _ => A) (fun _ => (s1, s2)) xi).expanded)
      P H A challenge context random
      (keypairFromSeed (keyOps P) P H (fun _ => A) (fun _ => (s1, s2)) xi).expanded message).2 =
        some (.ok sig)) :
    verify (verifyOps P) P H (fun _ => A) challenge context
      (keypairFromSeed (keyOps P) P H (fun _ => A) (fun _ => (s1, s2)) xi).verificationKey message
      sig = true := by
  unfold sign at hsign
  by_cases h1 : context.length > 255
  · rw [ite_eq_left h1] at hsign; simp at hsign
  · rw [ite_eq_right h1] at hsign
    simp only at hsign
    split_ifs at hsign with h2
    simp only [Option.some.injEq] at hsign
    exact signWithRandomness_verify hP H xi A s1 s2 hs1 hs2 challenge hc context message _ sig
      hsign

/-- **`verify` accepts every signature `sign_deterministic` produces** on a
    generated key. -/
theorem signDeterministic_verify {P : Params} (hP : P.Valid) (H : XOF) (xi : Bytes)
    (A : PolyMat) (s1 s2 : PolyVec)
    (hs1 : ∀ r < P.l, ∀ i < 256, -(P.eta : ℤ) ≤ s1 r i ∧ s1 r i ≤ P.eta)
    (hs2 : ∀ r < P.k, ∀ i < 256, -(P.eta : ℤ) ≤ s2 r i ∧ s2 r i ≤ P.eta)
    (challenge : Bytes → Poly) (hc : ∀ ct, challenge ct = sampleInBall P.tau (H ct))
    (context message sig : Bytes)
    (hsign : signDeterministic
      (signOps P (keypairFromSeed (keyOps P) P H (fun _ => A) (fun _ => (s1, s2)) xi).expanded)
      P H A challenge context
      (keypairFromSeed (keyOps P) P H (fun _ => A) (fun _ => (s1, s2)) xi).expanded message =
        .ok sig) :
    verify (verifyOps P) P H (fun _ => A) challenge context
      (keypairFromSeed (keyOps P) P H (fun _ => A) (fun _ => (s1, s2)) xi).verificationKey message
      sig = true :=
  signWithRandomness_verify hP H xi A s1 s2 hs1 hs2 challenge hc context message _ sig hsign

end OcamlPq.EndToEnd.MLDSA
