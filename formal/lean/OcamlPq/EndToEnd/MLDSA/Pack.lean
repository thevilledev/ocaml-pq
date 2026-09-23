import OcamlPq.EndToEnd.MLDSA.ParamFacts

/-!
# Packings, key and signature layouts on `MLDSAAlg` types

The Encoding area models `pack_t1`, `pack_eta`, `pack_t0`, `pack_w1`,
`unpack_z`, `encode_signature`, `decode_signature`, `decode_verification_key`
over `List ℕ` / `List ℤ` and proves them equal to FIPS 204 Algorithms 16, 17,
19, 23 (transcribed below), 26, 27 on the ranges the code uses. This file wraps both
sides in the `MLDSAAlg` types (`Poly`, `PolyVec`, `Bytes`) with the adapters of
`Adapters.lean` and restates the Encoding theorems there.

**Range restrictions.** The packers are only FIPS 204's on the coefficient
ranges FIPS 204 defines them for: `SimpleBitPack(w, b)` requires
`w ∈ [0, b]^256`, `BitPack(w, a, b)` requires `w ∈ [−a, b]^256`. Out of range,
the OCaml `pack_codes` lets high bits of one code spill into the next, while
the Lean transcription of FIPS 204 truncates each code to `bitlen b` bits. So
the equalities below carry range hypotheses; `MLDSAAlg`'s refinement
structures state them for *all* polynomials, which the concrete models do
not satisfy (see `KeyGen.lean`, `Sign.lean`, `Verify.lean` for how this is
bridged).
-/

namespace OcamlPq.EndToEnd.MLDSA

open OcamlPq.MLDSAAlg

/-! ## Polynomial packers -/

/-- `pack_t1` (Encoding model) on an `MLDSAAlg` polynomial. -/
def ocamlPackT1 (p : Poly) : Bytes := natToBytes (Encoding.Mldsa.packT1 (polyToNatList p))

/-- `pack_eta` (Encoding model). -/
def ocamlPackEta (eta : ℕ) (p : Poly) : Bytes :=
  natToBytes (Encoding.Mldsa.packEta eta (polyToList p))

/-- `pack_t0` (Encoding model). -/
def ocamlPackT0 (p : Poly) : Bytes := natToBytes (Encoding.Mldsa.packT0 (polyToList p))

/-- `pack_w1` (Encoding model) with `w1_bits` for `γ2`. -/
def ocamlPackW1 (gamma2 : ℕ) (p : Poly) : Bytes :=
  natToBytes (Encoding.Mldsa.packW1 (Encoding.Mldsa.w1Bits gamma2) (polyToNatList p))

/-- `unpack_z` (Encoding model) with `z_bits` for `γ1`. -/
def ocamlUnpackZ (gamma1 : ℕ) (v : Bytes) : Poly :=
  listToPoly (Encoding.Mldsa.unpackZ gamma1 (Encoding.Mldsa.zBits gamma1) (bytesToNat v))

/-- FIPS 204 Algorithm 16, `SimpleBitPack(w, b)` (Encoding area's
    transcription). -/
def fipsSimpleBitPack (p : Poly) (b : ℕ) : Bytes :=
  natToBytes (Encoding.Spec.simpleBitPack (polyToNatList p) b)

/-- FIPS 204 Algorithm 17, `BitPack(w, a, b)`. -/
def fipsBitPack (p : Poly) (a b : ℕ) : Bytes :=
  natToBytes (Encoding.Spec.bitPack (polyToList p) a b)

/-- FIPS 204 Algorithm 19, `BitUnpack(v, a, b)`. -/
def fipsBitUnpack (v : Bytes) (a b : ℕ) : Poly :=
  listToPoly (Encoding.Spec.bitUnpack (bytesToNat v) a b)

theorem mem_polyToNatList {p : Poly} {x : ℕ} :
    x ∈ polyToNatList p ↔ ∃ i < 256, (p i).toNat = x := by
  simp [polyToNatList]

/-- `pack_t1 = SimpleBitPack(·, 2^10 − 1)` on `[0, 2^10)^256`. -/
theorem packT1_eq_fips (p : Poly) (h : ∀ i < 256, 0 ≤ p i ∧ p i < 2 ^ 10) :
    ocamlPackT1 p = fipsSimpleBitPack p (2 ^ 10 - 1) := by
  unfold ocamlPackT1 fipsSimpleBitPack
  rw [Encoding.Mldsa.packT1_eq _ (by simp)]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_polyToNatList.mp hx
  have := h i hi
  omega

/-- `pack_eta = BitPack(·, η, η)` on `[−η, η]^256`. -/
theorem packEta_eq_fips {eta : ℕ} (heta : eta = 2 ∨ eta = 4) (p : Poly)
    (h : ∀ i < 256, -(eta : ℤ) ≤ p i ∧ p i ≤ eta) :
    ocamlPackEta eta p = fipsBitPack p eta eta := by
  unfold ocamlPackEta fipsBitPack
  rw [Encoding.Mldsa.packEta_eq eta heta _ (by simp)]
  intro v hv
  obtain ⟨i, hi, rfl⟩ := mem_polyToList.mp hv
  exact h i hi

/-- `pack_t0 = BitPack(·, 2^12 − 1, 2^12)` on `(−2^12, 2^12]^256`. -/
theorem packT0_eq_fips (p : Poly) (h : ∀ i < 256, -(2 ^ 12 : ℤ) < p i ∧ p i ≤ 2 ^ 12) :
    ocamlPackT0 p = fipsBitPack p (2 ^ 12 - 1) (2 ^ 12) := by
  unfold ocamlPackT0 fipsBitPack
  rw [Encoding.Mldsa.packT0_eq _ (by simp)]
  intro v hv
  obtain ⟨i, hi, rfl⟩ := mem_polyToList.mp hv
  exact h i hi

/-- `pack_w1 = SimpleBitPack(·, (q − 1)/(2γ2) − 1)` on `[0, (q − 1)/(2γ2))^256`. -/
theorem packW1_eq_fips {P : Params} (hP : P.Valid) (p : Poly)
    (h : ∀ i < 256, 0 ≤ p i ∧ p i < (w1Count P : ℤ)) :
    ocamlPackW1 P.gamma2 p = fipsSimpleBitPack p ((q - 1) / (2 * P.gamma2) - 1) := by
  have hf := e2eFacts hP
  unfold ocamlPackW1 fipsSimpleBitPack
  rw [Encoding.Mldsa.packW1_eq _ hf.gamma2 _ (by simp), hf.w1Bound]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_polyToNatList.mp hx
  have := h i hi
  have := hf.w1Count_le
  omega

/-- `unpack_z = BitUnpack(·, γ1 − 1, γ1)` on inputs of `32·z_bits` bytes. -/
theorem unpackZ_eq_fips {gamma1 : ℕ} (hg : gamma1 = 2 ^ 17 ∨ gamma1 = 2 ^ 19) (v : Bytes)
    (hv : v.length = 32 * Encoding.Mldsa.zBits gamma1) :
    ocamlUnpackZ gamma1 v = fipsBitUnpack v (gamma1 - 1) gamma1 := by
  unfold ocamlUnpackZ fipsBitUnpack
  rw [Encoding.Mldsa.unpackZ_eq _ hg _ (by simpa using hv) (bytesToNat_lt v)]

theorem listToPoly_range {l : List ℤ} {lo hi : ℤ} (h0 : lo ≤ 0) (h1 : 0 ≤ hi)
    (h : ∀ x ∈ l, lo ≤ x ∧ x ≤ hi) (i : ℕ) : lo ≤ listToPoly l i ∧ listToPoly l i ≤ hi := by
  unfold listToPoly
  by_cases hi' : i < l.length
  · rw [List.getD_eq_getElem _ _ hi']; exact h _ (List.getElem_mem hi')
  · rw [List.getD_eq_default _ _ (by omega)]; exact ⟨h0, h1⟩

/-- Every coefficient `unpack_z` produces lies in `(−γ1, γ1]`. -/
theorem unpackZ_range {gamma1 : ℕ} (hg : gamma1 = 2 ^ 17 ∨ gamma1 = 2 ^ 19) (v : Bytes)
    (hv : v.length = 32 * Encoding.Mldsa.zBits gamma1) (i : ℕ) :
    -(gamma1 : ℤ) < ocamlUnpackZ gamma1 v i ∧ ocamlUnpackZ gamma1 v i ≤ gamma1 := by
  have hr := Encoding.Mldsa.unpackZ_range gamma1 hg (bytesToNat v) (by simpa using hv)
    (bytesToNat_lt v)
  have := listToPoly_range (lo := -(gamma1 : ℤ) + 1) (hi := gamma1) (by omega) (by omega)
    (fun x hx => by have := hr x hx; unfold Encoding.Mldsa.ZRange at this; omega) i
  unfold ocamlUnpackZ
  omega

/-! ## Hints -/

/-- **Adapter.** A hint vector (`int array array`, `k` rows of 256) as the
    Encoding area's `HintVec`: entry `1` exactly where the OCaml encoder's test
    `hint.(row).(coefficient) <> 0` succeeds, `0` outside the `k × 256`
    array. -/
def hintToVec (k : ℕ) (h : PolyVec) : Encoding.Hint.HintVec :=
  fun r c => if r < k ∧ c < 256 ∧ h r c ≠ 0 then 1 else 0

/-- **Adapter.** A decoded `HintVec` as an `int array array`. -/
def hintToPoly (h : Encoding.Hint.HintVec) : PolyVec := fun r c => (h r c : ℤ)

theorem filter_length_eq_sum (L : List ℕ) (f : ℕ → ℤ) (g : ℕ → ℕ)
    (hfg : ∀ c ∈ L, (g c ≠ 0 ↔ f c ≠ 0)) (h01 : ∀ c ∈ L, f c = 0 ∨ f c = 1) :
    ((L.filter fun c => g c ≠ 0).length : ℤ) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih' := ih (fun c hc => hfg c (by simp [hc])) (fun c hc => h01 c (by simp [hc]))
    rw [List.map_cons, List.sum_cons]
    have ha := hfg a (by simp)
    rcases h01 a (by simp) with h | h
    · have : ¬ g a ≠ 0 := by rw [ha, h]; simp
      rw [List.filter_cons_of_neg (by simpa using this), ih', h, zero_add]
    · have : g a ≠ 0 := by rw [ha, h]; simp
      rw [List.filter_cons_of_pos (by simpa using this), List.length_cons, Nat.cast_add, ih', h]
      ring

/-- The weight of a 0/1 hint vector is the sum of its entries. -/
theorem weight_hintToVec (k : ℕ) (h : PolyVec) (h01 : ∀ r < k, ∀ c < 256, h r c = 0 ∨ h r c = 1) :
    (Encoding.Hint.weight k (hintToVec k h) : ℤ) = ((vecToLists k h).map List.sum).sum := by
  unfold Encoding.Hint.weight Encoding.Hint.allList vecToLists
  rw [List.length_flatMap, Nat.cast_list_sum, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r hr
  rw [List.mem_range] at hr
  simp only [Function.comp, Encoding.Hint.rowList, polyToList]
  apply filter_length_eq_sum
  · intro c hc
    rw [List.mem_range] at hc
    simp [hintToVec, hr, hc]
  · intro c hc
    exact h01 r hr c (List.mem_range.mp hc)

/-! ## Signatures -/

/-- `encode_signature c_tilde z hint` (Encoding model, lines 685–706). -/
def ocamlEncodeSig (P : Params) (ct : Bytes) (z h : PolyVec) : Bytes :=
  natToBytes (Encoding.Mldsa.encodeSig (encParams P) (bytesToNat ct) (vecToLists P.l z)
    (hintToVec P.k h))

/-- FIPS 204 Algorithm 26, `sigEncode(c̃, z, h)` (Encoding area's
    transcription). -/
def fipsSigEncode (P : Params) (ct : Bytes) (z h : PolyVec) : Bytes :=
  natToBytes (Encoding.Mldsa.sigEncode (encParams P) (bytesToNat ct) (vecToLists P.l z)
    (hintToVec P.k h))

/-- **`encode_signature` is `sigEncode`** for `|c̃| = λ/4`,
    `z ∈ (−γ1, γ1]^{ℓ×256}` and a hint of weight at most `ω`. -/
theorem encodeSig_eq_fips {P : Params} (hP : P.Valid) (ct : Bytes) (z h : PolyVec)
    (hct : ct.length = P.cTildeBytes)
    (hz : ∀ r < P.l, ∀ i < 256, -(P.gamma1 : ℤ) < z r i ∧ z r i ≤ P.gamma1)
    (hw : Encoding.Hint.weight P.k (hintToVec P.k h) ≤ P.omega) :
    ocamlEncodeSig P ct z h = fipsSigEncode P ct z h := by
  have hf := e2eFacts hP
  unfold ocamlEncodeSig fipsSigEncode
  rw [Encoding.Mldsa.encodeSig_eq_spec _ hf.encValid]
  refine ⟨by simpa [encParams] using hct, bytesToNat_lt ct, by simp [encParams], ?_, ?_, ?_, hw⟩
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := mem_vecToLists.mp hp
    refine ⟨by simp, fun v hv => ?_⟩
    obtain ⟨i, hi, rfl⟩ := mem_polyToList.mp hv
    exact hz r hr i hi
  · intro r c; unfold hintToVec; split_ifs <;> simp
  · intro r c hrc; unfold hintToVec; rw [ite_eq_right]; intro h'; simp only [encParams] at hrc; omega

/-- `decode_signature` (Encoding model, lines 642–676) on `MLDSAAlg` types;
    `none` is `Error _`. -/
def ocamlDecodeSig (P : Params) (sig : Bytes) : Option (Bytes × PolyVec × PolyVec) :=
  (Encoding.Mldsa.decodeSig (encParams P) (bytesToNat sig)).map
    fun x => (natToBytes x.1, listsToVec x.2.1, hintToPoly x.2.2)

/-- FIPS 204 Algorithm 27, `sigDecode(σ)` (Encoding area's transcription);
    `none` is `⊥`. -/
def fipsSigDecode (P : Params) (sig : Bytes) : Option (Bytes × PolyVec × PolyVec) :=
  (Encoding.Mldsa.sigDecode (encParams P) (bytesToNat sig)).map
    fun x => (natToBytes x.1, listsToVec x.2.1, hintToPoly x.2.2)

/-- **`decode_signature` is `sigDecode` on strings of the checked length, and
    rejects every other length.** -/
theorem decodeSig_eq_fips {P : Params} (hP : P.Valid) (sig : Bytes) :
    ocamlDecodeSig P sig = if sig.length = P.signatureSize then fipsSigDecode P sig else none := by
  have hf := e2eFacts hP
  unfold ocamlDecodeSig fipsSigDecode
  split_ifs with hlen
  · rw [Encoding.Mldsa.decodeSig_eq_spec _ hf.encValid _ (by simp [hlen, hf.sigSize])
      (bytesToNat_lt sig)]
  · unfold Encoding.Mldsa.decodeSig
    rw [ite_eq_left (by simp [hf.sigSize, hlen])]
    rfl

/-- Decoded hints are 0/1. -/
theorem fipsSigDecode_hint01 {P : Params} {sig ct : Bytes} {z h : PolyVec}
    (hd : fipsSigDecode P sig = some (ct, z, h)) : ∀ r c, h r c = 0 ∨ h r c = 1 := by
  unfold fipsSigDecode Encoding.Mldsa.sigDecode at hd
  simp only at hd
  split at hd
  · simp at hd
  · rename_i h' hh
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨-, -, rfl⟩ := hd
    have := (Encoding.Hint.decoded_valid _ _ _ (fun x hx => bytesToNat_lt sig x
      (List.mem_of_mem_drop hx)) _ hh).1
    intro r c
    have h1 := this r c
    unfold hintToPoly
    omega

/-- The `c̃` component of `sigDecode(σ)` is `σ[0 : λ/4]`. -/
theorem fipsSigDecode_cTilde {P : Params} {sig ct : Bytes} {z h : PolyVec}
    (hd : fipsSigDecode P sig = some (ct, z, h)) : ct = sig.take P.cTildeBytes := by
  unfold fipsSigDecode Encoding.Mldsa.sigDecode at hd
  simp only at hd
  split at hd
  · simp at hd
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -, -⟩ := hd
    rw [← bytesToNat_take, natToBytes_bytesToNat]; rfl

/-! ## Verification keys -/

/-- `decode_verification_key` (Encoding model, lines 474–486) on `MLDSAAlg`
    types; `none` is `Error _`. -/
def ocamlDecodeVk (P : Params) (pk : Bytes) : Option (Bytes × PolyVec) :=
  (Encoding.Mldsa.decodeVk (encParams P) (bytesToNat pk)).map
    fun x => (natToBytes x.1, fun r => natListToPoly (x.2.getD r []))

/-- FIPS 204 Algorithm 23, `pkDecode(pk)`:
    `(ρ, z_0, …, z_{k−1}) ← pk` with `z_i` of `32·(bitlen(q − 1) − d)` bytes,
    `t1[i] ← SimpleBitUnpack(z_i, 2^{bitlen(q−1)−d} − 1)`. (The Encoding area
    transcribes `pkEncode` only; this transcription uses its
    `SimpleBitUnpack`.) -/
def fipsPkDecode (P : Params) (pk : Bytes) : Bytes × PolyVec :=
  let c := bitlen (q - 1) - d
  (pk.take 32, fun r => if r < P.k then
    natListToPoly (Encoding.Spec.simpleBitUnpack
      (bytesToNat ((pk.drop (32 + r * (32 * c))).take (32 * c))) (2 ^ c - 1))
    else fun _ => 0)

/-- **`decode_verification_key` is `pkDecode` on strings of the checked length,
    and rejects every other length.** -/
theorem decodeVk_eq_fips {P : Params} (hP : P.Valid) (pk : Bytes) :
    ocamlDecodeVk P pk =
      if pk.length = P.verificationKeySize then some (fipsPkDecode P pk) else none := by
  have hf := e2eFacts hP
  unfold ocamlDecodeVk Encoding.Mldsa.decodeVk
  by_cases hlen : pk.length = P.verificationKeySize
  · rw [ite_eq_left hlen, ite_eq_right (by simp [hlen, hf.vkSize])]
    simp only [Option.map_some, Option.some.injEq]
    unfold fipsPkDecode
    simp only [hf.t1Bits]
    refine Prod.ext ?_ ?_
    · simp only [Encoding.sub, List.drop_zero]
      rw [← bytesToNat_take, natToBytes_bytesToNat]
    · funext r
      simp only
      split_ifs with hr
      · rw [List.getD_eq_getElem _ _ (by simp [encParams, hr])]
        simp only [List.getElem_map, List.getElem_range]
        have hle : 32 + r * 320 + 320 ≤ (bytesToNat pk).length := by
          simp only [length_bytesToNat, hlen, Params.verificationKeySize]
          nlinarith
        rw [Encoding.Mldsa.unpackT1_eq _ (Encoding.length_sub _ _ _ hle)
          (Encoding.sub_lt (bytesToNat_lt pk) _ _)]
        rw [bytesToNat_take, bytesToNat_drop]
        rfl
      · rw [List.getD_eq_default _ _ (by simp [encParams]; omega)]
        funext i; simp [natListToPoly]
  · rw [ite_eq_right hlen, ite_eq_left (by simp [hlen, hf.vkSize])]
    rfl

/-! ## The `‖z‖∞` check -/

/-- `vector_norm_violation_flag z (P.gamma1 - beta) <> 0` on the `ℓ` rows of
    `z`. -/
def ocamlZNormViolation (P : Params) (z : PolyVec) : Bool :=
  MLDSA.vectorNormViolationFlag (vecToLists P.l z) ((P.gamma1 : ℤ) - (P.tau * P.eta : ℕ)) ≠ 0

/-- FIPS 204 `‖z‖∞ < γ1 − β` (Algorithm 8 line 13), with `‖·‖∞` of §2.3
    (`MLDSA.coeffNorm w = |w mod± q|`). -/
def fipsZNormOk (P : Params) (z : PolyVec) : Bool :=
  (List.range P.l).all fun r => (List.range 256).all fun i =>
    decide (MLDSA.coeffNorm (z r i) < (P.gamma1 : ℤ) - (P.tau * P.eta : ℕ))

theorem fipsZNormOk_iff (P : Params) (z : PolyVec) :
    fipsZNormOk P z = true ↔
      ∀ r < P.l, ∀ i < 256, MLDSA.coeffNorm (z r i) < (P.gamma1 : ℤ) - (P.tau * P.eta : ℕ) := by
  simp [fipsZNormOk, List.all_eq_true]

theorem infNormGe_vecToLists (len : ℕ) (v : PolyVec) (b : ℤ) :
    MLDSA.infNormGe (vecToLists len v) b ↔ ∃ r < len, ∃ i < 256, MLDSA.coeffNorm (v r i) ≥ b := by
  unfold MLDSA.infNormGe
  constructor
  · rintro ⟨p, hp, x, hx, h⟩
    obtain ⟨r, hr, rfl⟩ := mem_vecToLists.mp hp
    obtain ⟨i, hi, rfl⟩ := mem_polyToList.mp hx
    exact ⟨r, hr, i, hi, h⟩
  · rintro ⟨r, hr, i, hi, h⟩
    exact ⟨_, mem_vecToLists.mpr ⟨r, hr, rfl⟩, _, mem_polyToList.mpr ⟨i, hi, rfl⟩, h⟩

theorem zNorm_eq_fips (P : Params) (z : PolyVec) :
    ocamlZNormViolation P z = !fipsZNormOk P z := by
  unfold ocamlZNormViolation
  rw [MLDSA.vectorNormViolationFlag_eq]
  cases hz : fipsZNormOk P z
  · have : ¬ ∀ r < P.l, ∀ i < 256,
        MLDSA.coeffNorm (z r i) < (P.gamma1 : ℤ) - (P.tau * P.eta : ℕ) := by
      rw [← fipsZNormOk_iff]; simp [hz]
    push Not at this
    rw [ite_eq_left ((infNormGe_vecToLists _ _ _).mpr this)]
    decide
  · have := (fipsZNormOk_iff P z).mp hz
    rw [ite_eq_right]
    · decide
    · intro h
      obtain ⟨r, hr, i, hi, h⟩ := (infNormGe_vecToLists _ _ _).mp h
      have := this r hr i hi
      omega

end OcamlPq.EndToEnd.MLDSA
