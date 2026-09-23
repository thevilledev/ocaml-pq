import OcamlPq.Encoding.MldsaPack
import OcamlPq.Encoding.HintRoundTrip

/-!
# ML-DSA key and signature layouts

Models of `encode_signature` / `decode_signature` (`mldsa/mldsa_engine.ml`
lines 642–706), `encode_verification_key` / `decode_verification_key`
(lines 471–486) and `encode_expanded_signing_key` /
`decode_expanded_signing_key` (lines 488–529), and the sizes of lines 116–132.

Main results:

* `sizes`: public key 1312/1952/2592, signing key 2560/4032/4896 and
  signature 2420/3309/4627 bytes (FIPS 204 Table 2).
* `encodeSig_eq_spec`: `encode_signature` is FIPS 204 `sigEncode`
  (Algorithm 26); `decodeSig_eq_spec`: `decode_signature` is `sigDecode`
  (Algorithm 27) on strings of the checked length, including the exact
  accept/reject behaviour of `HintBitUnpack`.
* `decodeSig_encodeSig`: decoding an encoded signature gives back
  `(c̃, z, h)`.
* `encodeSig_decodeSig` — **signature non-malleability at the encoding
  level**: if `decode_signature σ = Ok (c̃, z, h)` then
  `encode_signature c̃ z h = σ`. Two different byte strings never decode to
  the same `(c̃, z, h)`.
* `decodeSig_offsets`: every region `decode_signature` reads lies inside a
  string of the checked length, and the regions tile it.
* `encodeVk_eq_spec`, `decodeVk_encodeVk`, `encodeVk_decodeVk`: the
  verification key is FIPS 204 `pkEncode`, round-trips, and every byte string
  of the right length is a (canonical) key.

Expanded signing keys are in `MldsaSk.lean`.
-/

namespace OcamlPq.Encoding.Mldsa

open Nat (ofDigits)
open OcamlPq.Encoding
open OcamlPq.Encoding.Packer
open OcamlPq.Encoding.Hint

/-- The parameters of `Mldsa_engine.Make`. -/
structure Params where
  k : ℕ
  l : ℕ
  eta : ℕ
  gamma1 : ℕ
  gamma2 : ℕ
  omega : ℕ
  cTildeBytes : ℕ

/-- ML-DSA-44 (lines 910–920). -/
def mldsa44 : Params := ⟨4, 4, 2, 2 ^ 17, (q - 1) / 88, 80, 32⟩
/-- ML-DSA-65 (lines 922–932). -/
def mldsa65 : Params := ⟨6, 5, 4, 2 ^ 19, (q - 1) / 32, 55, 48⟩
/-- ML-DSA-87 (lines 934–944). -/
def mldsa87 : Params := ⟨8, 7, 2, 2 ^ 19, (q - 1) / 32, 75, 64⟩

namespace Params

/-- `eta_packed_bytes = n * eta_bits / 8`. -/
def etaPackedBytes (P : Params) : ℕ := 256 * etaBits P.eta / 8
/-- `z_packed_bytes = n * z_bits / 8`. -/
def zPackedBytes (P : Params) : ℕ := 256 * zBits P.gamma1 / 8
/-- `verification_key_size = seed_size + k * t1_packed_bytes`. -/
def vkSize (P : Params) : ℕ := 32 + P.k * 320
/-- `signing_key_size = 2 * seed_size + tr_bytes + (l + k) * eta_packed_bytes + k * t0_packed_bytes`. -/
def skSize (P : Params) : ℕ := 2 * 32 + 64 + (P.l + P.k) * P.etaPackedBytes + P.k * 416
/-- `signature_size = c_tilde_bytes + l * z_packed_bytes + omega + k`. -/
def sigSize (P : Params) : ℕ := P.cTildeBytes + P.l * P.zPackedBytes + P.omega + P.k
/-- The offset of the hint section. -/
def hintOffset (P : Params) : ℕ := P.cTildeBytes + P.l * P.zPackedBytes

/-- The parameter sets the library instantiates satisfy these. -/
def Valid (P : Params) : Prop := (P.eta = 2 ∨ P.eta = 4) ∧ (P.gamma1 = 2 ^ 17 ∨ P.gamma1 = 2 ^ 19)

theorem zPackedBytes_eq (P : Params) : P.zPackedBytes = 32 * zBits P.gamma1 := by
  unfold zPackedBytes; omega

theorem etaPackedBytes_eq (P : Params) : P.etaPackedBytes = 32 * etaBits P.eta := by
  unfold etaPackedBytes; omega

end Params

theorem valid_params : mldsa44.Valid ∧ mldsa65.Valid ∧ mldsa87.Valid := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [mldsa44, mldsa65, mldsa87]

/-- **Sizes** (FIPS 204 Table 2). -/
theorem sizes :
    (mldsa44.vkSize, mldsa44.skSize, mldsa44.sigSize) = (1312, 2560, 2420) ∧
    (mldsa65.vkSize, mldsa65.skSize, mldsa65.sigSize) = (1952, 4032, 3309) ∧
    (mldsa87.vkSize, mldsa87.skSize, mldsa87.sigSize) = (2592, 4896, 4627) := by
  decide

/-! ## Sequential blits -/

/-- Blitting equal-length blocks one after another, advancing `position`. -/
theorem blit_seq (len : ℕ) :
    ∀ (blocks : List (List ℕ)) (P rest : List ℕ), (∀ b ∈ blocks, b.length = len) →
      blocks.foldl (fun (st : List ℕ × ℕ) b => (blit b 0 st.1 st.2 len, st.2 + len))
        (P ++ rest, P.length) =
      (P ++ blocks.flatten ++ rest.drop (blocks.length * len), P.length + blocks.length * len) := by
  intro blocks
  induction blocks with
  | nil => intro P rest _; simp
  | cons b bs ih =>
    intro P rest hlen
    have hb := hlen b (by simp)
    rw [List.foldl_cons]
    simp only
    rw [show len = b.length from hb.symm, blit_after_prefix, hb]
    have := ih (P ++ b) (rest.drop len) (fun x hx => hlen x (by simp [hx]))
    simp only [List.length_append, hb] at this
    rw [this]
    simp only [List.flatten_cons, List.append_assoc, List.drop_drop, List.length_cons]
    rw [show (bs.length + 1) * len = len + bs.length * len by ring, Nat.add_assoc]

/-- A string cut into a prefix, `n` blocks of length `len`, and the rest. -/
theorem split_blocks (s : List ℕ) (off n len : ℕ) :
    s = sub s 0 off ++ ((List.range n).map (fun i => sub s (off + i * len) len)).flatten ++
      s.drop (off + n * len) := by
  have hmid : ((List.range n).map (fun i => sub s (off + i * len) len)).flatten =
      (s.drop off).take (n * len) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.flatten_append, ih, List.map_singleton,
        List.flatten_singleton, Nat.succ_mul, List.take_add, List.drop_drop]
      rfl
  rw [hmid]
  unfold sub
  rw [List.drop_zero, List.append_assoc, ← List.drop_drop, List.take_append_drop,
    List.take_append_drop]

theorem sub_block (blocks : List (List ℕ)) (len : ℕ) (hlen : ∀ b ∈ blocks, b.length = len)
    (P R : List ℕ) (i : ℕ) (hi : i < blocks.length) :
    sub (P ++ blocks.flatten ++ R) (P.length + i * len) len = blocks[i] := by
  unfold sub
  rw [List.append_assoc, ← List.drop_drop, List.drop_left' rfl]
  exact sub_flatten_blocks blocks len hlen R i hi

/-! ## Signatures -/

/-- `encode_signature c_tilde z hint` (lines 685–706). -/
def encodeSig (P : Params) (cTilde : List ℕ) (z : List (List ℤ)) (h : HintVec) : List ℕ :=
  let output := List.replicate P.sigSize 0
  let output := blit cTilde 0 output 0 P.cTildeBytes
  let st := z.foldl (fun (st : List ℕ × ℕ) p =>
    (blit (packZ P.gamma1 (zBits P.gamma1) p) 0 st.1 st.2 P.zPackedBytes, st.2 + P.zPackedBytes))
    (output, P.cTildeBytes)
  encodeHint st.2 P.k P.omega h st.1

/-- `decode_signature octets` (lines 642–676); `none` is `Error _`. -/
def decodeSig (P : Params) (octets : List ℕ) : Option (List ℕ × List (List ℤ) × HintVec) :=
  if octets.length ≠ P.sigSize then none
  else
    let cTilde := sub octets 0 P.cTildeBytes
    let zOffset := P.cTildeBytes
    let z := (List.range P.l).map (fun index =>
      unpackZ P.gamma1 (zBits P.gamma1) (sub octets (zOffset + index * P.zPackedBytes) P.zPackedBytes))
    let hintOffset := zOffset + P.l * P.zPackedBytes
    match decodeHint octets hintOffset P.k P.omega with
    | none => none
    | some hint => some (cTilde, z, hint)

/-- FIPS 204 Algorithm 26, `sigEncode(c̃, z, h)`:
`σ ← c̃; for i < ℓ: σ ← σ ‖ BitPack(z[i], γ₁ − 1, γ₁); σ ← σ ‖ HintBitPack(h)`. -/
def sigEncode (P : Params) (cTilde : List ℕ) (z : List (List ℤ)) (h : HintVec) : List ℕ :=
  let σ := (List.range P.l).foldl
    (fun σ i => σ ++ Spec.bitPack (z.getD i []) (P.gamma1 - 1) P.gamma1) cTilde
  σ ++ hintBitPack P.k P.omega h

/-- FIPS 204 Algorithm 27, `sigDecode(σ)`: split `σ` into
`c̃ ∈ 𝔹^{λ/4}`, `x_i ∈ 𝔹^{32(1 + bitlen(γ₁ − 1))}` and `h ∈ 𝔹^{ω+k}`;
`z[i] ← BitUnpack(x_i, γ₁ − 1, γ₁)`; `h ← HintBitUnpack(h)`. -/
def sigDecode (P : Params) (σ : List ℕ) : Option (List ℕ × List (List ℤ) × HintVec) :=
  let xlen := 32 * (1 + Spec.bitlen (P.gamma1 - 1))
  let cTilde := σ.take P.cTildeBytes
  let z := (List.range P.l).map (fun i =>
    Spec.bitUnpack ((σ.drop (P.cTildeBytes + i * xlen)).take xlen) (P.gamma1 - 1) P.gamma1)
  match hintBitUnpack P.k P.omega (σ.drop (P.cTildeBytes + P.l * xlen)) with
  | none => none
  | some h => some (cTilde, z, h)

theorem bitlen_gamma1_sub_one (P : Params) (hP : P.Valid) :
    32 * (1 + Spec.bitlen (P.gamma1 - 1)) = P.zPackedBytes := by
  rw [Params.zPackedBytes_eq]
  rcases hP.2 with h | h <;> rw [h]
  · rw [show zBits (2 ^ 17) = 18 by decide, show (2 : ℕ) ^ 17 - 1 = 2 ^ 17 - 1 from rfl,
      Spec.bitlen_eq (c := 17) (by norm_num) (by norm_num) (by norm_num)]
  · rw [show zBits (2 ^ 19) = 20 by decide,
      Spec.bitlen_eq (c := 19) (by norm_num) (by norm_num) (by norm_num)]

/-- A valid signature input: `|c̃| = c_tilde_bytes`, `ℓ` polynomials `z_i` with
coefficients in `(−γ₁, γ₁]`, and `h ∈ {0,1}^{k×256}` with at most `ω` ones. -/
structure SigInput (P : Params) (cTilde : List ℕ) (z : List (List ℤ)) (h : HintVec) : Prop where
  cTilde_len : cTilde.length = P.cTildeBytes
  cTilde_lt : ∀ x ∈ cTilde, x < 256
  z_len : z.length = P.l
  z_poly : ∀ p ∈ z, p.length = 256 ∧ ∀ v ∈ p, ZRange P.gamma1 v
  h01 : ∀ r c, h r c ≤ 1
  hdom : ∀ r c, P.k ≤ r ∨ 256 ≤ c → h r c = 0
  weight : weight P.k h ≤ P.omega

theorem length_packZ (P : Params) (p : List ℤ) (hp : p.length = 256) :
    (packZ P.gamma1 (zBits P.gamma1) p).length = P.zPackedBytes := by
  unfold packZ
  rw [length_packCodes]; simp [hp, Params.zPackedBytes]

theorem packZ_lt (P : Params) (hP : P.Valid) (p : List ℤ) (hp : p.length = 256)
    (hr : ∀ v ∈ p, ZRange P.gamma1 v) : ∀ x ∈ packZ P.gamma1 (zBits P.gamma1) p, x < 256 := by
  obtain ⟨-, -, h1⟩ := gamma1_cases P.gamma1 hP.2
  have hcodes : ∀ x ∈ p.map (fun v => ((P.gamma1 : ℤ) - v).toNat), x < 2 ^ zBits P.gamma1 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ha, hb⟩ := hr v hv
    have := gamma1_double P.gamma1 hP.2
    have : (((P.gamma1 : ℤ) - v).toNat : ℤ) < 2 ^ zBits P.gamma1 := by
      rw [Int.toNat_of_nonneg (by omega)]; omega
    exact_mod_cast this
  have := packCodes_regroup hcodes (by simp [hp]; exact ⟨32 * zBits P.gamma1, by ring⟩)
  exact this.right_lt

/-- **`encode_signature` is `c̃ ‖ pack_z(z₀) ‖ … ‖ HintBitPack(h)`.** -/
theorem encodeSig_eq (P : Params) (cTilde : List ℕ) (z : List (List ℤ))
    (h : HintVec) (hin : SigInput P cTilde z h) :
    encodeSig P cTilde z h =
      cTilde ++ (z.map (packZ P.gamma1 (zBits P.gamma1))).flatten ++ hintBitPack P.k P.omega h := by
  have hzl : ∀ b ∈ z.map (packZ P.gamma1 (zBits P.gamma1)), b.length = P.zPackedBytes := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact length_packZ P p (hin.z_poly p hp).1
  unfold encodeSig
  simp only
  have h0 : blit cTilde 0 (List.replicate P.sigSize 0) 0 P.cTildeBytes =
      cTilde ++ List.replicate (P.sigSize - P.cTildeBytes) 0 := by
    have := blit_after_prefix [] cTilde (List.replicate P.sigSize 0)
    simp only [List.nil_append, List.length_nil, hin.cTilde_len] at this
    rw [this, List.drop_replicate]
  rw [h0, ← List.foldl_map (f := packZ P.gamma1 (zBits P.gamma1))
    (g := fun (st : List ℕ × ℕ) b => (blit b 0 st.1 st.2 P.zPackedBytes, st.2 + P.zPackedBytes)),
    show P.cTildeBytes = cTilde.length from hin.cTilde_len.symm, blit_seq _ _ _ _ hzl]
  simp only [List.length_map, hin.z_len, List.drop_replicate]
  rw [show P.sigSize - cTilde.length - P.l * P.zPackedBytes = P.omega + P.k by
      unfold Params.sigSize; rw [hin.cTilde_len]; omega]
  have hPl : (cTilde ++ (z.map (packZ P.gamma1 (zBits P.gamma1))).flatten).length =
      cTilde.length + P.l * P.zPackedBytes := by
    rw [List.length_append, length_flatten_blocks _ _ hzl]; simp [hin.z_len]
  rw [← hPl, encodeHint_shift, encodeHint_eq_spec]

/-- **`encode_signature` is FIPS 204 `sigEncode`** (Algorithm 26). -/
theorem encodeSig_eq_spec (P : Params) (hP : P.Valid) (cTilde : List ℕ) (z : List (List ℤ))
    (h : HintVec) (hin : SigInput P cTilde z h) :
    encodeSig P cTilde z h = sigEncode P cTilde z h := by
  rw [encodeSig_eq P cTilde z h hin]
  unfold sigEncode
  simp only
  rw [Spec.foldl_append_range, ← hin.z_len]
  have := Spec.flatMap_range_getD' z [] (fun p => Spec.bitPack p (P.gamma1 - 1) P.gamma1)
  rw [this, List.flatMap_def, List.map_congr_left (fun p hp =>
    packZ_eq P.gamma1 hP.2 p (hin.z_poly p hp).1 (hin.z_poly p hp).2)]

theorem length_encodeSig (P : Params) (cTilde : List ℕ) (z : List (List ℤ))
    (h : HintVec) (hin : SigInput P cTilde z h) : (encodeSig P cTilde z h).length = P.sigSize := by
  have hzl : ∀ b ∈ z.map (packZ P.gamma1 (zBits P.gamma1)), b.length = P.zPackedBytes := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact length_packZ P p (hin.z_poly p hp).1
  rw [encodeSig_eq P cTilde z h hin, List.length_append, List.length_append,
    length_flatten_blocks _ _ hzl, length_hintBitPack _ _ _ hin.weight]
  simp [hin.z_len, hin.cTilde_len, Params.sigSize]; ring

/-- **The regions `decode_signature` reads.** For a string of the checked
length, `c̃ = σ[0 : c]`, `z_i` is read from `σ[c + i·zp : c + (i+1)·zp]`
(`i < ℓ`) and the hint section is `σ[c + ℓ·zp : c + ℓ·zp + ω + k]`; these
regions are in bounds and tile `σ`. -/
theorem decodeSig_offsets (P : Params) (σ : List ℕ) (hlen : σ.length = P.sigSize) :
    (∀ i < P.l, P.cTildeBytes + i * P.zPackedBytes + P.zPackedBytes ≤ P.hintOffset) ∧
    P.hintOffset + P.omega + P.k = σ.length ∧
    (∀ row < P.k, P.hintOffset + P.omega + row < σ.length) ∧
    σ = sub σ 0 P.cTildeBytes ++
      ((List.range P.l).map (fun i => sub σ (P.cTildeBytes + i * P.zPackedBytes) P.zPackedBytes)).flatten
      ++ σ.drop P.hintOffset := by
  refine ⟨fun i hi => ?_, ?_, fun row hr => ?_, ?_⟩
  · unfold Params.hintOffset; nlinarith
  · rw [hlen]; unfold Params.hintOffset Params.sigSize; ring
  · rw [hlen]; unfold Params.hintOffset Params.sigSize; omega
  · exact split_blocks σ _ _ _

/-- **`decode_signature` is FIPS 204 `sigDecode`** (Algorithm 27) on every
byte string of the checked length. -/
theorem decodeSig_eq_spec (P : Params) (hP : P.Valid) (σ : List ℕ) (hlen : σ.length = P.sigSize)
    (hb : ∀ x ∈ σ, x < 256) : decodeSig P σ = sigDecode P σ := by
  unfold decodeSig sigDecode
  rw [ite_eq_right (by rw [hlen]; simp), bitlen_gamma1_sub_one P hP]
  simp only
  have htl : (σ.take P.hintOffset).length = P.hintOffset := by
    rw [List.length_take, hlen]; unfold Params.hintOffset Params.sigSize; omega
  have hdec : decodeHint σ P.hintOffset P.k P.omega =
      hintBitUnpack P.k P.omega (σ.drop P.hintOffset) := by
    have := decodeHint_shift (σ.take P.hintOffset) (σ.drop P.hintOffset) P.k P.omega
    rwa [List.take_append_drop, htl] at this
  unfold Params.hintOffset at hdec
  rw [hdec]
  have hz : (List.range P.l).map (fun index => unpackZ P.gamma1 (zBits P.gamma1)
      (sub σ (P.cTildeBytes + index * P.zPackedBytes) P.zPackedBytes)) =
      (List.range P.l).map (fun i => Spec.bitUnpack ((σ.drop (P.cTildeBytes + i * P.zPackedBytes)).take
        P.zPackedBytes) (P.gamma1 - 1) P.gamma1) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    apply unpackZ_eq P.gamma1 hP.2
    · rw [length_sub _ _ _ (by rw [hlen]; unfold Params.sigSize; nlinarith),
        Params.zPackedBytes_eq]
    · exact sub_lt hb _ _
  rw [hz]
  rfl

/-- **Round trip.** `decode_signature (encode_signature c̃ z h) = Ok (c̃, z, h)`. -/
theorem decodeSig_encodeSig (P : Params) (hP : P.Valid) (cTilde : List ℕ) (z : List (List ℤ))
    (h : HintVec) (hin : SigInput P cTilde z h) :
    decodeSig P (encodeSig P cTilde z h) = some (cTilde, z, h) := by
  have hlen := length_encodeSig P cTilde z h hin
  have hzl : ∀ b ∈ z.map (packZ P.gamma1 (zBits P.gamma1)), b.length = P.zPackedBytes := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact length_packZ P p (hin.z_poly p hp).1
  have hfl := length_flatten_blocks _ _ hzl
  simp only [List.length_map, hin.z_len] at hfl
  rw [encodeSig_eq P cTilde z h hin] at hlen ⊢
  unfold decodeSig
  rw [ite_eq_right (by rw [hlen]; simp)]
  simp only
  -- the hint section
  have hdec : decodeHint (cTilde ++ (z.map (packZ P.gamma1 (zBits P.gamma1))).flatten ++
      hintBitPack P.k P.omega h) (P.cTildeBytes + P.l * P.zPackedBytes) P.k P.omega = some h := by
    rw [show P.cTildeBytes + P.l * P.zPackedBytes =
      (cTilde ++ (z.map (packZ P.gamma1 (zBits P.gamma1))).flatten).length by
        simp [hin.cTilde_len, hfl], decodeHint_shift]
    exact decode_encode _ _ h hin.h01 hin.hdom hin.weight
  rw [hdec]
  simp only [Option.some.injEq, Prod.mk.injEq]
  refine ⟨?_, ?_, trivial⟩
  · rw [List.append_assoc]
    exact sub_prefix' [] cTilde _ 0 _ rfl hin.cTilde_len.symm
  · apply List.ext_getElem
    · simp [hin.z_len]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [show P.cTildeBytes + i * P.zPackedBytes = cTilde.length + i * P.zPackedBytes by
        rw [hin.cTilde_len], sub_block _ _ hzl cTilde _ i (by simpa using h2)]
      simp only [List.getElem_map]
      have hmem := List.getElem_mem h2
      exact unpackZ_packZ P.gamma1 hP.2 _ (hin.z_poly _ hmem).1 (hin.z_poly _ hmem).2

/-- **Canonicity (non-malleability of the signature encoding).** If
`decode_signature σ = Ok (c̃, z, h)` then `encode_signature c̃ z h = σ`: every
byte of an accepted signature is determined by the decoded value. -/
theorem encodeSig_decodeSig (P : Params) (hP : P.Valid) (σ : List ℕ) (hb : ∀ x ∈ σ, x < 256)
    (cTilde : List ℕ) (z : List (List ℤ)) (h : HintVec)
    (hdec : decodeSig P σ = some (cTilde, z, h)) : encodeSig P cTilde z h = σ := by
  have hlen : σ.length = P.sigSize := by
    unfold decodeSig at hdec
    by_contra hne
    rw [ite_eq_left hne] at hdec
    cases hdec
  obtain ⟨-, htot, -, hsplit⟩ := decodeSig_offsets P σ hlen
  have htl : (σ.take P.hintOffset).length = P.hintOffset := by
    rw [List.length_take, hlen]; unfold Params.hintOffset Params.sigSize; omega
  have hhint : decodeHint σ P.hintOffset P.k P.omega =
      hintBitUnpack P.k P.omega (σ.drop P.hintOffset) := by
    have := decodeHint_shift (σ.take P.hintOffset) (σ.drop P.hintOffset) P.k P.omega
    rwa [List.take_append_drop, htl] at this
  unfold decodeSig at hdec
  rw [ite_eq_right (by rw [hlen]; simp)] at hdec
  simp only at hdec
  unfold Params.hintOffset at hhint
  rw [hhint] at hdec
  cases hh : hintBitUnpack P.k P.omega (σ.drop (P.cTildeBytes + P.l * P.zPackedBytes)) with
  | none => rw [hh] at hdec; cases hdec
  | some h' =>
    rw [hh] at hdec
    simp only [Option.some.injEq, Prod.mk.injEq] at hdec
    obtain ⟨hc, hz, hh'⟩ := hdec
    subst hc hz hh'
    have hylen : (σ.drop (P.cTildeBytes + P.l * P.zPackedBytes)).length = P.omega + P.k := by
      simp [hlen, Params.sigSize]; omega
    have hyb : ∀ x ∈ σ.drop (P.cTildeBytes + P.l * P.zPackedBytes), x < 256 :=
      fun x hx => hb x (List.mem_of_mem_drop hx)
    have henc := encode_decode _ _ _ hylen hyb _ hh
    obtain ⟨h01, hdom⟩ := decoded_valid _ _ _ hyb _ hh
    have hblocks : ∀ i < P.l, (sub σ (P.cTildeBytes + i * P.zPackedBytes) P.zPackedBytes).length =
        32 * zBits P.gamma1 := by
      intro i hi
      rw [length_sub _ _ _ (by rw [hlen]; unfold Params.sigSize; nlinarith), Params.zPackedBytes_eq]
    have hin : SigInput P (sub σ 0 P.cTildeBytes)
        ((List.range P.l).map (fun index => unpackZ P.gamma1 (zBits P.gamma1)
          (sub σ (P.cTildeBytes + index * P.zPackedBytes) P.zPackedBytes))) h' := by
      refine ⟨length_sub _ _ _ (by rw [hlen]; unfold Params.sigSize; omega), sub_lt hb _ _,
        by simp, ?_, h01, hdom, weight_le_of_decode _ _ _ hyb _ hh⟩
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      rw [List.mem_range] at hi
      refine ⟨?_, unpackZ_range P.gamma1 hP.2 _ (hblocks i hi) (sub_lt hb _ _)⟩
      have hreg := unpackCodes_regroup (bits := zBits P.gamma1) (gamma1_cases P.gamma1 hP.2).2.2
        ⟨256, by rw [hblocks i hi]; ring⟩ (sub_lt hb (P.cTildeBytes + i * P.zPackedBytes)
          P.zPackedBytes)
      have := hreg.length
      rw [hblocks i hi] at this
      unfold unpackZ
      rw [List.length_map]
      have h1 := (gamma1_cases P.gamma1 hP.2).2.2
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < zBits P.gamma1) (by rw [this]; ring)
    rw [encodeSig_eq P _ _ _ hin, henc, List.map_map]
    have hpack : ((List.range P.l).map ((packZ P.gamma1 (zBits P.gamma1)) ∘ fun index =>
        unpackZ P.gamma1 (zBits P.gamma1)
          (sub σ (P.cTildeBytes + index * P.zPackedBytes) P.zPackedBytes))) =
        (List.range P.l).map (fun i => sub σ (P.cTildeBytes + i * P.zPackedBytes) P.zPackedBytes) := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      exact packZ_unpackZ P.gamma1 hP.2 _ (hblocks i hi) (sub_lt hb _ _)
    rw [hpack]
    unfold Params.hintOffset at hsplit
    exact hsplit.symm

/-! ## Verification keys -/

/-- `encode_verification_key rho t1` (lines 471–472):
`rho ^ String.concat "" (Array.to_list (Array.map pack_t1 t1))`. -/
def encodeVk (rho : List ℕ) (t1 : List (List ℕ)) : List ℕ := rho ++ (t1.map packT1).flatten

/-- `decode_verification_key octets` (lines 474–486). -/
def decodeVk (P : Params) (octets : List ℕ) : Option (List ℕ × List (List ℕ)) :=
  if octets.length ≠ P.vkSize then none
  else some (sub octets 0 32,
    (List.range P.k).map (fun index => unpackT1 (sub octets (32 + index * 320) 320)))

/-- FIPS 204 Algorithm 22, `pkEncode(ρ, t₁)`:
`pk ← ρ; for i < k: pk ← pk ‖ SimpleBitPack(t₁[i], 2^{bitlen(q−1)−d} − 1)`. -/
def pkEncode (P : Params) (rho : List ℕ) (t1 : List (List ℕ)) : List ℕ :=
  (List.range P.k).foldl
    (fun pk i => pk ++ Spec.simpleBitPack (t1.getD i []) (2 ^ (Spec.bitlen (q - 1) - 13) - 1)) rho

theorem encodeVk_eq_spec (P : Params) (rho : List ℕ) (t1 : List (List ℕ)) (ht : t1.length = P.k)
    (hpoly : ∀ p ∈ t1, p.length = 256 ∧ ∀ x ∈ p, x < 2 ^ 10) :
    encodeVk rho t1 = pkEncode P rho t1 := by
  unfold encodeVk pkEncode
  rw [bitlen_q_sub_one, Spec.foldl_append_range, ← ht]
  have := Spec.flatMap_range_getD' t1 [] (fun p => Spec.simpleBitPack p (2 ^ (23 - 13) - 1))
  rw [this, List.flatMap_def, List.map_congr_left (fun p hp =>
    packT1_eq p (hpoly p hp).1 (hpoly p hp).2)]

theorem decodeVk_encodeVk (P : Params) (rho : List ℕ) (t1 : List (List ℕ)) (hrho : rho.length = 32)
    (ht : t1.length = P.k) (hpoly : ∀ p ∈ t1, p.length = 256 ∧ ∀ x ∈ p, x < 2 ^ 10) :
    decodeVk P (encodeVk rho t1) = some (rho, t1) := by
  have hbl : ∀ b ∈ t1.map packT1, b.length = 320 := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    unfold packT1; rw [length_packCodes, (hpoly p hp).1]
  have hfl := length_flatten_blocks _ _ hbl
  simp only [List.length_map, ht] at hfl
  unfold decodeVk encodeVk
  rw [ite_eq_right (by simp only [List.length_append, hfl, hrho, Params.vkSize]; omega)]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · have := sub_prefix [] rho (t1.map packT1).flatten
    simpa [hrho] using this
  · apply List.ext_getElem
    · simp [ht]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      have := sub_block (t1.map packT1) 320 hbl rho [] i (by simpa using h2)
      rw [List.append_nil, hrho] at this
      rw [this, List.getElem_map]
      have hmem := List.getElem_mem h2
      exact unpackT1_packT1 _ (hpoly _ hmem).1 (hpoly _ hmem).2

/-- Every byte string of length `32 + 320k` is a verification key, and it
re-encodes to itself. -/
theorem encodeVk_decodeVk (P : Params) (octets : List ℕ) (hlen : octets.length = P.vkSize)
    (hb : ∀ x ∈ octets, x < 256) :
    ∃ rho t1, decodeVk P octets = some (rho, t1) ∧ encodeVk rho t1 = octets := by
  unfold decodeVk
  rw [ite_eq_right (by simp [hlen])]
  refine ⟨_, _, rfl, ?_⟩
  unfold encodeVk
  rw [List.map_map]
  have hpack : (List.range P.k).map (packT1 ∘ fun index => unpackT1 (sub octets (32 + index * 320) 320)) =
      (List.range P.k).map (fun i => sub octets (32 + i * 320) 320) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    exact packT1_unpackT1 _ (length_sub _ _ _ (by rw [hlen]; unfold Params.vkSize; nlinarith))
      (sub_lt hb _ _)
  rw [hpack]
  have := split_blocks octets 32 P.k 320
  rw [List.drop_eq_nil_of_le (by rw [hlen]; unfold Params.vkSize; omega), List.append_nil] at this
  exact this.symm

end OcamlPq.Encoding.Mldsa
