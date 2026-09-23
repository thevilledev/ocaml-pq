import OcamlPq.MLKEMAlg.Keys

/-!
# Portability and bounds of the composition layer (obligation 7)

The `int` values computed in lib/mlkem_engine.ml lines 292-525 outside the
sampling loops. The loops themselves are covered by `sampleCbd_portable`,
`draw_portable`, `sampleNtt_portable` and `ctEqual_portable`. For the three
parameter sets:

* every byte passed to `Char.unsafe_chr` is in `[0, 256)`: the domain byte `k`
  of `G(d‖k)`, the `sample_ntt` indices, and every `sample_cbd` nonce (at most
  `2k`);
* every offset and length passed to `decode_12`, `decode_compressed`,
  `String.sub` and `Bytes.blit_string` stays within its string, so none of
  these calls raises `Invalid_argument` or reads out of bounds;
* every such value is a portable `int` (below `2^30`).
-/

namespace OcamlPq.MLKEMAlg

theorem composition_bounds (P : Params) (hP : P.Valid) :
    -- `Char.unsafe_chr k` in `keygen_internal`
    P.k < 256 ∧
    -- nonces: `0 … 2k-1` in `keygen_internal`, `0 … 2k` in `pke_encrypt`
    2 * P.k < 256 ∧
    -- `decode_12` in `parse_ek` / `decapsulation_key_of_expanded`, and
    -- `blit_string (encode_12 _) 0 out (i * 384) 384`
    (∀ i < P.k, i * 384 + 384 ≤ P.ekSize ∧ i * 384 + 384 ≤ P.dkSize) ∧
    -- `String.sub encoded (k * 384) 32` in `parse_ek`, `blit_string rho` in `encode_ek`
    P.k * 384 + 32 = P.ekSize ∧
    -- `String.sub encoded ek_offset encapsulation_key_size`, the `h` and `z`
    -- slices of `decapsulation_key_of_expanded`, and the blits of
    -- `decapsulation_key_to_expanded`
    P.k * 384 + P.ekSize + 32 + 32 = P.dkSize ∧
    -- `decode_compressed du ciphertext (i * encoding_size_u)` and the blits of `pke_encrypt`
    (∀ i < P.k, i * P.encodingSizeU + 32 * P.du ≤ P.ctSize) ∧
    P.k * P.encodingSizeU + 32 * P.dv = P.ctSize ∧
    -- every size is a portable `int`
    Portable (P.ekSize : ℤ) ∧ Portable (P.dkSize : ℤ) ∧ Portable (P.ctSize : ℤ) ∧
    Portable ((P.k * 384 + P.ekSize + 32 : ℕ) : ℤ) := by
  have hek := P.ekSize_eq
  have hdk := P.dkSize_eq
  have hct := P.ctSize_eq
  have hu := P.encodingSizeU_eq
  obtain ⟨-, hk, -, -, -, hdu, -, hdv⟩ := hP.bounds
  refine ⟨by omega, by omega, fun i hi => ⟨by nlinarith, by nlinarith⟩, by omega, by omega,
    fun i hi => by rw [hct, hu]; nlinarith, by rw [hct, hu],
    Portable.of_nat_lt (by omega), Portable.of_nat_lt (by omega),
    Portable.of_nat_lt (by rw [hct]; nlinarith), Portable.of_nat_lt (by omega)⟩

/-- `String.sub g 0 32` and `String.sub g 32 32` on a SHA3-512 output
    (`keygen_internal`, `encapsulate_internal`, `decapsulate`) are in bounds,
    as is `String.sub seed 32 32` on a 64-byte seed. -/
theorem sha3_512_sub_bounds (K : Keccak) (x : Bytes) :
    0 + 32 ≤ (K.sha3_512 x).length ∧ 32 + 32 ≤ (K.sha3_512 x).length := by
  rw [K.sha3_512_length]; omega

end OcamlPq.MLKEMAlg
