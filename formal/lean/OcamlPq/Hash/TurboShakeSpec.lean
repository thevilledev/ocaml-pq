import OcamlPq.Hash.KeccakSpec

/-!
# RFC 9861 (TurboSHAKE), transcribed

An independent transcription of Section 2.2 of RFC 9861 (KangarooTwelve and
TurboSHAKE), written from the standard and not from the code:

* the permutation `KP` is `KECCAK-p[1600, n_r = 12]` of FIPS 202 §3.3, the
  last 12 rounds of `KECCAK-f[1600]`;
* the input `M′ = M ‖ D` is padded with `00` bytes to a multiple of the rate,
  unless it already is one, and `80` is XORed into its last byte;
* the state starts all-zero; each block of the padded input is XORed into the
  first `rate` bytes of the state and followed by `KP`; the output is the first
  `rate` bytes of the state, with `KP` applied between output blocks, truncated
  to `L` bytes.

The last point is FIPS 202 Algorithm 8, `SPONGE`, run on an input that is
already padded, so the transcription uses `FIPS202.sponge` with a padding rule
that appends nothing. TurboSHAKE128 has a rate of 168 bytes and TurboSHAKE256
of 136 bytes.

Byte strings are `List UInt8`. The state and the blocks are bit strings in the
order of FIPS 202 Appendix B.1, each byte least significant bit first. RFC 9861
reads a lane as a 64-bit little-endian word, which is the same order. RFC 9861
also notes that this padding "equivalently implements the pad10*1 rule";
`TurboShake.turboSHAKE_eq_pad101` proves it.
-/

namespace OcamlPq.Hash.RFC9861

open FIPS202

/-- §2.2: `KP` is `KECCAK-p[1600, n_r = 12]`. -/
def KP (S : Bits) : Bits := KeccakP 12 S

/-- §2.2: `M′ = M ‖ D`; if `|M′|` is not a multiple of the rate `R`, zero
bytes are appended to make it one; then `80` is XORed to its last byte. -/
def padInput (R : ℕ) (M : List UInt8) (D : UInt8) : List UInt8 :=
  let M' := M ++ [D]
  let M' := if M'.length % R = 0 then M' else M' ++ List.replicate (R - M'.length % R) 0
  M'.modify (M'.length - 1) (· ^^^ 0x80)

/-- The input is padded at the byte level before the sponge sees it, so the
sponge's own padding rule appends nothing. -/
def noPad (_ _ : ℕ) : Bits := []

/-- §2.2: the sponge over `KP` with a rate of `R` bytes, absorbing
`padInput R M D` and squeezing `L` bytes. -/
def turboSHAKE (R : ℕ) (M : List UInt8) (D : UInt8) (L : ℕ) : Bits :=
  sponge KP noPad (8 * R) (bytesToBits (padInput R M D)) (8 * L)

/-- §2.2: `TurboSHAKE128(M, D, L)`, rate 168 bytes, capacity 32. -/
def TurboSHAKE128 (M : List UInt8) (D : UInt8) (L : ℕ) : Bits := turboSHAKE 168 M D L

/-- §2.2: `TurboSHAKE256(M, D, L)`, rate 136 bytes, capacity 64. -/
def TurboSHAKE256 (M : List UInt8) (D : UInt8) (L : ℕ) : Bits := turboSHAKE 136 M D L

end OcamlPq.Hash.RFC9861
