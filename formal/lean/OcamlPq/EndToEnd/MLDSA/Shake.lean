import OcamlPq.EndToEnd.MLDSA.Adapters

/-!
# SHAKE128 / SHAKE256 as `MLDSAAlg.XOF`s

`MLDSAAlg` treats SHAKE as an abstract extendable-output function
`XOF = Bytes → ℕ → Byte` (an infinite output stream per input), with
`XOF.squeeze H x L` the first `L` bytes. This file instantiates it twice:

* `ocamlShake128`, `ocamlShake256`: from the Hash area's model of
  `Mldsa_keccak.shake128/shake256` (`Hash.Keccak.shake128 L x`, textually the
  code of `lib/keccak.ml`, see `OcamlPq/Hash.lean`). Byte `i` of the stream is
  byte `i` of the output of length `i + 1`. `ocamlShake128_squeeze` shows that
  `XOF.squeeze` is exactly the OCaml call `shake128 ~output_length:L x`; this
  uses the Hash area's prefix consistency `shake128_prefix`/`shake256_prefix`.
* `fipsShake128`, `fipsShake256`: from the FIPS 202 specification
  (`Hash.FIPS202.SHAKE128/SHAKE256` on bit strings, FIPS 202 Appendix B.1 bit
  order). `fipsShake128_squeeze_bits` states that `XOF.squeeze` of these is
  `SHAKE128(M, 8L)` of FIPS 202.

`fipsShake128_eq`/`fipsShake256_eq` (from the Hash area's `shake128_eq`,
`shake256_eq`) identify the two, so the end-to-end theorems can state the
OCaml side with the OCaml SHAKE and the FIPS 204 side with FIPS 202 SHAKE.
-/

namespace OcamlPq.EndToEnd.MLDSA

open OcamlPq.MLDSAAlg
open OcamlPq.Hash

/-! ## The OCaml SHAKE as a stream -/

/-- The output stream of an OCaml SHAKE function `sh ~output_length input`:
    byte `i` is byte `i` of the output of length `i + 1`. -/
def keccakXOF (sh : ℕ → List UInt8 → List UInt8) : XOF :=
  fun input i => u8ToByte ((sh (i + 1) (bytesToU8 input)).getD i 0)

/-- `Mldsa_keccak.shake128` as an `XOF`. -/
def ocamlShake128 : XOF := keccakXOF Keccak.shake128

/-- `Mldsa_keccak.shake256` as an `XOF`. -/
def ocamlShake256 : XOF := keccakXOF Keccak.shake256

theorem keccakXOF_squeeze (sh : ℕ → List UInt8 → List UInt8)
    (hlen : ∀ L M, (sh L M).length = L)
    (hpre : ∀ L L' M, L ≤ L' → sh L M = (sh L' M).take L) (input : Bytes) (L : ℕ) :
    (keccakXOF sh).squeeze input L = u8ToBytes (sh L (bytesToU8 input)) := by
  apply List.ext_getElem (by simp [u8ToBytes, hlen])
  intro i h1 h2
  have hi : i < L := by simpa using h1
  simp only [XOF.squeeze, List.getElem_map, List.getElem_range, keccakXOF, u8ToBytes]
  congr 1
  rw [hpre (i + 1) L _ (by omega), List.getD_eq_getElem _ _ (by simp [hlen]; omega),
    List.getElem_take]

/-- **The OCaml call `Mldsa_keccak.shake128 ~output_length:L x` is
    `XOF.squeeze ocamlShake128 x L`.** -/
theorem ocamlShake128_squeeze (input : Bytes) (L : ℕ) :
    ocamlShake128.squeeze input L = u8ToBytes (Keccak.shake128 L (bytesToU8 input)) :=
  keccakXOF_squeeze _ Keccak.shake128_length (fun L L' M h => Keccak.shake128_prefix L L' h M)
    input L

/-- **The OCaml call `Mldsa_keccak.shake256 ~output_length:L x` is
    `XOF.squeeze ocamlShake256 x L`.** -/
theorem ocamlShake256_squeeze (input : Bytes) (L : ℕ) :
    ocamlShake256.squeeze input L = u8ToBytes (Keccak.shake256 L (bytesToU8 input)) :=
  keccakXOF_squeeze _ Keccak.shake256_length (fun L L' M h => Keccak.shake256_prefix L L' h M)
    input L

/-! ## FIPS 202 SHAKE as a stream -/

/-- Eight bits, least significant first (FIPS 202 Appendix B.1), as a byte. -/
def bitsToByte (bs : List Bool) : Byte := byteOfNat (bs.foldr (fun b acc => b.toNat + 2 * acc) 0)

/-- The output stream of a FIPS 202 extendable-output function
    `SHAKE : Bits → ℕ → Bits`: byte `i` is bits `8i … 8i + 7` of
    `SHAKE(M, 8(i + 1))`. -/
def fipsXOF (SHAKE : FIPS202.Bits → ℕ → FIPS202.Bits) : XOF :=
  fun input i => bitsToByte
    (((SHAKE (FIPS202.bytesToBits (bytesToU8 input)) (8 * (i + 1))).drop (8 * i)).take 8)

/-- FIPS 202 `SHAKE128` as an `XOF` (`G` of FIPS 204). -/
def fipsShake128 : XOF := fipsXOF FIPS202.SHAKE128

/-- FIPS 202 `SHAKE256` as an `XOF` (`H` of FIPS 204). -/
def fipsShake256 : XOF := fipsXOF FIPS202.SHAKE256

theorem foldr_testBit (n x : ℕ) :
    ((List.range n).map fun j => x.testBit j).foldr (fun b acc => b.toNat + 2 * acc) 0 =
      x % 2 ^ n := by
  induction n generalizing x with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.foldr_cons]
    have e : ((fun j => x.testBit j) ∘ Nat.succ) = fun j => (x / 2).testBit j := by
      funext j; simp [Function.comp, Nat.testBit_div_two]
    rw [e, ih, Nat.testBit_zero]
    have h1 : x % 2 ^ (n + 1) = x % 2 + 2 * (x / 2 % 2 ^ n) := by
      rw [pow_succ', Nat.mod_mul]
    rw [h1]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem bytesToBits_block (l : List UInt8) (i : ℕ) (hi : i < l.length) :
    ((FIPS202.bytesToBits l).drop (8 * i)).take 8 = (List.range 8).map fun j => l[i].toNat.testBit j := by
  have hsplit : l = l.take i ++ (l[i] :: l.drop (i + 1)) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  conv_lhs => rw [hsplit]
  rw [bytesToBits_append, bytesToBits_cons,
    List.drop_append_of_le_length (by simp; omega)]
  rw [List.drop_of_length_le (by simp)]
  simp

/-- **FIPS 202 SHAKE128 and the OCaml `shake128` give the same stream**
    (from the Hash area's `Keccak.shake128_eq`). -/
theorem fipsShake128_eq : fipsShake128 = ocamlShake128 := by
  funext input i
  simp only [fipsShake128, fipsXOF, ocamlShake128, keccakXOF]
  rw [← Keccak.shake128_eq]
  have hl := Keccak.shake128_length (i + 1) (bytesToU8 input)
  rw [bytesToBits_block _ i (by omega), List.getD_eq_getElem _ _ (by omega)]
  unfold bitsToByte u8ToByte
  rw [foldr_testBit]
  congr 1
  exact Nat.mod_eq_of_lt (by simpa using UInt8.toNat_lt _)

/-- **FIPS 202 SHAKE256 and the OCaml `shake256` give the same stream**
    (from the Hash area's `Keccak.shake256_eq`). -/
theorem fipsShake256_eq : fipsShake256 = ocamlShake256 := by
  funext input i
  simp only [fipsShake256, fipsXOF, ocamlShake256, keccakXOF]
  rw [← Keccak.shake256_eq]
  have hl := Keccak.shake256_length (i + 1) (bytesToU8 input)
  rw [bytesToBits_block _ i (by omega), List.getD_eq_getElem _ _ (by omega)]
  unfold bitsToByte u8ToByte
  rw [foldr_testBit]
  congr 1
  exact Nat.mod_eq_of_lt (by simpa using UInt8.toNat_lt _)

/-- **`H(x, L)` of FIPS 204 is FIPS 202 `SHAKE256(x, 8L)`** for the stream
    `fipsShake256`. -/
theorem fipsShake256_squeeze_bits (input : Bytes) (L : ℕ) :
    FIPS202.bytesToBits (bytesToU8 (fipsShake256.squeeze input L)) =
      FIPS202.SHAKE256 (FIPS202.bytesToBits (bytesToU8 input)) (8 * L) := by
  rw [fipsShake256_eq, ocamlShake256_squeeze, bytesToU8_u8ToBytes, Keccak.shake256_eq]

/-- **`G(x, L)` of FIPS 204 is FIPS 202 `SHAKE128(x, 8L)`** for the stream
    `fipsShake128`. -/
theorem fipsShake128_squeeze_bits (input : Bytes) (L : ℕ) :
    FIPS202.bytesToBits (bytesToU8 (fipsShake128.squeeze input L)) =
      FIPS202.SHAKE128 (FIPS202.bytesToBits (bytesToU8 input)) (8 * L) := by
  rw [fipsShake128_eq, ocamlShake128_squeeze, bytesToU8_u8ToBytes, Keccak.shake128_eq]

end OcamlPq.EndToEnd.MLDSA
