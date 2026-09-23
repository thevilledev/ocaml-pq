import Mathlib
import OcamlPq.Common.Int

/-!
# Byte strings, XOFs and the byte-level helpers of `mldsa_engine.ml`

OCaml `string`s are modelled as `List Byte` with `Byte := Fin 256`.

SHAKE128 and SHAKE256 are treated as abstract extendable-output functions:
an `XOF` maps an input byte string to an infinite byte stream `ℕ → Byte`,
and `Mldsa_keccak.shake* ~output_length:L input` is the first `L` bytes of
that stream (`XOF.squeeze`). Prefix consistency (a longer output extends a
shorter one) is therefore built into the model; it is the only property of
SHAKE the sampling proofs use. The FIPS 204 incremental interface
(`H.Init`, `H.Absorb`, `H.Squeeze`) is modelled by reading the same stream
sequentially, with the XOF context represented by the number of bytes
already squeezed.
-/

namespace OcamlPq.MLDSAAlg

/-- An OCaml `char` / a byte. -/
abbrev Byte := Fin 256

/-- An OCaml `string`. -/
abbrev Bytes := List Byte

/-- An extendable-output function (SHAKE128 or SHAKE256): the infinite output
    stream for each input. -/
abbrev XOF := Bytes → ℕ → Byte

/-- `Mldsa_keccak.shake128/shake256 ~output_length:L input`
    (`mldsa/mldsa_keccak.ml`, lines 117–118): the first `L` bytes of the
    stream. -/
def XOF.squeeze (H : XOF) (input : Bytes) (L : ℕ) : Bytes :=
  (List.range L).map (H input)

@[simp] theorem XOF.length_squeeze (H : XOF) (input : Bytes) (L : ℕ) :
    (H.squeeze input L).length = L := by
  simp [XOF.squeeze]

/-- `get_u8 string index` (`mldsa_engine.ml`, line 160):
    `Char.code (String.unsafe_get string index)`. The model returns `0`
    out of bounds; every use is proved to be in bounds. -/
def getU8 (s : Bytes) (i : ℕ) : ℕ := (s.getD i 0).val

theorem getU8_lt (s : Bytes) (i : ℕ) : getU8 s i < 256 := (s.getD i 0).isLt

theorem getU8_squeeze {H : XOF} {x : Bytes} {L i : ℕ} (h : i < L) :
    getU8 (H.squeeze x L) i = (H x i).val := by
  unfold getU8 XOF.squeeze
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

/-- `Char.unsafe_chr value` for a byte value; reduces modulo 256, which the
    uses below never need (each call site is proved to pass a value `< 256`). -/
def byteOfNat (v : ℕ) : Byte := ⟨v % 256, Nat.mod_lt _ (by norm_num)⟩

theorem byteOfNat_val_of_lt {v : ℕ} (h : v < 256) : (byteOfNat v).val = v := by
  simp [byteOfNat, Nat.mod_eq_of_lt h]

/-- `String.make 1 (Char.unsafe_chr v)`. -/
def byteString (v : ℕ) : Bytes := [byteOfNat v]

/-- `u16_le value` (`mldsa_engine.ml`, lines 165–169). -/
def u16le (value : ℕ) : Bytes :=
  [byteOfNat (value &&& 0xff), byteOfNat ((value >>> 8) &&& 0xff)]

theorem land_0xff (x : ℕ) : x &&& 0xff = x % 256 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 8
  norm_num at this; exact this

theorem lsr_8 (x : ℕ) : x >>> 8 = x / 256 := by
  rw [Nat.shiftRight_eq_div_pow]

/-- Both bytes written by `u16_le` are already in `[0, 255]`, so
    `Char.unsafe_chr` is exact. -/
theorem u16le_bytes_lt (value : ℕ) :
    value &&& 0xff < 256 ∧ (value >>> 8) &&& 0xff < 256 := by
  simp only [land_0xff]; omega

/-- FIPS 204 Algorithm 11, `IntegerToBytes(x, α)`: for `i` from `0` to
    `α − 1`, `y[i] ← x mod 256; x ← ⌊x / 256⌋`. -/
def integerToBytes : ℕ → ℕ → Bytes
  | _, 0 => []
  | x, α + 1 => byteOfNat (x % 256) :: integerToBytes (x / 256) α

/-- `u16_le` is `IntegerToBytes(·, 2)`. (Both keep only `v mod 2^16`; FIPS 204
    only applies `IntegerToBytes(x, 2)` to `x < 2^16`, which `SignLoop` proves
    for every nonce.) -/
theorem u16le_eq_integerToBytes (v : ℕ) : u16le v = integerToBytes v 2 := by
  simp only [u16le, integerToBytes, land_0xff, lsr_8]

/-- `u16_le` is injective on `[0, 2^16)`: distinct nonces give distinct
    XOF inputs. -/
theorem u16le_inj {a b : ℕ} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) (h : u16le a = u16le b) :
    a = b := by
  simp only [u16le, land_0xff, lsr_8, byteOfNat, List.cons.injEq, Fin.mk.injEq, and_true] at h
  omega

/-- Beyond `2^16` the helper silently truncates, so every caller must keep
    its argument below `2^16` (proved for all call sites in `SignLoop`). -/
theorem u16le_mod (v : ℕ) : u16le v = u16le (v % 2 ^ 16) := by
  simp only [u16le, land_0xff, lsr_8]
  simp only [byteOfNat, List.cons.injEq, Fin.mk.injEq, and_true]
  constructor <;> omega

/-- `IntegerToBytes(x, 1)` is the single byte `x` for `x < 256`. -/
theorem integerToBytes_one {x : ℕ} (h : x < 256) : integerToBytes x 1 = byteString x := by
  simp [integerToBytes, byteString, byteOfNat, Nat.mod_eq_of_lt h]

/-- `String.sub s offset length` (`mldsa_engine.ml`, line 163). -/
def sub (s : Bytes) (offset length : ℕ) : Bytes := (s.drop offset).take length

theorem length_sub {s : Bytes} {offset length : ℕ} (h : offset + length ≤ s.length) :
    (sub s offset length).length = length := by
  simp [sub]; omega

/-- FIPS 204 Algorithm 12, `BytesToBits`, read at bit index `k`: bit `j` of
    byte `i` is `y[8i + j] = ⌊C[i] / 2^j⌋ mod 2` (the loop of Algorithm 12
    sets `y[8i + j] ← C′[i] mod 2; C′[i] ← ⌊C′[i] / 2⌋`). -/
def bytesToBits (C : Bytes) (k : ℕ) : ℕ := (C.getD (k / 8) 0).val / 2 ^ (k % 8) % 2

theorem bytesToBits_le_one (C : Bytes) (k : ℕ) : bytesToBits C k ≤ 1 := by
  unfold bytesToBits; omega

end OcamlPq.MLDSAAlg
