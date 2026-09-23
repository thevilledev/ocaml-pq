import OcamlPq.Common.Int
import OcamlPq.Hash.KeccakConstants
import OcamlPq.Hash.Sha2Model

/-!
# Safety of the hash code: indices, shift amounts, `int` ranges

For each OCaml function of `lib/keccak.ml` and `slhdsa/slhdsa_hash.ml`
lines 120–340 this file lists every `int` expression that indexes an array or
string, is a shift amount, or is passed to `Bytes`/`String` functions, and
proves, over all values the loops can produce:

* array/string indices are in bounds (this matters most for
  `String.unsafe_get`/`Bytes.unsafe_set`, which are not checked at run time);
* `Int32`/`Int64` shift amounts are in `[0, 31]`/`[0, 63]` (OCaml leaves other
  amounts unspecified);
* `Bytes.create`/`Bytes.make`/`String.make` get non-negative lengths and
  `String.sub`/`Bytes.blit` are in bounds, so no `Invalid_argument` is raised
  for valid inputs;
* every `int` intermediate is non-negative and bounded by the input and output
  lengths plus a small constant, hence `Portable` whenever those lengths are
  below `2^30 − 144`, and never wraps on 64-bit (where strings are shorter
  than `2^57`).

All the loop variables are non-negative, so the models' `ℕ` arithmetic is the
OCaml `int` arithmetic as long as nothing wraps, which these bounds exclude.
-/

namespace OcamlPq.Hash.Safety

open Keccak Sha2

/-! ## `lib/keccak.ml` -/

/-- `permute` (lines 30–66): every index into `a`, `b` (25 lanes), `c`, `d`
(5 lanes), `rotation` (25) and `round_constants` (24) is in bounds. -/
theorem permute_indices : ∀ x : Fin 5, ∀ y : Fin 5, ∀ round : Fin 24,
    x.val + 20 < 25 ∧ (x.val + 4) % 5 < 5 ∧ (x.val + 1) % 5 < 5 ∧ x.val + 5 * y.val < 25 ∧
    y.val + 5 * ((2 * x.val + 3 * y.val) % 5) < 25 ∧
    (x.val + 1) % 5 + 5 * y.val < 25 ∧ (x.val + 2) % 5 + 5 * y.val < 25 ∧
    round.val < roundConstants.size ∧ x.val + 5 * y.val < Keccak.rotation.size := by
  decide

/-- `rotl x n` (lines 26–28) is only called with `n = 1` or `n = rotation.(i)`;
for each, either `n = 0` (no shift performed) or both `shift_left x n` and
`shift_right_logical x (64 − n)` have amounts in `[1, 63]`. -/
theorem rotl_shift_amounts : ∀ i : Fin 25,
    Keccak.rotation[i.val]! = 0 ∨ (1 ≤ Keccak.rotation[i.val]! ∧ Keccak.rotation[i.val]! ≤ 63 ∧
      1 ≤ 64 - Keccak.rotation[i.val]! ∧ 64 - Keccak.rotation[i.val]! ≤ 63) := by
  decide

/-- `load64_le`/`store64_le` (lines 68–80): shift amounts `8 i ≤ 56`. -/
theorem load_store_shifts : ∀ i : Fin 8, 8 * i.val ≤ 56 := by decide

/-- `xor_block state block` (lines 82–85) with `|block| ≤ 200`: every
`state.(i)` is in bounds and every `String.unsafe_get block (8 i + k)` of
`load64_le` is in bounds. -/
theorem xorBlock_indices (len : ℕ) (hlen : len ≤ 200) (i k : ℕ) (hi : i < len / 8) (hk : k < 8) :
    i < 25 ∧ 8 * i + k < len := by
  omega

/-- The squeeze loop's `store64_le block (8 i) state.(i)` for `i < rate / 8`
(lines 107–109): `state.(i)` and every `Bytes.unsafe_set block (8 i + k)` are
in bounds (`|block| = rate ≤ 200`). -/
theorem squeeze_store_indices (rate : ℕ) (hr : rate ≤ 200) (i k : ℕ) (hi : i < rate / 8)
    (hk : k < 8) : i < 25 ∧ 8 * i + k < rate := by
  omega

/-- The rates used, and the constant bytes stored with `Char.unsafe_chr`. -/
theorem sponge_constants : ∀ rate ∈ [168, 136, 72], ∀ suffix ∈ [0x06, 0x1f],
    0 < rate ∧ rate % 8 = 0 ∧ rate ≤ 200 ∧ suffix < 256 ∧ suffix ||| 0x80 < 256 ∧
    0x80 < 256 := by
  decide

/-- The `int` values of `sponge` (lines 87–115), for input length `len` and
`output_length = L ≥ 0`: `String.sub input (block·rate) rate` and
`Bytes.blit_string input (full·rate) tail 0 rem` are in bounds,
`Bytes.set tail rem` and `Bytes.get/set tail (rate−1)` are in bounds, every
squeeze iteration has `1 ≤ take ≤ rate` and blits inside `out`, and every
intermediate is at most `max len L + rate`. -/
theorem sponge_ints (rate len L : ℕ) (hr : 0 < rate) :
    (∀ block < len / rate, block * rate + rate ≤ len) ∧
    len / rate * rate + len % rate = len ∧ len % rate < rate ∧ rate - 1 < rate ∧
    (∀ produced < L, 1 ≤ min rate (L - produced) ∧ min rate (L - produced) ≤ rate ∧
      produced + min rate (L - produced) ≤ L) := by
  refine ⟨fun block hb => ?_, Nat.div_add_mod' len rate, Nat.mod_lt _ hr, by omega,
    fun produced hp => ⟨by omega, by omega, by omega⟩⟩
  have := Nat.mul_le_mul_right rate (show block + 1 ≤ len / rate by omega)
  have := Nat.div_mul_le_self len rate
  rw [Nat.add_mul, Nat.one_mul] at *
  omega

/-- Hence all `int` intermediates of `sponge` are `Portable` when the input and
output lengths are below `2^30 − 200`. -/
theorem sponge_portable (rate len L : ℕ) (hr : 0 < rate) (hr200 : rate ≤ 200)
    (hlen : len < 2 ^ 30 - 200) (hL : L < 2 ^ 30 - 200) :
    Portable ((len / rate : ℕ) : ℤ) ∧ Portable ((len / rate * rate : ℕ) : ℤ) ∧ Portable ((len % rate : ℕ) : ℤ) ∧
    Portable ((rate - 1 : ℕ) : ℤ) ∧ (∀ block < len / rate, Portable ((block * rate : ℕ) : ℤ)) ∧
    (∀ produced ≤ L, Portable ((produced + min rate (L - produced) : ℕ) : ℤ) ∧
      Portable ((L - produced : ℕ) : ℤ)) := by
  have h1 := Nat.div_le_self len rate
  have h2 := Nat.div_mul_le_self len rate
  have h3 := Nat.mod_lt len hr
  refine ⟨Portable.of_nat_lt (by omega), Portable.of_nat_lt (by omega),
    Portable.of_nat_lt (by omega), Portable.of_nat_lt (by omega), fun block hb => ?_,
    fun produced hp => ⟨Portable.of_nat_lt (by omega), Portable.of_nat_lt (by omega)⟩⟩
  apply Portable.of_nat_lt
  have := Nat.mul_le_mul_right rate (show block ≤ len / rate by omega)
  omega

/-! ## SHA-256 / SHA-512 (`slhdsa/slhdsa_hash.ml` lines 120–315) -/

/-- SHA-256 padding (lines 163–174): `padded_length = ⌈(len + 9)/64⌉·64` is the
smallest multiple of 64 that is at least `len + 9`, so
`len + 9 ≤ padded_length ≤ len + 72`, and the `0x80` byte
(`Bytes.unsafe_set padded input_length`) and the length bytes at
`padded_length − 1 − i` (`i < 8`) are in bounds and do not overlap. -/
theorem sha256_padding_ints (len : ℕ) :
    len + 9 ≤ (len + 9 + 63) / 64 * 64 ∧ (len + 9 + 63) / 64 * 64 ≤ len + 72 ∧
    (len + 9 + 63) / 64 * 64 - 64 < len + 9 ∧
    (len + 9 + 63) / 64 * 64 % 64 = 0 ∧ len < (len + 9 + 63) / 64 * 64 ∧
    (∀ i < 8, len < (len + 9 + 63) / 64 * 64 - 1 - i ∧
      (len + 9 + 63) / 64 * 64 - 1 - i < (len + 9 + 63) / 64 * 64) := by
  refine ⟨by omega, by omega, by omega, by omega, by omega, fun i hi => ⟨by omega, by omega⟩⟩

/-- SHA-512 padding (lines 270–276): `padded_length` is the smallest multiple
of 128 that is at least `len + 17`, so `len + 17 ≤ padded_length ≤ len + 144`,
and `set_u64_be padded (padded_length − 8)` writes after the `0x80` byte. -/
theorem sha512_padding_ints (len : ℕ) :
    len + 17 ≤ (len + 17 + 127) / 128 * 128 ∧ (len + 17 + 127) / 128 * 128 ≤ len + 144 ∧
    (len + 17 + 127) / 128 * 128 - 128 < len + 17 ∧
    (len + 17 + 127) / 128 * 128 % 128 = 0 ∧
    len + 8 < (len + 17 + 127) / 128 * 128 - 8 := by
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Block loads (lines 184–186 and 286–288): `get_u32_be padded (64·block + 4 i)`
and `get_u64_be padded (128·block + 8 i)` read only inside `padded`
(`String.unsafe_get`, unchecked). -/
theorem block_load_indices (PL block i k : ℕ) :
    (block < PL / 64 → i < 16 → k < 4 → block * 64 + 4 * i + k < PL) ∧
    (block < PL / 128 → i < 16 → k < 8 → block * 128 + 8 * i + k < PL) := by
  constructor
  · intro hb hi hk
    have := Nat.mul_le_mul_right 64 (show block + 1 ≤ PL / 64 by omega)
    have := Nat.div_mul_le_self PL 64
    omega
  · intro hb hi hk
    have := Nat.mul_le_mul_right 128 (show block + 1 ≤ PL / 128 by omega)
    have := Nat.div_mul_le_self PL 128
    omega

/-- Schedule and round indices (lines 187–215, 289–307): `w.(i − 15)`,
`w.(i − 2)`, `w.(i − 16)`, `w.(i − 7)` for `16 ≤ i < R` and `w.(i)`,
`constants.(i)` for `i < R`, with `R = 64` (`w` of size 64) or `R = 80`. -/
theorem schedule_indices : ∀ R ∈ [64, 80], ∀ i < R, 16 ≤ i →
    i - 15 < R ∧ i - 2 < R ∧ i - 16 < R ∧ i - 7 < R ∧ 1 ≤ i - 15 := by
  decide

theorem constants_sizes : sha256Constants.size = 64 ∧ sha512Constants.size = 80 ∧
    sha256H0.size = 8 ∧ sha512H0.size = 8 := by
  decide

/-- All rotation and shift amounts are in range: `rotr32 x n` shifts by `n`
and `32 − n` in `[1, 31]`; `rotr64 x n` by `n` and `64 − n` in `[1, 63]`;
`shift_right_logical` by 3, 10, 7, 6; `set_u32_be` by 24, 16, 8. -/
theorem sha2_shift_amounts :
    (∀ n ∈ [2, 6, 7, 11, 13, 17, 18, 19, 22, 25], 1 ≤ n ∧ n ≤ 31 ∧ 1 ≤ 32 - n ∧ 32 - n ≤ 31) ∧
    (∀ n ∈ [1, 8, 14, 18, 19, 28, 34, 39, 41, 61], 1 ≤ n ∧ n ≤ 63 ∧ 1 ≤ 64 - n ∧ 64 - n ≤ 63) ∧
    (∀ i < 8, 8 * (7 - i) ≤ 56) := by
  decide

/-- Output stores (lines 221–222, 313–314): `set_u32_be result (4 i)` for
`i < 8` stays inside 32 bytes, `set_u64_be result (8 i)` inside 64 bytes. -/
theorem output_indices : ∀ i < 8, 4 * i + 3 < 32 ∧ 8 * i + 7 < 64 := by
  decide

/-- The `int` intermediates of `sha256`/`sha512` (`input_length + 9 + 63`,
`padded_length`, `padded_length / 64`, `block * 64`, `base + 4 i`, … and the
SHA-512 analogues) are all at most `len + 144`, hence `Portable` for
`len < 2^30 − 144`. -/
theorem sha2_portable (len : ℕ) (hlen : len < 2 ^ 30 - 144) :
    Portable ((len + 9 + 63 : ℕ) : ℤ) ∧ Portable (((len + 9 + 63) / 64 * 64 : ℕ) : ℤ) ∧
    Portable ((len + 17 + 127 : ℕ) : ℤ) ∧ Portable (((len + 17 + 127) / 128 * 128 : ℕ) : ℤ) ∧
    (∀ block < (len + 9 + 63) / 64, ∀ i < 16, Portable ((block * 64 + 4 * i : ℕ) : ℤ)) ∧
    (∀ block < (len + 17 + 127) / 128, ∀ i < 16, Portable ((block * 128 + 8 * i : ℕ) : ℤ)) := by
  refine ⟨Portable.of_nat_lt (by omega), Portable.of_nat_lt (by omega),
    Portable.of_nat_lt (by omega), Portable.of_nat_lt (by omega), fun block hb i hi => ?_,
    fun block hb i hi => ?_⟩
  · apply Portable.of_nat_lt
    have := Nat.mul_le_mul_right 64 (show block + 1 ≤ (len + 9 + 63) / 64 by omega)
    have := Nat.div_mul_le_self (len + 9 + 63) 64
    omega
  · apply Portable.of_nat_lt
    have := Nat.mul_le_mul_right 128 (show block + 1 ≤ (len + 17 + 127) / 128 by omega)
    have := Nat.div_mul_le_self (len + 17 + 127) 128
    omega

/-- On 64-bit native code (`int` = 63 bits) no `sha256`/`sha512` intermediate
wraps for any OCaml string (`Sys.max_string_length = 2^57 − 9`). -/
theorem sha2_no_wrap_native64 (len : ℕ) (hlen : len ≤ 2 ^ 57 - 9) :
    wrap 63 (len + 17 + 127 : ℕ) = (len + 17 + 127 : ℕ) ∧
    wrap 63 ((len + 17 + 127) / 128 * 128 : ℕ) = ((len + 17 + 127) / 128 * 128 : ℕ) := by
  have key : ∀ v : ℕ, v ≤ 2 ^ 57 + 200 → wrap 63 (v : ℤ) = v := by
    intro v hv
    unfold wrap
    rw [Int.emod_eq_of_lt (by positivity) (by push_cast; omega)]
    ring
  exact ⟨key _ (by omega), key _ (by omega)⟩

/-- The limit of the `Portable` guarantee: with a 31-bit `int`,
`input_length + 9 + 63` wraps once `len ≥ 2^30 − 72` (here `len = 2^30 − 40`),
`padded_length` becomes negative and `Bytes.make` raises `Invalid_argument`
(SHA-512: `len ≥ 2^30 − 144`). On 32-bit native code this cannot happen
(`Sys.max_string_length = 2^24 − 5`); under `wasm_of_ocaml` it would need a
single string of about 1 GiB. The result is an exception, never a wrong
digest. -/
theorem sha256_wraps_at_31_bits :
    wrap 31 ((2 ^ 30 - 40 : ℕ) + 9 + 63 : ℤ) < 0 := by
  unfold wrap; norm_num

/-- `Int64.mul (Int64.of_int len) 8L` is `8·len` exactly (no signed overflow)
for `len < 2^60`, and its 64-bit pattern is `8·len` for `len < 2^61`. -/
theorem bit_length_exact (len : ℕ) (h : len < 2 ^ 61) :
    (BitVec.ofNat 64 len * 8#64).toNat = 8 * len := by
  have : BitVec.ofNat 64 len * 8#64 = BitVec.ofNat 64 (8 * len) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_comm]
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## HMAC and MGF1 (lines 317–340) -/

/-- `hmac` (lines 321–324): `String.make (block_size − |key'|)` gets a
non-negative length whenever the hash output fits in a block. -/
theorem hmac_make_nonneg (B keyLen hashLen : ℕ) (h : hashLen ≤ B) :
    let k := if keyLen > B then hashLen else keyLen
    k ≤ B := by
  intro k
  simp only [k]
  split <;> omega

/-- `mgf1` (lines 329–337): the counters are `< 2^32` for
`output_length ≤ 2^32 · digest_size`, and the `int` intermediates are
`Portable` for `output_length < 2^30 − 64`. -/
theorem mgf1_ints (hLen L : ℕ) (hh : 0 < hLen) (hh64 : hLen ≤ 64) :
    (L ≤ 2 ^ 32 * hLen → ∀ counter < (L + hLen - 1) / hLen, counter < 2 ^ 32) ∧
    (L < 2 ^ 30 - 128 → Portable ((L + hLen - 1 : ℕ) : ℤ) ∧ Portable (((L + hLen - 1) / hLen : ℕ) : ℤ) ∧
      Portable (((L + hLen - 1) / hLen * hLen : ℕ) : ℤ)) := by
  refine ⟨fun hL counter hc => ?_, fun hL => ⟨Portable.of_nat_lt (by omega),
    Portable.of_nat_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)),
    Portable.of_nat_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ _) (by omega))⟩⟩
  have hb : (L + hLen - 1) / hLen < 2 ^ 32 + 1 :=
    (Nat.div_lt_iff_lt_mul hh).mpr (by rw [Nat.add_mul, Nat.one_mul]; omega)
  omega

end OcamlPq.Hash.Safety
