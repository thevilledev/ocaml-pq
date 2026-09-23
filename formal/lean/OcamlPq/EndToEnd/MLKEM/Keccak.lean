import OcamlPq.EndToEnd.MLKEM.Adapters

/-!
# The concrete Keccak functions

`MLKEMAlg` takes the hash functions as a `Keccak` structure: SHA3-256 and
SHA3-512 as byte-string functions, SHAKE128 and SHAKE256 as one infinite
output stream per input. This file builds two instances:

* `K₀`: the Hash area's models of `sha3_256`, `sha3_512`, `shake128`,
  `shake256` (lib/keccak.ml:117-120). The SHAKE stream is read off the model:
  byte `i` of the stream is byte `i` of `shake128 ~output_length:(i + 1)`.
  `K₀_shake128Out` / `K₀_shake256Out` show that `MLKEMAlg`'s
  `Keccak.shake128Out L x` (its model of `Keccak.shake128 ~output_length:L x`)
  is then exactly the OCaml model's output. This uses the prefix consistency
  `shake128_prefix`, `shake256_prefix` of the Hash area.
* `Kfips`: FIPS 202 `SHA3-256`, `SHA3-512`, `SHAKE128`, `SHAKE256` as
  transcribed by the Hash area (`Hash.FIPS202`), on the bit strings of the
  inputs (FIPS 202 Appendix B.1, `Hash.FIPS202.bytesToBits`), with the output
  bit strings read back as bytes (`bitsToBytes202`). Byte `i` of the SHAKE
  stream is byte `i` of `SHAKE128(M, 8(i + 1))`.

`K₀_eq_Kfips : K₀ = Kfips` follows from `sha3_256_eq`, `sha3_512_eq`,
`shake128_eq`, `shake256_eq`. Byte strings of the Hash area are
`List UInt8`; `u8s` / `ofU8s` convert (`UInt8.ofFin` / `UInt8.toFin`, a
bijection `Fin 256 ≃ UInt8`).
-/

namespace OcamlPq.EndToEnd.MLKEM

open OcamlPq.MLKEMAlg

/-! ## `Fin 256` and `UInt8` -/

/-- A byte as the Hash area's `UInt8`. -/
def toU8 (b : Byte) : UInt8 := UInt8.ofFin b

/-- A `UInt8` as a byte. -/
def ofU8 (u : UInt8) : Byte := u.toFin

/-- An `MLKEMAlg` byte string as a Hash-area byte string. -/
def u8s (s : Bytes) : List UInt8 := s.map toU8

/-- A Hash-area byte string as an `MLKEMAlg` byte string. -/
def ofU8s (l : List UInt8) : Bytes := l.map ofU8

@[simp] theorem ofU8_toU8 (b : Byte) : ofU8 (toU8 b) = b := UInt8.toFin_ofFin b

@[simp] theorem toU8_ofU8 (u : UInt8) : toU8 (ofU8 u) = u := UInt8.ofFin_toFin u

@[simp] theorem ofU8s_u8s (s : Bytes) : ofU8s (u8s s) = s := by
  simp [ofU8s, u8s, List.map_map, Function.comp_def]

@[simp] theorem u8s_ofU8s (l : List UInt8) : u8s (ofU8s l) = l := by
  simp [ofU8s, u8s, List.map_map, Function.comp_def]

@[simp] theorem length_ofU8s (l : List UInt8) : (ofU8s l).length = l.length := by simp [ofU8s]

@[simp] theorem length_u8s (s : Bytes) : (u8s s).length = s.length := by simp [u8s]

/-! ## The OCaml model -/

/-- The Keccak functions of lib/keccak.ml, as modelled by the Hash area. -/
def K₀ : Keccak where
  sha3_256 x := ofU8s (Hash.Keccak.sha3_256 (u8s x))
  sha3_512 x := ofU8s (Hash.Keccak.sha3_512 (u8s x))
  shake128 x i := ofU8 ((Hash.Keccak.shake128 (i + 1) (u8s x)).getD i 0)
  shake256 x i := ofU8 ((Hash.Keccak.shake256 (i + 1) (u8s x)).getD i 0)
  sha3_256_length x := by
    rw [length_ofU8s]
    exact (Hash.Keccak.sponge_get 136 6 32 (by norm_num) (by norm_num) _).1
  sha3_512_length x := by
    rw [length_ofU8s]
    exact (Hash.Keccak.sponge_get 72 6 64 (by norm_num) (by norm_num) _).1

theorem K₀_sha3_256 (x : Bytes) : K₀.sha3_256 x = ofU8s (Hash.Keccak.sha3_256 (u8s x)) := by
  unfold K₀; dsimp only

theorem K₀_sha3_512 (x : Bytes) : K₀.sha3_512 x = ofU8s (Hash.Keccak.sha3_512 (u8s x)) := by
  unfold K₀; dsimp only

theorem K₀_shake128 (x : Bytes) (i : ℕ) :
    K₀.shake128 x i = ofU8 ((Hash.Keccak.shake128 (i + 1) (u8s x)).getD i 0) := by
  unfold K₀; dsimp only

theorem K₀_shake256 (x : Bytes) (i : ℕ) :
    K₀.shake256 x i = ofU8 ((Hash.Keccak.shake256 (i + 1) (u8s x)).getD i 0) := by
  unfold K₀; dsimp only

/-- `MLKEMAlg`'s model of `Keccak.shake128 ~output_length:L x` is the Hash
    area's model of the same call. -/
theorem K₀_shake128Out (L : ℕ) (x : Bytes) :
    K₀.shake128Out L x = ofU8s (Hash.Keccak.shake128 L (u8s x)) := by
  have hlen := Hash.Keccak.shake128_length L (u8s x)
  apply List.ext_getElem (by simp [Keccak.shake128Out, hlen])
  intro i h1 h2
  have hi : i < L := by simpa using h1
  simp only [Keccak.shake128Out, List.getElem_ofFn, ofU8s, List.getElem_map, K₀_shake128]
  rw [Hash.Keccak.shake128_prefix (i + 1) L (by omega),
    List.getD_eq_getElem _ _ (by rw [List.length_take, hlen]; omega), List.getElem_take]

/-- `MLKEMAlg`'s model of `Keccak.shake256 ~output_length:L x` is the Hash
    area's model of the same call. -/
theorem K₀_shake256Out (L : ℕ) (x : Bytes) :
    K₀.shake256Out L x = ofU8s (Hash.Keccak.shake256 L (u8s x)) := by
  have hlen := Hash.Keccak.shake256_length L (u8s x)
  apply List.ext_getElem (by simp [Keccak.shake256Out, hlen])
  intro i h1 h2
  have hi : i < L := by simpa using h1
  simp only [Keccak.shake256Out, List.getElem_ofFn, ofU8s, List.getElem_map, K₀_shake256]
  rw [Hash.Keccak.shake256_prefix (i + 1) L (by omega),
    List.getD_eq_getElem _ _ (by rw [List.length_take, hlen]; omega), List.getElem_take]

/-! ## FIPS 202 -/

/-- A bit string of length `8m` as `m` bytes, bit `8k + j` being bit `j` of
    byte `k` (the inverse of FIPS 202 Appendix B.1's byte-to-bit conversion,
    `Hash.FIPS202.bytesToBits`). -/
def bitsToBytes202 (S : Hash.FIPS202.Bits) : List UInt8 :=
  List.ofFn fun k : Fin (S.length / 8) =>
    UInt8.ofNat (∑ j ∈ Finset.range 8, (S.getD (8 * k.val + j) false).toNat * 2 ^ j)

theorem bitsToBytes202_bytesToBits (bs : List UInt8) :
    bitsToBytes202 (Hash.FIPS202.bytesToBits bs) = bs := by
  apply List.ext_getElem (by simp [bitsToBytes202, Hash.bytesToBits_length])
  intro k h1 h2
  simp only [bitsToBytes202, List.getElem_ofFn]
  have hterm : ∀ j ∈ Finset.range 8,
      ((Hash.FIPS202.bytesToBits bs).getD (8 * k + j) false).toNat * 2 ^ j =
        ((bs[k]'h2).toNat / 2 ^ j % 2) * 2 ^ j := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [List.getD_eq_getElem _ _ (by rw [Hash.bytesToBits_length]; omega),
      Hash.bytesToBits_getElem, ← Nat.toNat_testBit]
    simp only [show (8 * k + j) / 8 = k by omega, show (8 * k + j) % 8 = j by omega]
  rw [Finset.sum_congr rfl hterm, byte_bits_sum _ (UInt8.toNat_lt _), UInt8.ofNat_toNat]

/-- The FIPS 202 functions of the Hash area (`Hash.FIPS202.SHA3_256`,
    `SHA3_512`, `SHAKE128`, `SHAKE256`), on byte strings. -/
def Kfips : Keccak where
  sha3_256 x := ofU8s (bitsToBytes202 (Hash.FIPS202.SHA3_256 (Hash.FIPS202.bytesToBits (u8s x))))
  sha3_512 x := ofU8s (bitsToBytes202 (Hash.FIPS202.SHA3_512 (Hash.FIPS202.bytesToBits (u8s x))))
  shake128 x i := ofU8 ((bitsToBytes202
    (Hash.FIPS202.SHAKE128 (Hash.FIPS202.bytesToBits (u8s x)) (8 * (i + 1)))).getD i 0)
  shake256 x i := ofU8 ((bitsToBytes202
    (Hash.FIPS202.SHAKE256 (Hash.FIPS202.bytesToBits (u8s x)) (8 * (i + 1)))).getD i 0)
  sha3_256_length x := by
    rw [← Hash.Keccak.sha3_256_eq, bitsToBytes202_bytesToBits, length_ofU8s]
    exact (Hash.Keccak.sponge_get 136 6 32 (by norm_num) (by norm_num) _).1
  sha3_512_length x := by
    rw [← Hash.Keccak.sha3_512_eq, bitsToBytes202_bytesToBits, length_ofU8s]
    exact (Hash.Keccak.sponge_get 72 6 64 (by norm_num) (by norm_num) _).1

theorem Kfips_sha3_256 (x : Bytes) :
    Kfips.sha3_256 x =
      ofU8s (bitsToBytes202 (Hash.FIPS202.SHA3_256 (Hash.FIPS202.bytesToBits (u8s x)))) := by
  unfold Kfips; dsimp only

theorem Kfips_sha3_512 (x : Bytes) :
    Kfips.sha3_512 x =
      ofU8s (bitsToBytes202 (Hash.FIPS202.SHA3_512 (Hash.FIPS202.bytesToBits (u8s x)))) := by
  unfold Kfips; dsimp only

theorem Kfips_shake128 (x : Bytes) (i : ℕ) :
    Kfips.shake128 x i = ofU8 ((bitsToBytes202
      (Hash.FIPS202.SHAKE128 (Hash.FIPS202.bytesToBits (u8s x)) (8 * (i + 1)))).getD i 0) := by
  unfold Kfips; dsimp only

theorem Kfips_shake256 (x : Bytes) (i : ℕ) :
    Kfips.shake256 x i = ofU8 ((bitsToBytes202
      (Hash.FIPS202.SHAKE256 (Hash.FIPS202.bytesToBits (u8s x)) (8 * (i + 1)))).getD i 0) := by
  unfold Kfips; dsimp only

/-- Two `Keccak` structures are equal if their four functions are. -/
theorem Keccak.ext' {K K' : Keccak} (h1 : K.sha3_256 = K'.sha3_256)
    (h2 : K.sha3_512 = K'.sha3_512) (h3 : K.shake128 = K'.shake128)
    (h4 : K.shake256 = K'.shake256) : K = K' := by
  cases K; cases K'
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

/-- **The OCaml Keccak functions are FIPS 202.** -/
theorem K₀_eq_Kfips : K₀ = Kfips := by
  apply Keccak.ext'
  · funext x
    rw [K₀_sha3_256, Kfips_sha3_256, ← Hash.Keccak.sha3_256_eq, bitsToBytes202_bytesToBits]
  · funext x
    rw [K₀_sha3_512, Kfips_sha3_512, ← Hash.Keccak.sha3_512_eq, bitsToBytes202_bytesToBits]
  · funext x i
    rw [K₀_shake128, Kfips_shake128, ← Hash.Keccak.shake128_eq, bitsToBytes202_bytesToBits]
  · funext x i
    rw [K₀_shake256, Kfips_shake256, ← Hash.Keccak.shake256_eq, bitsToBytes202_bytesToBits]

/-- The first `L` bytes of the FIPS 203 XOF stream of `Kfips` are
    `SHAKE128(M, 8L)`. -/
theorem Kfips_shake128Out (L : ℕ) (x : Bytes) :
    Kfips.shake128Out L x =
      ofU8s (bitsToBytes202 (Hash.FIPS202.SHAKE128 (Hash.FIPS202.bytesToBits (u8s x)) (8 * L))) := by
  rw [← K₀_eq_Kfips, K₀_shake128Out, ← Hash.Keccak.shake128_eq, bitsToBytes202_bytesToBits]

/-- The first `L` bytes of the SHAKE256 stream of `Kfips` are
    `SHAKE256(M, 8L)`. -/
theorem Kfips_shake256Out (L : ℕ) (x : Bytes) :
    Kfips.shake256Out L x =
      ofU8s (bitsToBytes202 (Hash.FIPS202.SHAKE256 (Hash.FIPS202.bytesToBits (u8s x)) (8 * L))) := by
  rw [← K₀_eq_Kfips, K₀_shake256Out, ← Hash.Keccak.shake256_eq, bitsToBytes202_bytesToBits]

end OcamlPq.EndToEnd.MLKEM
