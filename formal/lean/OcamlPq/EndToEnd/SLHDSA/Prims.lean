import OcamlPq.Hash
import OcamlPq.SLHDSA

/-!
# SLH-DSA end to end: the concrete and the specified hash primitives

The SLH-DSA area models `slhdsa_engine.ml` over an abstract bundle of hash
primitives (`OcamlPq.SLHDSA.Hash.Prims`, byte strings as `List ℕ`). The Hash
area models `slhdsa_hash.ml` (SHA-256, SHA-512, HMAC, MGF1 and, via the
textually identical copy of `lib/keccak.ml`, SHAKE256) with byte strings as
`List UInt8`, and proves those models equal to FIPS 180-4 / FIPS 202 /
FIPS 198-1 / RFC 8017.

This file fills the bundle twice:

* `codePrims`: the Hash area's **OCaml models** (`Sha2.sha256`,
  `Sha2.sha512`, `Keccak.shake256`, `Sha2.hmacSha256`, `Sha2.hmacSha512`,
  `Sha2.mgf1Sha256`, `Sha2.mgf1Sha512`), i.e. `Slhdsa_hash` itself;
* `specPrims`: the Hash area's **specifications** (`SHA256Bytes`,
  `SHA512Bytes` from FIPS 180-4, `SHAKE256Bytes` from FIPS 202 defined here,
  FIPS 198-1 `HMAC` with `B = 64`/`128`, RFC 8017 `MGF1`),

and proves them equal (`codePrims_*`), unconditionally for SHA-256, SHAKE256,
HMAC-SHA-256 and MGF1-SHA-256 (with `maskLen ≤ 2^37`), and for inputs of
fewer than `2^61` bytes for the SHA-512 family (the OCaml code computes the
bit length in an `Int64`; see `Sha2.sha512_eq`).

## Representation adapters

Both areas represent an OCaml `string` as a list of its bytes; they differ
only in the element type. The adapters are

* `toU8 : List ℕ → List UInt8 := map UInt8.ofNat` (every element of an OCaml
  string is `< 256`, where `UInt8.ofNat` is the identity; `toU8_ofU8`,
  `ofU8_toU8`);
* `ofU8 : List UInt8 → List ℕ := map UInt8.toNat` (injective, lands in
  `[0, 256)`).

A primitive `f` on `List UInt8` is used on `List ℕ` as `ofU8 ∘ f ∘ toU8`
(both bundles use the same adapters, so the adapters never contribute a
difference between code and specification).
-/

namespace OcamlPq.EndToEnd.SLHDSA

open OcamlPq.Hash.FIPS202 (bytesToBits SHAKE256)

/-! ## Adapters -/

/-- `List ℕ` byte string (SLH-DSA area) → `List UInt8` byte string (Hash area). -/
def toU8 (x : List ℕ) : List UInt8 := x.map UInt8.ofNat

/-- `List UInt8` byte string (Hash area) → `List ℕ` byte string (SLH-DSA area). -/
def ofU8 (x : List UInt8) : List ℕ := x.map UInt8.toNat

@[simp] theorem toU8_length (x : List ℕ) : (toU8 x).length = x.length := by simp [toU8]
@[simp] theorem ofU8_length (x : List UInt8) : (ofU8 x).length = x.length := by simp [ofU8]
@[simp] theorem toU8_append (x y : List ℕ) : toU8 (x ++ y) = toU8 x ++ toU8 y := by simp [toU8]
@[simp] theorem ofU8_append (x y : List UInt8) : ofU8 (x ++ y) = ofU8 x ++ ofU8 y := by simp [ofU8]

theorem ofU8_lt (x : List UInt8) : ∀ b ∈ ofU8 x, b < 256 := by
  intro b hb
  simp only [ofU8, List.mem_map] at hb
  obtain ⟨c, -, rfl⟩ := hb
  exact c.toNat_lt

theorem toU8_ofU8 (x : List UInt8) : toU8 (ofU8 x) = x := by
  simp [toU8, ofU8, Function.comp_def]

/-- On byte-valued lists (every OCaml string) the adapters are inverse. -/
theorem ofU8_toU8 (x : List ℕ) (hx : ∀ b ∈ x, b < 256) : ofU8 (toU8 x) = x := by
  simp only [ofU8, toU8, List.map_map]
  conv_rhs => rw [← List.map_id x]
  apply List.map_congr_left
  intro b hb
  simp [Nat.mod_eq_of_lt (hx b hb)]

/-! ## FIPS 202 SHAKE256 on byte strings -/

/-- `bytesToBits` (FIPS 202 Appendix B.1) is injective. -/
theorem bytesToBits_injective (a b : List UInt8) (h : bytesToBits a = bytesToBits b) : a = b := by
  have hl : a.length = b.length := by
    have := congrArg List.length h
    simp only [OcamlPq.Hash.bytesToBits_length] at this
    omega
  apply List.ext_getElem hl
  intro i hia hib
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 8
  · have h1 := OcamlPq.Hash.bytesToBits_getElem a (8 * i + t) (by simp; omega)
    have h2 := OcamlPq.Hash.bytesToBits_getElem b (8 * i + t) (by simp; omega)
    have e1 : (8 * i + t) / 8 = i := by omega
    have e2 : (8 * i + t) % 8 = t := by omega
    simp only [e1, e2] at h1 h2
    rw [← h1, ← h2]
    simp only [h]
  · rw [OcamlPq.Hash.UInt8.testBit_ge _ (by omega), OcamlPq.Hash.UInt8.testBit_ge _ (by omega)]

open Classical in
/-- FIPS 202 `SHAKE256(M, 8L)` as a byte-string function: the byte string
    whose bit string (Appendix B.1) is `SHAKE256` of the input's bit string
    (unique by `bytesToBits_injective`; it exists by `Keccak.shake256_eq`). -/
noncomputable def SHAKE256Bytes (L : ℕ) (M : List UInt8) : List UInt8 :=
  if h : ∃ out, bytesToBits out = SHAKE256 (bytesToBits M) (8 * L) then h.choose else []

/-- **SHAKE256.** The OCaml model is FIPS 202 SHAKE256 on byte strings. -/
theorem shake256_eq_bytes (L : ℕ) (M : List UInt8) :
    OcamlPq.Hash.Keccak.shake256 L M = SHAKE256Bytes L M := by
  have h : ∃ out, bytesToBits out = SHAKE256 (bytesToBits M) (8 * L) :=
    ⟨_, OcamlPq.Hash.Keccak.shake256_eq L M⟩
  rw [SHAKE256Bytes, dite_eq_left h]
  exact bytesToBits_injective _ _ ((OcamlPq.Hash.Keccak.shake256_eq L M).trans h.choose_spec.symm)

/-! ## The two bundles -/

section Bundles

open OcamlPq.Hash

/-- **The concrete primitives**: the Hash area's models of `Slhdsa_hash`
    (`sha256`, `sha512`, `shake256 ~output_length`, `hmac_sha256`,
    `hmac_sha512`, `mgf1_sha256 ~output_length`, `mgf1_sha512
    ~output_length`), through the adapters. -/
def codePrims : OcamlPq.SLHDSA.Hash.Prims where
  sha256 x := ofU8 (Sha2.sha256 (toU8 x))
  sha512 x := ofU8 (Sha2.sha512 (toU8 x))
  shake256 L x := ofU8 (Keccak.shake256 L (toU8 x))
  hmacSha256 k m := ofU8 (Sha2.hmacSha256 (toU8 k) (toU8 m))
  hmacSha512 k m := ofU8 (Sha2.hmacSha512 (toU8 k) (toU8 m))
  mgf1Sha256 L x := ofU8 (Sha2.mgf1Sha256 L (toU8 x))
  mgf1Sha512 L x := ofU8 (Sha2.mgf1Sha512 L (toU8 x))

/-- **The specified primitives**: FIPS 180-4 SHA-256/SHA-512
    (`Sha2.SHA256Bytes`, `Sha2.SHA512Bytes`, the byte strings whose bits are
    `FIPS180.SHA256`/`SHA512` of the input's bits), FIPS 202 SHAKE256
    (`SHAKE256Bytes`), FIPS 198-1 HMAC with block sizes `B = 64` / `128`,
    and RFC 8017 MGF1 with `hLen = 32` / `64` ("mask too long", which needs
    `maskLen > 2^32·hLen`, is mapped to the empty string; SLH-DSA only asks
    for `m ≤ 49` bytes). -/
noncomputable def specPrims : OcamlPq.SLHDSA.Hash.Prims where
  sha256 x := ofU8 (Sha2.SHA256Bytes (toU8 x))
  sha512 x := ofU8 (Sha2.SHA512Bytes (toU8 x))
  shake256 L x := ofU8 (SHAKE256Bytes L (toU8 x))
  hmacSha256 k m := ofU8 (FIPS198.HMAC Sha2.SHA256Bytes 64 (toU8 k) (toU8 m))
  hmacSha512 k m := ofU8 (FIPS198.HMAC Sha2.SHA512Bytes 128 (toU8 k) (toU8 m))
  mgf1Sha256 L x := ofU8 ((RFC8017.MGF1 Sha2.SHA256Bytes 32 (toU8 x) L).getD [])
  mgf1Sha512 L x := ofU8 ((RFC8017.MGF1 Sha2.SHA512Bytes 64 (toU8 x) L).getD [])

/-! ## Code = specification, primitive by primitive -/

theorem codePrims_sha256 : codePrims.sha256 = specPrims.sha256 := by
  funext x
  simp only [codePrims, specPrims, Sha2.sha256_eq_bytes]

theorem codePrims_shake256 : codePrims.shake256 = specPrims.shake256 := by
  funext L x
  simp only [codePrims, specPrims, shake256_eq_bytes]

theorem codePrims_hmacSha256 : codePrims.hmacSha256 = specPrims.hmacSha256 := by
  funext k m
  simp only [codePrims, specPrims, Sha2.hmacSha256_eq]

theorem codePrims_mgf1Sha256 (L : ℕ) (hL : L ≤ 2 ^ 32 * 32) (x : List ℕ) :
    codePrims.mgf1Sha256 L x = specPrims.mgf1Sha256 L x := by
  simp only [codePrims, specPrims, Sha2.mgf1Sha256_eq L hL, Option.getD_some]

theorem codePrims_sha512 (x : List ℕ) (hx : x.length < 2 ^ 61) :
    codePrims.sha512 x = specPrims.sha512 x := by
  simp only [codePrims, specPrims, Sha2.sha512_eq_bytes (toU8 x) (by simpa using hx)]

theorem codePrims_hmacSha512 (k m : List ℕ) (hk : k.length < 2 ^ 61)
    (hm : m.length < 2 ^ 61 - 256) : codePrims.hmacSha512 k m = specPrims.hmacSha512 k m := by
  simp only [codePrims, specPrims, Sha2.hmacSha512_eq (toU8 k) (toU8 m) (by simpa using hk)
    (by simpa using hm)]

theorem codePrims_mgf1Sha512 (L : ℕ) (hL : L ≤ 2 ^ 32 * 64) (x : List ℕ)
    (hx : x.length < 2 ^ 61 - 4) : codePrims.mgf1Sha512 L x = specPrims.mgf1Sha512 L x := by
  simp only [codePrims, specPrims]
  rw [Sha2.mgf1Sha512_eq L hL (toU8 x) (by simpa using hx), Option.getD_some]

/-! ## Output lengths and byte ranges of the concrete primitives -/

theorem codePrims_sha256_length (x : List ℕ) : (codePrims.sha256 x).length = 32 := by
  simp [codePrims, Sha2.sha256_length]

theorem codePrims_sha512_length (x : List ℕ) : (codePrims.sha512 x).length = 64 := by
  simp [codePrims, Sha2.sha512_length]

theorem codePrims_shake256_length (L : ℕ) (x : List ℕ) : (codePrims.shake256 L x).length = L := by
  simp [codePrims, Keccak.shake256_length]

theorem codePrims_hmacSha256_length (k m : List ℕ) : (codePrims.hmacSha256 k m).length = 32 := by
  simp [codePrims, Sha2.hmacSha256, Sha2.hmac, Sha2.sha256_length]

theorem codePrims_hmacSha512_length (k m : List ℕ) : (codePrims.hmacSha512 k m).length = 64 := by
  simp [codePrims, Sha2.hmacSha512, Sha2.hmac, Sha2.sha512_length]

/-- `mgf1 hash ~digest_size:hLen ~output_length:L` returns exactly `L` bytes
    (its `String.sub … 0 L` is in bounds: `Sha2.mgf1_sub_in_bounds`). -/
theorem mgf1_length (hash : List UInt8 → List UInt8) (hLen L : ℕ) (hh : 0 < hLen)
    (hlen : ∀ x, (hash x).length = hLen) (seed : List UInt8) :
    (Sha2.mgf1 hash hLen L seed).length = L := by
  have := Sha2.mgf1_sub_in_bounds hash hLen L hh hlen seed
  simp only [Sha2.mgf1, List.drop_zero, List.length_take]
  omega

theorem codePrims_mgf1Sha256_length (L : ℕ) (x : List ℕ) :
    (codePrims.mgf1Sha256 L x).length = L := by
  simp only [codePrims, Sha2.mgf1Sha256, ofU8_length]
  exact mgf1_length _ 32 L (by norm_num) Sha2.sha256_length _

theorem codePrims_mgf1Sha512_length (L : ℕ) (x : List ℕ) :
    (codePrims.mgf1Sha512 L x).length = L := by
  simp only [codePrims, Sha2.mgf1Sha512, ofU8_length]
  exact mgf1_length _ 64 L (by norm_num) Sha2.sha512_length _

theorem codePrims_sha256_lt (x : List ℕ) : ∀ b ∈ codePrims.sha256 x, b < 256 := by
  simp only [codePrims]
  exact ofU8_lt _
theorem codePrims_sha512_lt (x : List ℕ) : ∀ b ∈ codePrims.sha512 x, b < 256 := by
  simp only [codePrims]
  exact ofU8_lt _
theorem codePrims_shake256_lt (L : ℕ) (x : List ℕ) : ∀ b ∈ codePrims.shake256 L x, b < 256 := by
  simp only [codePrims]
  exact ofU8_lt _
theorem codePrims_hmacSha256_lt (k m : List ℕ) : ∀ b ∈ codePrims.hmacSha256 k m, b < 256 := by
  simp only [codePrims]
  exact ofU8_lt _
theorem codePrims_hmacSha512_lt (k m : List ℕ) : ∀ b ∈ codePrims.hmacSha512 k m, b < 256 := by
  simp only [codePrims]
  exact ofU8_lt _
theorem codePrims_mgf1Sha256_lt (L : ℕ) (x : List ℕ) : ∀ b ∈ codePrims.mgf1Sha256 L x, b < 256 := by
  simp only [codePrims]
  exact ofU8_lt _
theorem codePrims_mgf1Sha512_lt (L : ℕ) (x : List ℕ) : ∀ b ∈ codePrims.mgf1Sha512 L x, b < 256 := by
  simp only [codePrims]
  exact ofU8_lt _

end Bundles

end OcamlPq.EndToEnd.SLHDSA
