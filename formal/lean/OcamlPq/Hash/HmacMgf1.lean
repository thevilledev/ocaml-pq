import OcamlPq.Hash.Sha512

/-!
# HMAC (FIPS 198-1) and MGF1 (RFC 8017), `slhdsa/slhdsa_hash.ml` lines 317–340

* `hmac_eq`: the OCaml `hmac ~block_size hash` is FIPS 198-1 HMAC with hash
  `hash` and block size `B = block_size`, for every hash whose outputs have
  at most `B` bytes (true for SHA-256/`B = 64` and SHA-512/`B = 128`).
* `hmacSha256_eq`, `hmacSha512_eq`: `hmac_sha256`/`hmac_sha512` are HMAC with
  the FIPS 180-4 hash functions (as byte-string functions `SHA256Bytes`,
  `SHA512Bytes`).
* `mgf1_eq`: `mgf1 hash ~digest_size:hLen ~output_length:L` is RFC 8017 MGF1
  for every `L ≤ 2^32 · hLen` (RFC 8017 outputs "mask too long" above that;
  `mgf1_no_length_check` records that the OCaml code has no such check, which
  is unreachable in practice).
-/

namespace OcamlPq.Hash.Sha2

open FIPS180 Keccak

/-! ## Bytes as bits is injective, so FIPS 180-4 defines byte-string hashes -/

theorem bytesToBitsBE_injective (a b : List UInt8) (h : bytesToBitsBE a = bytesToBitsBE b) : a = b := by
  have hl : a.length = b.length := by
    have := congrArg List.length h; simp at this; omega
  apply List.ext_getElem hl
  intro i hia hib
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 8
  · have h1 := bytesToBitsBE_getElem a (8 * i + (7 - t)) (by simp; omega)
    have h2 := bytesToBitsBE_getElem b (8 * i + (7 - t)) (by simp; omega)
    have e1 : (8 * i + (7 - t)) / 8 = i := by omega
    have e2 : 7 - (8 * i + (7 - t)) % 8 = t := by omega
    simp only [e1, e2] at h1 h2
    rw [← h1, ← h2]
    simp only [h]
  · rw [UInt8.testBit_ge _ (by omega), UInt8.testBit_ge _ (by omega)]

open Classical in
/-- SHA-256 as a byte-string function: the byte string whose bits are
FIPS 180-4 `SHA256` of the input's bits. -/
noncomputable def SHA256Bytes (M : List UInt8) : List UInt8 :=
  if h : ∃ out, bytesToBitsBE out = SHA256 (bytesToBitsBE M) then h.choose else []

open Classical in
/-- SHA-512 as a byte-string function. -/
noncomputable def SHA512Bytes (M : List UInt8) : List UInt8 :=
  if h : ∃ out, bytesToBitsBE out = SHA512 (bytesToBitsBE M) then h.choose else []

theorem sha256_eq_bytes (M : List UInt8) : sha256 M = SHA256Bytes M := by
  have h : ∃ out, bytesToBitsBE out = SHA256 (bytesToBitsBE M) := ⟨_, sha256_eq M⟩
  rw [SHA256Bytes, dite_eq_left h]
  exact bytesToBitsBE_injective _ _ ((sha256_eq M).trans h.choose_spec.symm)

theorem sha512_eq_bytes (M : List UInt8) (hM : M.length < 2 ^ 61) : sha512 M = SHA512Bytes M := by
  have h : ∃ out, bytesToBitsBE out = SHA512 (bytesToBitsBE M) := ⟨_, sha512_eq M hM⟩
  rw [SHA512Bytes, dite_eq_left h]
  exact bytesToBitsBE_injective _ _ ((sha512_eq M hM).trans h.choose_spec.symm)

/-! ## HMAC -/

theorem zipWith_replicate (l : List UInt8) (n : ℕ) (b : UInt8) (h : l.length = n) :
    List.zipWith (· ^^^ ·) l (List.replicate n b) = l.map fun c => c ^^^ b := by
  subst h
  induction l with
  | nil => rfl
  | cons c l ih => simp [List.replicate_succ, ih]

/-- **HMAC.** For any hash function whose outputs are at most `B` bytes, the
OCaml `hmac ~block_size:B hash` is FIPS 198-1 HMAC. -/
theorem hmac_eq (B : ℕ) (hash : List UInt8 → List UInt8) (hL : ∀ x, (hash x).length ≤ B)
    (key message : List UInt8) : hmac B hash key message = FIPS198.HMAC hash B key message := by
  -- the padded key is FIPS 198-1 `K0`, and it has `B` bytes
  have hK0 : (if key.length > B then hash key else key) ++
      List.replicate (B - (if key.length > B then hash key else key).length) 0 =
      FIPS198.K0 hash B key := by
    unfold FIPS198.K0
    by_cases h1 : key.length = B
    · simp [h1]
    · by_cases h2 : key.length > B
      · simp [h1, h2]
      · simp [h1, h2]
  have hlen : (FIPS198.K0 hash B key).length = B := by
    unfold FIPS198.K0
    by_cases h1 : key.length = B
    · simp [h1]
    · by_cases h2 : key.length > B
      · have := hL key; simp [h1, h2]; omega
      · simp [h1, h2]; omega
  simp only [hmac, FIPS198.HMAC, xorWith]
  rw [hK0, zipWith_replicate _ _ _ hlen, zipWith_replicate _ _ _ hlen]

/-- **HMAC-SHA-256.** `hmac_sha256` is FIPS 198-1 HMAC with FIPS 180-4
SHA-256 and `B = 64`. -/
theorem hmacSha256_eq (key message : List UInt8) :
    hmacSha256 key message = FIPS198.HMAC SHA256Bytes 64 key message := by
  rw [hmacSha256, hmac_eq 64 sha256 (fun x => by rw [sha256_length]; norm_num)]
  have : sha256 = SHA256Bytes := funext sha256_eq_bytes
  rw [this]

/-- **HMAC-SHA-512.** `hmac_sha512` is FIPS 198-1 HMAC with FIPS 180-4
SHA-512 and `B = 128`, for keys and messages of fewer than `2^61 − 256` bytes
(every OCaml string). -/
theorem hmacSha512_eq (key message : List UInt8) (hk : key.length < 2 ^ 61)
    (hm : message.length < 2 ^ 61 - 256) :
    hmacSha512 key message = FIPS198.HMAC SHA512Bytes 128 key message := by
  rw [hmacSha512, hmac_eq 128 sha512 (fun x => by rw [sha512_length]; norm_num)]
  -- every string hashed is shorter than `2^61` bytes
  have hK0 : (FIPS198.K0 sha512 128 key).length = 128 := by
    unfold FIPS198.K0
    by_cases h1 : key.length = 128
    · simp [h1]
    · by_cases h2 : key.length > 128
      · simp [h1, h2, sha512_length]
      · simp [h1, h2]; omega
  unfold FIPS198.HMAC
  simp only
  have e1 : sha512 ((FIPS198.K0 sha512 128 key).zipWith (· ^^^ ·) (List.replicate 128 0x36) ++ message) =
      SHA512Bytes ((FIPS198.K0 sha512 128 key).zipWith (· ^^^ ·) (List.replicate 128 0x36) ++ message) :=
    sha512_eq_bytes _ (by simp [hK0]; omega)
  have hK0' : FIPS198.K0 sha512 128 key = FIPS198.K0 SHA512Bytes 128 key := by
    unfold FIPS198.K0
    by_cases h1 : key.length = 128
    · simp [h1]
    · by_cases h2 : key.length > 128
      · simp [h1, h2, sha512_eq_bytes key hk]
      · simp [h1, h2]
  rw [e1, sha512_eq_bytes _ (by simp [hK0]; rw [← sha512_eq_bytes _ (by simp [hK0]; omega), sha512_length]; omega),
    hK0']

/-! ## MGF1 -/

/-- `set_u32_be (Bytes.create 4) 0 (Int32.of_int counter)` is `I2OSP(counter, 4)`
for `counter < 2^32` (including `counter ≥ 2^31`, where `Int32.of_int` gives
a negative `Int32.t` with the same bits). -/
theorem encode_counter (counter : ℕ) (hc : counter < 2 ^ 32) :
    setU32Be (List.replicate 4 0) 0 (int32OfInt counter) = RFC8017.I2OSP counter 4 := by
  have key : ∀ s, s ≤ 24 → (byteOfInt32 ((int32OfInt counter >>> s) &&& 0xff#32)) =
      UInt8.ofNat (counter / 2 ^ s % 256) := by
    intro s hs
    simp only [byteOfInt32, int32OfInt]
    congr 1
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
      show (0xff#32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have k0 := key 0 (by norm_num)
  simp only [Nat.pow_zero, Nat.div_one, BitVec.ushiftRight_zero] at k0
  simp only [setU32Be, RFC8017.I2OSP, List.range_succ, List.range_zero, List.nil_append, key 24 (by norm_num), key 16 (by norm_num), key 8 (by norm_num), k0]
  simp

/-- `set_u32_be encoded 0 x` overwrites all four bytes of `encoded =
Bytes.create 4`, so the model's choice of zero-filled contents is immaterial. -/
theorem setU32Be_overwrites (junk : List UInt8) (hj : junk.length = 4) (x : BitVec 32) :
    setU32Be junk 0 x = setU32Be (List.replicate 4 0) 0 x := by
  match junk, hj with
  | [_, _, _, _], _ => simp [setU32Be]

/-- **MGF1.** For `L ≤ 2^32 · hLen` and a hash with `hLen`-byte outputs, the
OCaml `mgf1 hash ~digest_size:hLen ~output_length:L seed` is RFC 8017 MGF1. -/
theorem mgf1_eq (hash : List UInt8 → List UInt8) (hLen L : ℕ) (hh : 0 < hLen)
    (hL : L ≤ 2 ^ 32 * hLen) (seed : List UInt8) :
    RFC8017.MGF1 hash hLen seed L = some (mgf1 hash hLen L seed) := by
  unfold RFC8017.MGF1 mgf1
  rw [ite_eq_right (by omega)]
  simp only [List.drop_zero, Option.some.injEq]
  congr 1
  apply List.foldl_ext
  intro T counter hc
  have hc' := List.mem_range.mp hc
  have : counter < 2 ^ 32 := by
    have hb : (L + hLen - 1) / hLen < 2 ^ 32 + 1 :=
      (Nat.div_lt_iff_lt_mul hh).mpr (by rw [Nat.add_mul, Nat.one_mul]; omega)
    omega
  rw [encode_counter counter this]

/-- **MGF1-SHA-256.** `mgf1_sha256 ~output_length:L seed` is RFC 8017 MGF1
with FIPS 180-4 SHA-256, for every `L ≤ 2^37`. -/
theorem mgf1Sha256_eq (L : ℕ) (hL : L ≤ 2 ^ 32 * 32) (seed : List UInt8) :
    RFC8017.MGF1 SHA256Bytes 32 seed L = some (mgf1Sha256 L seed) := by
  have : SHA256Bytes = sha256 := (funext sha256_eq_bytes).symm
  rw [this, mgf1Sha256]
  exact mgf1_eq sha256 32 L (by norm_num) hL seed

/-- **MGF1-SHA-512.** `mgf1_sha512 ~output_length:L seed` is RFC 8017 MGF1
with FIPS 180-4 SHA-512, for every `L ≤ 2^38` and seed shorter than
`2^61 − 4` bytes. -/
theorem mgf1Sha512_eq (L : ℕ) (hL : L ≤ 2 ^ 32 * 64) (seed : List UInt8)
    (hs : seed.length < 2 ^ 61 - 4) :
    RFC8017.MGF1 SHA512Bytes 64 seed L = some (mgf1Sha512 L seed) := by
  rw [mgf1Sha512, ← mgf1_eq sha512 64 L (by norm_num) hL seed]
  unfold RFC8017.MGF1
  rewrite [ite_eq_right (by omega), ite_eq_right (by omega)]
  refine congrArg some (congrArg (List.take L) ?_)
  apply List.foldl_ext
  intro T counter _
  rw [sha512_eq_bytes _ (by simp [RFC8017.I2OSP]; omega)]

/-- The OCaml `String.sub (Buffer.contents result) 0 output_length` is in
bounds: the buffer holds `⌈L / hLen⌉ · hLen ≥ L` bytes. -/
theorem mgf1_sub_in_bounds (hash : List UInt8 → List UInt8) (hLen L : ℕ) (hh : 0 < hLen)
    (hlen : ∀ x, (hash x).length = hLen) (seed : List UInt8) :
    L ≤ ((List.range ((L + hLen - 1) / hLen)).foldl (fun result counter =>
      result ++ hash (seed ++ setU32Be (List.replicate 4 0) 0 (int32OfInt counter))) []).length := by
  have : ∀ n (T : List UInt8), ((List.range n).foldl (fun result counter =>
      result ++ hash (seed ++ setU32Be (List.replicate 4 0) 0 (int32OfInt counter))) T).length =
      T.length + n * hLen := by
    intro n
    induction n with
    | zero => intro T; simp
    | succ n ih =>
      intro T
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, List.length_append, ih, hlen]
      ring
  rw [this]
  simp only [List.length_nil, Nat.zero_add]
  have h1 := Nat.div_add_mod (L + hLen - 1) hLen
  have h2 := Nat.mod_lt (L + hLen - 1) hh
  rw [Nat.mul_comm]
  omega

/-- RFC 8017 step 1 ("mask too long") has no counterpart in the OCaml code:
for `L > 2^32 · hLen` the specification fails while the model still returns
a string (its 32-bit counter wraps). Unreachable in practice: it needs a
`2^37`-byte output for SHA-256, and SLH-DSA calls MGF1 with `L ≤ 49`. -/
theorem mgf1_no_length_check (hash : List UInt8 → List UInt8) (hLen L : ℕ)
    (hL : L > 2 ^ 32 * hLen) (seed : List UInt8) : RFC8017.MGF1 hash hLen seed L = none := by
  unfold RFC8017.MGF1
  rw [ite_eq_left hL]

end OcamlPq.Hash.Sha2
