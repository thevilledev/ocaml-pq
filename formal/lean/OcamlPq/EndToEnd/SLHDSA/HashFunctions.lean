import OcamlPq.EndToEnd.SLHDSA.Prims

/-!
# SLH-DSA end to end: F, H, T_ℓ, PRF, PRF_msg, H_msg over the concrete primitives

* `addressCompressed_eq_compress`: `address_compressed = ADRS_c` for **every**
  address. The SLH-DSA area's `addressCompressed_eq` assumes `layer, type <
  256`, but both sides keep only the low byte of the layer and of the type
  (`Char.unsafe_chr` in the code; `ADRS[3]`, `ADRS[19]` of the big-endian
  words in FIPS 205 §11.2), so the hypothesis is unnecessary. Consequently
  `thash_one`, `thash_many`, `prf_fips` restate the area's `thash_F`,
  `thash_T`, `prf_eq` without `SmallAddress`.
* `fipsF_code`, `fipsHT_code`, `fipsPRF_code`, `fipsPRFmsg_code`,
  `fipsHmsg_code`: FIPS 205 §11 over the concrete primitives = §11 over the
  specified primitives (`specPrims`); only the SHA-512-based functions (sets
  with `n ∈ {24, 32}`, `usesSha512`) need a length bound on their input.
* `codeFam` (the code's hash family) and `hashOk_code`: the area's `HashOk`
  holds for all twelve parameter sets.
-/

namespace OcamlPq.EndToEnd.SLHDSA

open OcamlPq.SLHDSA
open OcamlPq.SLHDSA.Base2b (fipsToByte)

/-- The parameter set uses SHA-512 (and HMAC-SHA-512, MGF1-SHA-512): the
    SHA2 sets with `n ∈ {24, 32}` (FIPS 205 §11.2.2). These are the only
    sets whose primitives need a length bound to match their specification. -/
def usesSha512 (P : Params) : Prop := P.hash = .sha2 ∧ P.n ≠ 16

instance (P : Params) : Decidable (usesSha512 P) := by unfold usesSha512; infer_instance

/-! ## `address_compressed` = `ADRS_c` for every address -/

theorem addressCompressed_eq_compress (a : Address) :
    Code.addressCompressed a = FipsADRS.compress (Code.addressFull a) := by
  simp only [FipsADRS.compress, Code.addressCompressed, Code.addressFull, Code.setU32BE,
    Code.setU64BE, List.range_succ, List.range_zero, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, land_ff]
  simp [Nat.shiftRight_eq_div_pow]

theorem compress_length_le (adrs : List ℕ) : (FipsADRS.compress adrs).length ≤ 22 := by
  simp only [FipsADRS.compress, List.length_append, List.length_singleton, List.length_take]
  omega

/-! ## The code's `thash` / `prf` are F, H, T_ℓ, PRF (every address) -/

section Generic

variable (pr : Hash.Prims) (P : Params)

/-- `thash` with one block = `F`. -/
theorem thash_one (pkSeed : List ℕ) (hpk : pkSeed.length = P.n) (a : Address) (m1 : List ℕ) :
    Hash.thash pr P pkSeed a [m1] = Hash.fipsF pr P pkSeed (Code.addressFull a) m1 := by
  unfold Hash.thash Hash.fipsF
  rcases h : P.hash with _ | _
  · simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_singleton,
      gt_iff_lt, lt_self_iff_false, decide_false, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte, Hash.truncate_eq, Hash.sha2Prefix_eq, hpk, addressCompressed_eq_compress,
      List.append_assoc]
  · simp

/-- `thash` with `ℓ ≥ 2` blocks = `H` / `T_ℓ` on the concatenated blocks. -/
theorem thash_many (hP : P ∈ allParams) (pkSeed : List ℕ) (hpk : pkSeed.length = P.n)
    (a : Address) (blocks : List (List ℕ)) (hb : 2 ≤ blocks.length) :
    Hash.thash pr P pkSeed a blocks = Hash.fipsHT pr P pkSeed (Code.addressFull a) blocks.flatten := by
  unfold Hash.thash Hash.fipsHT
  rcases h : P.hash with _ | _
  · have hb' : blocks.length > 1 := by omega
    rcases n_cases P hP with hn | hn | hn <;>
      simp [hn, hb', Hash.truncate_eq, Hash.sha2Prefix_eq, hpk, addressCompressed_eq_compress]
  · simp

/-- `prf` = `PRF`. -/
theorem prf_fips (pkSeed skSeed : List ℕ) (hpk : pkSeed.length = P.n) (a : Address) :
    Hash.prf pr P pkSeed skSeed a = Hash.fipsPRF pr P pkSeed skSeed (Code.addressFull a) := by
  unfold Hash.prf Hash.fipsPRF
  rcases h : P.hash with _ | _
  · simp [Hash.truncate_eq, Hash.sha2Prefix_eq, hpk, addressCompressed_eq_compress]
  · simp

end Generic

/-! ## §11 over the concrete primitives = §11 over the specified primitives -/

section CodeSpec

variable (P : Params)

theorem fipsF_code (pkSeed adrs m : List ℕ) :
    Hash.fipsF codePrims P pkSeed adrs m = Hash.fipsF specPrims P pkSeed adrs m := by
  unfold Hash.fipsF
  rw [codePrims_sha256, codePrims_shake256]

theorem fipsPRF_code (pkSeed skSeed adrs : List ℕ) :
    Hash.fipsPRF codePrims P pkSeed skSeed adrs = Hash.fipsPRF specPrims P pkSeed skSeed adrs := by
  unfold Hash.fipsPRF
  rw [codePrims_sha256, codePrims_shake256]

/-- `H` / `T_ℓ`: SHA-512 needs its input `PK.seed ‖ toByte(0, 128 − n) ‖
    ADRS_c ‖ M` to be shorter than `2^61` bytes. -/
theorem fipsHT_code (pkSeed adrs m : List ℕ) (hpk : pkSeed.length ≤ 128)
    (hm : usesSha512 P → m.length < 2 ^ 60) :
    Hash.fipsHT codePrims P pkSeed adrs m = Hash.fipsHT specPrims P pkSeed adrs m := by
  unfold Hash.fipsHT
  rcases h : P.hash with _ | _
  · simp only
    split_ifs with hn
    · rw [codePrims_sha256]
    · have hm' := hm ⟨h, hn⟩
      have hc := compress_length_le adrs
      rw [codePrims_sha512]
      simp only [List.length_append, fipsToByte_length] at hc ⊢
      omega
  · simp only
    rw [codePrims_shake256]

/-- `PRF_msg`: HMAC-SHA-512 needs a key shorter than `2^61` bytes and a
    text shorter than `2^61 − 256` bytes. -/
theorem fipsPRFmsg_code (skPrf optRand M : List ℕ)
    (h : usesSha512 P → skPrf.length < 2 ^ 60 ∧ (optRand ++ M).length < 2 ^ 60) :
    Hash.fipsPRFmsg codePrims P skPrf optRand M = Hash.fipsPRFmsg specPrims P skPrf optRand M := by
  unfold Hash.fipsPRFmsg
  rcases hh : P.hash with _ | _
  · simp only
    split_ifs with hn
    · rw [codePrims_hmacSha256]
    · obtain ⟨h1, h2⟩ := h ⟨hh, hn⟩
      rw [codePrims_hmacSha512 _ _ (by omega) (by omega)]
  · simp only
    rw [codePrims_shake256]

/-- `H_msg`: SHA-512 needs `R ‖ PK.seed ‖ PK.root ‖ M` shorter than `2^61`
    bytes; MGF1 needs `m ≤ 2^32·hLen` (and, for SHA-512, a seed shorter than
    `2^61 − 4` bytes). -/
theorem fipsHmsg_code (hmP : P.m ≤ 2 ^ 32 * 32) (R pkSeed pkRoot M : List ℕ)
    (h : usesSha512 P → (R ++ pkSeed ++ pkRoot ++ M).length < 2 ^ 60) :
    Hash.fipsHmsg codePrims P R pkSeed pkRoot M = Hash.fipsHmsg specPrims P R pkSeed pkRoot M := by
  unfold Hash.fipsHmsg
  rcases hh : P.hash with _ | _
  · simp only
    split_ifs with hn
    · rw [codePrims_sha256, codePrims_mgf1Sha256 _ hmP]
    · have h1 := h ⟨hh, hn⟩
      simp only [List.length_append] at h1
      rw [codePrims_mgf1Sha512 _ (by omega) _
          (by simp only [List.length_append, codePrims_sha512_length]; omega),
        codePrims_sha512 _ (by simp only [List.length_append]; omega)]
  · simp only
    rw [codePrims_shake256]

end CodeSpec

/-! ## The code's hash family and `HashOk` -/

/-- The hash family of `slhdsa_engine.ml` for parameter set `P`, over the
    OCaml models of `Slhdsa_hash`. -/
def codeFam (P : Params) : Top.HashFam := Top.HashFam.ofPrims codePrims P

theorem truncate_nbytes (n : ℕ) (v : List ℕ) (hv : n ≤ v.length) (hb : ∀ b ∈ v, b < 256) :
    Hypertree.NBytes n (Hash.truncate n v) := by
  unfold Hash.truncate
  split_ifs with h
  · exact ⟨h, hb⟩
  · exact ⟨by simp; omega, fun b hb' => hb b (List.mem_of_mem_take hb')⟩

/-- **`HashOk` for the concrete primitives.** For all twelve parameter sets,
    the code's `thash` returns `n` bytes and `hash_message` returns `m`
    bytes (SHA-256/SHA-512 give 32/64 bytes, truncated to `n ≤ 32`;
    `shake256 ~output_length:n`/`m` gives `n`/`m` bytes; MGF1 gives `m`
    bytes), all `< 256`. -/
theorem hashOk_code (P : Params) (hP : P ∈ allParams) : Top.HashOk (codeFam P) P := by
  have hn : P.n ≤ 32 := by rcases n_cases P hP with h | h | h <;> omega
  constructor
  · intro pk a bs
    show Hypertree.NBytes P.n (Hash.thash codePrims P pk a bs)
    unfold Hash.thash
    rcases h : P.hash with _ | _
    · simp only
      split_ifs
      · exact truncate_nbytes _ _ (by rw [codePrims_sha512_length]; omega) (codePrims_sha512_lt _)
      · exact truncate_nbytes _ _ (by rw [codePrims_sha256_length]; omega) (codePrims_sha256_lt _)
    · exact ⟨codePrims_shake256_length _ _, codePrims_shake256_lt _ _⟩
  · intro R pk root M
    show (Hash.hashMessage codePrims P R pk root M).length = P.m ∧
      ∀ x ∈ Hash.hashMessage codePrims P R pk root M, x < 256
    unfold Hash.hashMessage
    rcases h : P.hash with _ | _
    · simp only
      split_ifs
      · exact ⟨codePrims_mgf1Sha256_length _ _, codePrims_mgf1Sha256_lt _ _⟩
      · exact ⟨codePrims_mgf1Sha512_length _ _, codePrims_mgf1Sha512_lt _ _⟩
    · exact ⟨codePrims_shake256_length _ _, codePrims_shake256_lt _ _⟩

/-- `prf_message` returns `n` bytes (used to bound the inputs of `H_msg`). -/
theorem prfMessage_length (P : Params) (hP : P ∈ allParams) (skPrf r M : List ℕ) :
    (Hash.prfMessage codePrims P skPrf r M).length = P.n := by
  have hn : P.n ≤ 32 := by rcases n_cases P hP with h | h | h <;> omega
  unfold Hash.prfMessage
  rcases h : P.hash with _ | _
  · simp only
    split_ifs
    · exact (truncate_nbytes _ _ (by rw [codePrims_hmacSha256_length]; omega)
        (codePrims_hmacSha256_lt _ _)).1
    · exact (truncate_nbytes _ _ (by rw [codePrims_hmacSha512_length]; omega)
        (codePrims_hmacSha512_lt _ _)).1
  · exact codePrims_shake256_length _ _

end OcamlPq.EndToEnd.SLHDSA
