import OcamlPq.SLHDSA.Address

/-!
# SLH-DSA: instantiation of the hash functions (FIPS 205 §11)

Models `sha2_prefix`, `thash`, `prf`, `prf_message` and `hash_message`
(slhdsa_engine.ml 213–268) over *abstract* SHA-256, SHA-512, SHAKE256,
HMAC and MGF1 primitives (those are verified elsewhere), and proves that
they compute FIPS 205's `F`, `H`, `T_ℓ`, `PRF`, `PRF_msg`, `H_msg` of §11.1
(SHAKE), §11.2.1 (SHA2, category 1, `n = 16`) and §11.2.2 (SHA2,
categories 3 and 5, `n ∈ {24, 32}`), for the ADRS encoding `address_full`
(and `ADRS_c = address_compressed`).

In particular the SHA2 selection `P.n >= 24 && List.length input_blocks > 1`
realises "F and PRF use SHA-256 for all `n`; H and `T_ℓ` use SHA-512 for
`n ∈ {24, 32}` and SHA-256 for `n = 16`" at every call site: `F` is always
called with one block, `H` with two, `T_len` with `len = 2n + 3 ≥ 35`
blocks and `T_k` with `k ≥ 14` blocks.
-/

namespace OcamlPq.SLHDSA.Hash

open Base2b

/-- The external primitives (`Slhdsa_hash`), abstract. -/
structure Prims where
  sha256 : List ℕ → List ℕ
  sha512 : List ℕ → List ℕ
  /-- `shake256 ~output_length input`. -/
  shake256 : ℕ → List ℕ → List ℕ
  /-- `hmac_sha256 key message`. -/
  hmacSha256 : List ℕ → List ℕ → List ℕ
  hmacSha512 : List ℕ → List ℕ → List ℕ
  /-- `mgf1_sha256 ~output_length seed`. -/
  mgf1Sha256 : ℕ → List ℕ → List ℕ
  mgf1Sha512 : ℕ → List ℕ → List ℕ

variable (pr : Prims) (P : Params)

/-! ## Code models (lines 157–158, 213–268) -/

section Code

/-- `truncate length value` (157–158); `String.sub value 0 length` (the
    SHA-256/512 outputs are 32/64 bytes, never shorter than `n`). -/
def truncate (length : ℕ) (value : List ℕ) : List ℕ :=
  if value.length = length then value else value.take length

/-- `sha2_prefix block_size seed` (213–214). -/
def sha2Prefix (blockSize : ℕ) (seed : List ℕ) : List ℕ :=
  seed ++ List.replicate (blockSize - seed.length) 0

/-- `thash context address input_blocks` (216–230). -/
def thash (pkSeed : List ℕ) (address : Address) (inputBlocks : List (List ℕ)) : List ℕ :=
  let input := inputBlocks.flatten
  match P.hash with
  | .shake => pr.shake256 P.n (pkSeed ++ Code.addressFull address ++ input)
  | .sha2 =>
    if decide (P.n ≥ 24) && decide (inputBlocks.length > 1) then
      truncate P.n (pr.sha512 (sha2Prefix 128 pkSeed ++ Code.addressCompressed address ++ input))
    else
      truncate P.n (pr.sha256 (sha2Prefix 64 pkSeed ++ Code.addressCompressed address ++ input))

/-- `prf context address` (232–241). -/
def prf (pkSeed skSeed : List ℕ) (address : Address) : List ℕ :=
  match P.hash with
  | .shake => pr.shake256 P.n (pkSeed ++ Code.addressFull address ++ skSeed)
  | .sha2 =>
    truncate P.n (pr.sha256 (sha2Prefix 64 pkSeed ++ Code.addressCompressed address ++ skSeed))

/-- `prf_message sk_prf randomness message` (243–252). -/
def prfMessage (skPrf randomness message : List ℕ) : List ℕ :=
  match P.hash with
  | .shake => pr.shake256 P.n (skPrf ++ randomness ++ message)
  | .sha2 =>
    truncate P.n (if P.n = 16 then pr.hmacSha256 skPrf (randomness ++ message)
      else pr.hmacSha512 skPrf (randomness ++ message))

/-- `hash_message randomizer verification_key message` (254–268). -/
def hashMessage (randomizer pkSeed pkRoot message : List ℕ) : List ℕ :=
  let publicKey := pkSeed ++ pkRoot
  match P.hash with
  | .shake => pr.shake256 P.m (randomizer ++ publicKey ++ message)
  | .sha2 =>
    let digest :=
      if P.n = 16 then pr.sha256 (randomizer ++ publicKey ++ message)
      else pr.sha512 (randomizer ++ publicKey ++ message)
    let seed := randomizer ++ pkSeed ++ digest
    if P.n = 16 then pr.mgf1Sha256 P.m seed else pr.mgf1Sha512 P.m seed

end Code

/-! ## FIPS 205 §11 -/

section Spec

/-- `Trunc_n`: the first `n` bytes. -/
def trunc (n : ℕ) (x : List ℕ) : List ℕ := x.take n

/-- `F(PK.seed, ADRS, M₁)` (§11.1, §11.2.1, §11.2.2). -/
def fipsF (pkSeed adrs m1 : List ℕ) : List ℕ :=
  match P.hash with
  | .shake => pr.shake256 P.n (pkSeed ++ adrs ++ m1)
  | .sha2 => trunc P.n (pr.sha256 (pkSeed ++ fipsToByte 0 (64 - P.n) ++ FipsADRS.compress adrs ++ m1))

/-- `H(PK.seed, ADRS, M₂)` and `T_ℓ(PK.seed, ADRS, M_ℓ)` (identical
    definitions in §11.1, §11.2.1, §11.2.2). -/
def fipsHT (pkSeed adrs m : List ℕ) : List ℕ :=
  match P.hash with
  | .shake => pr.shake256 P.n (pkSeed ++ adrs ++ m)
  | .sha2 =>
    if P.n = 16 then
      trunc P.n (pr.sha256 (pkSeed ++ fipsToByte 0 (64 - P.n) ++ FipsADRS.compress adrs ++ m))
    else
      trunc P.n (pr.sha512 (pkSeed ++ fipsToByte 0 (128 - P.n) ++ FipsADRS.compress adrs ++ m))

/-- `PRF(PK.seed, SK.seed, ADRS)`. -/
def fipsPRF (pkSeed skSeed adrs : List ℕ) : List ℕ :=
  match P.hash with
  | .shake => pr.shake256 P.n (pkSeed ++ adrs ++ skSeed)
  | .sha2 =>
    trunc P.n (pr.sha256 (pkSeed ++ fipsToByte 0 (64 - P.n) ++ FipsADRS.compress adrs ++ skSeed))

/-- `PRF_msg(SK.prf, opt_rand, M)`. -/
def fipsPRFmsg (skPrf optRand M : List ℕ) : List ℕ :=
  match P.hash with
  | .shake => pr.shake256 P.n (skPrf ++ optRand ++ M)
  | .sha2 =>
    if P.n = 16 then trunc P.n (pr.hmacSha256 skPrf (optRand ++ M))
    else trunc P.n (pr.hmacSha512 skPrf (optRand ++ M))

/-- `H_msg(R, PK.seed, PK.root, M)`. -/
def fipsHmsg (R pkSeed pkRoot M : List ℕ) : List ℕ :=
  match P.hash with
  | .shake => pr.shake256 P.m (R ++ pkSeed ++ pkRoot ++ M)
  | .sha2 =>
    if P.n = 16 then pr.mgf1Sha256 P.m (R ++ pkSeed ++ pr.sha256 (R ++ pkSeed ++ pkRoot ++ M))
    else pr.mgf1Sha512 P.m (R ++ pkSeed ++ pr.sha512 (R ++ pkSeed ++ pkRoot ++ M))

end Spec

/-! ## Theorems -/

theorem truncate_eq (len : ℕ) (x : List ℕ) : truncate len x = trunc len x := by
  unfold truncate trunc
  split_ifs with h
  · rw [List.take_of_length_le (by omega)]
  · rfl

theorem fipsToByte_zero (k : ℕ) : fipsToByte 0 k = List.replicate k 0 := by
  rw [fipsToByte_eq]
  apply List.ext_getElem <;> simp

theorem sha2Prefix_eq (bs : ℕ) (seed : List ℕ) :
    sha2Prefix bs seed = seed ++ fipsToByte 0 (bs - seed.length) := by
  rw [sha2Prefix, fipsToByte_zero]

/-- The layer and type fit in a byte, so `address_compressed = ADRS_c`. -/
def SmallAddress (a : Address) : Prop := a.layer < 256 ∧ a.typ < 256

/-- **`thash` with one block = `F`** (every `chain` step and every FORS
    leaf), for every parameter set, every `n`-byte `PK.seed` and every
    address with `layer, type < 256`. -/
theorem thash_F (pkSeed : List ℕ) (hpk : pkSeed.length = P.n)
    (a : Address) (ha : SmallAddress a) (m1 : List ℕ) :
    thash pr P pkSeed a [m1] = fipsF pr P pkSeed (Code.addressFull a) m1 := by
  unfold thash fipsF
  rcases h : P.hash with _ | _
  · simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_singleton,
      gt_iff_lt, lt_self_iff_false, decide_false, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte, truncate_eq, sha2Prefix_eq, hpk, addressCompressed_eq a ha.1 ha.2,
      List.append_assoc]
  · simp

/-- **`thash` with two blocks = `H`** (every `treehash` / `compute_root`
    node): SHA-512 exactly when `n ∈ {24, 32}`. -/
theorem thash_H (hP : P ∈ allParams) (pkSeed : List ℕ) (hpk : pkSeed.length = P.n)
    (a : Address) (ha : SmallAddress a) (l r : List ℕ) :
    thash pr P pkSeed a [l, r] = fipsHT pr P pkSeed (Code.addressFull a) (l ++ r) := by
  unfold thash fipsHT
  rcases h : P.hash with _ | _
  · rcases n_cases P hP with hn | hn | hn <;>
      simp [hn, truncate_eq, sha2Prefix_eq, hpk, addressCompressed_eq a ha.1 ha.2]
  · simp

/-- **`thash` with `ℓ ≥ 2` blocks = `T_ℓ`** (the WOTS+ public-key
    compression with `ℓ = len` and the FORS root compression with `ℓ = k`). -/
theorem thash_T (hP : P ∈ allParams) (pkSeed : List ℕ) (hpk : pkSeed.length = P.n)
    (a : Address) (ha : SmallAddress a) (blocks : List (List ℕ)) (hb : 2 ≤ blocks.length) :
    thash pr P pkSeed a blocks = fipsHT pr P pkSeed (Code.addressFull a) blocks.flatten := by
  unfold thash fipsHT
  rcases h : P.hash with _ | _
  · have hb' : blocks.length > 1 := by omega
    rcases n_cases P hP with hn | hn | hn <;>
      simp [hn, hb', truncate_eq, sha2Prefix_eq, hpk, addressCompressed_eq a ha.1 ha.2]
  · simp

/-- `T_len` and `T_k` are always called with more than one block. -/
theorem T_arity : ∀ P ∈ allParams, 2 ≤ P.len ∧ 2 ≤ P.k := by decide +kernel

/-- **`prf` = `PRF`** (SHA-256 for every `n` in the SHA2 sets). -/
theorem prf_eq (pkSeed skSeed : List ℕ) (hpk : pkSeed.length = P.n) (a : Address)
    (ha : SmallAddress a) :
    prf pr P pkSeed skSeed a = fipsPRF pr P pkSeed skSeed (Code.addressFull a) := by
  unfold prf fipsPRF
  rcases h : P.hash with _ | _
  · simp [truncate_eq, sha2Prefix_eq, hpk, addressCompressed_eq a ha.1 ha.2]
  · simp

/-- **`prf_message` = `PRF_msg`** (HMAC-SHA-256 for `n = 16`, HMAC-SHA-512
    otherwise). -/
theorem prfMessage_eq (skPrf optRand M : List ℕ) :
    prfMessage pr P skPrf optRand M = fipsPRFmsg pr P skPrf optRand M := by
  unfold prfMessage fipsPRFmsg
  rcases h : P.hash with _ | _
  · split_ifs <;> simp [truncate_eq]
  · simp

/-- **`hash_message` = `H_msg`** (MGF1 over `R ‖ PK.seed ‖ SHA-x(R ‖ PK.seed
    ‖ PK.root ‖ M)` for SHA2, `SHAKE256(R ‖ PK.seed ‖ PK.root ‖ M, 8m)` for
    SHAKE). -/
theorem hashMessage_eq (R pkSeed pkRoot M : List ℕ) :
    hashMessage pr P R pkSeed pkRoot M = fipsHmsg pr P R pkSeed pkRoot M := by
  unfold hashMessage fipsHmsg
  rcases h : P.hash with _ | _
  · split_ifs <;> simp [List.append_assoc]
  · simp [List.append_assoc]

end OcamlPq.SLHDSA.Hash
