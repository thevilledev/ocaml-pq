import OcamlPq.Common.Int

/-!
# SLH-DSA parameter sets and derived sizes

Models the functor argument `PARAMETERS` and the derived constants of
`Make` in `slhdsa/slhdsa_engine.ml` (lines 13–22, 95–119), and the twelve
parameter sets at lines 735–865. Checks them against FIPS 205 Table 2 and
the length formulas of FIPS 205 §5 and §9–10.
-/

namespace OcamlPq.SLHDSA

/-- The hash family of a parameter set (`` `Sha2 | `Shake``). -/
inductive HashFamily
  | sha2
  | shake
  deriving DecidableEq, Repr

/-- The functor argument `PARAMETERS` (slhdsa_engine.ml 13–22). -/
structure Params where
  hash : HashFamily
  n : ℕ
  h : ℕ
  d : ℕ
  a : ℕ
  k : ℕ
  m : ℕ
  deriving DecidableEq, Repr

namespace Params

variable (P : Params)

/-! ## Derived constants (slhdsa_engine.ml 95–113) -/

/-- `wots_w = 16` (line 95). -/
def wotsW (_P : Params) : ℕ := 16
/-- `wots_len1 = 2 * P.n` (line 96). -/
def len1 : ℕ := 2 * P.n
/-- `wots_len2 = 3` (line 97). -/
def len2 (_P : Params) : ℕ := 3
/-- `wots_len = wots_len1 + wots_len2` (line 98). -/
def len : ℕ := P.len1 + P.len2
/-- `tree_height = P.h / P.d` (line 99), FIPS 205's `h′`. -/
def treeHeight : ℕ := P.h / P.d
/-- `fors_message_bytes = ((P.k * P.a) + 7) / 8` (line 100). -/
def forsMessageBytes : ℕ := (P.k * P.a + 7) / 8
/-- `tree_bits = tree_height * (P.d - 1)` (line 101). -/
def treeBits : ℕ := P.treeHeight * (P.d - 1)
/-- `tree_bytes = (tree_bits + 7) / 8` (line 102). -/
def treeBytes : ℕ := (P.treeBits + 7) / 8
/-- `leaf_bytes = (tree_height + 7) / 8` (line 103). -/
def leafBytes : ℕ := (P.treeHeight + 7) / 8
/-- `seed_size = 3 * P.n` (line 105). -/
def seedSize : ℕ := 3 * P.n
/-- `signing_key_size = 4 * P.n` (line 106). -/
def signingKeySize : ℕ := 4 * P.n
/-- `verification_key_size = 2 * P.n` (line 107). -/
def verificationKeySize : ℕ := 2 * P.n
/-- `fors_signature_size = P.k * (P.a + 1) * P.n` (line 108). -/
def forsSignatureSize : ℕ := P.k * (P.a + 1) * P.n
/-- `wots_signature_size = wots_len * P.n` (line 109). -/
def wotsSignatureSize : ℕ := P.len * P.n
/-- `signature_size` (lines 111–113). -/
def signatureSize : ℕ :=
  P.n + P.forsSignatureSize + P.d * (P.wotsSignatureSize + P.treeHeight * P.n)

/-- The three module-initialisation checks (lines 115–119) succeed. -/
def initChecksPass : Prop :=
  P.h % P.d = 0 ∧ P.forsMessageBytes + P.treeBytes + P.leafBytes = P.m ∧ P.treeBits ≤ 64

instance : Decidable P.initChecksPass := by unfold initChecksPass; infer_instance

/-! ## FIPS 205 formulas -/

/-- FIPS 205 §5 eq. (5.1)–(5.4) with `lg_w = 4`: `len1 = ⌈8n / lg_w⌉`. -/
def fipsLen1 : ℕ := (8 * P.n + 3) / 4
/-- FIPS 205 eq. (5.3): `len2 = ⌊log₂(len1 · (w − 1)) / lg_w⌋ + 1`. -/
def fipsLen2 : ℕ := Nat.log 2 (P.fipsLen1 * 15) / 4 + 1
/-- FIPS 205 Algorithm 19 line 7: `⌈(h − h/d)/8⌉` bytes of tree index. -/
def fipsTreeBytes : ℕ := (P.h - P.h / P.d + 7) / 8
/-- FIPS 205 Algorithm 19 line 8: `⌈h/(8d)⌉` bytes of leaf index. -/
def fipsLeafBytes : ℕ := (P.h + 8 * P.d - 1) / (8 * P.d)
/-- FIPS 205 Algorithm 20 line 1: the signature length `(1 + k(1 + a) + h + d·len)·n`. -/
def fipsSignatureSize : ℕ := (1 + P.k * (1 + P.a) + P.h + P.d * (P.fipsLen1 + P.fipsLen2)) * P.n

end Params

/-! ## The twelve parameter sets (slhdsa_engine.ml 735–865) -/

/-- `Sha2_128s` (lines 735–744). -/
def sha2_128s : Params := ⟨.sha2, 16, 63, 7, 12, 14, 30⟩
/-- `Sha2_128f` (lines 746–755). -/
def sha2_128f : Params := ⟨.sha2, 16, 66, 22, 6, 33, 34⟩
/-- `Sha2_192s` (lines 757–766). -/
def sha2_192s : Params := ⟨.sha2, 24, 63, 7, 14, 17, 39⟩
/-- `Sha2_192f` (lines 768–777). -/
def sha2_192f : Params := ⟨.sha2, 24, 66, 22, 8, 33, 42⟩
/-- `Sha2_256s` (lines 779–788). -/
def sha2_256s : Params := ⟨.sha2, 32, 64, 8, 14, 22, 47⟩
/-- `Sha2_256f` (lines 790–799). -/
def sha2_256f : Params := ⟨.sha2, 32, 68, 17, 9, 35, 49⟩
/-- `Shake_128s` (lines 801–810). -/
def shake_128s : Params := ⟨.shake, 16, 63, 7, 12, 14, 30⟩
/-- `Shake_128f` (lines 812–821). -/
def shake_128f : Params := ⟨.shake, 16, 66, 22, 6, 33, 34⟩
/-- `Shake_192s` (lines 823–832). -/
def shake_192s : Params := ⟨.shake, 24, 63, 7, 14, 17, 39⟩
/-- `Shake_192f` (lines 834–843). -/
def shake_192f : Params := ⟨.shake, 24, 66, 22, 8, 33, 42⟩
/-- `Shake_256s` (lines 845–854). -/
def shake_256s : Params := ⟨.shake, 32, 64, 8, 14, 22, 47⟩
/-- `Shake_256f` (lines 856–865). -/
def shake_256f : Params := ⟨.shake, 32, 68, 17, 9, 35, 49⟩

/-- All twelve parameter sets instantiated by the library. -/
def allParams : List Params :=
  [sha2_128s, sha2_128f, sha2_192s, sha2_192f, sha2_256s, sha2_256f,
   shake_128s, shake_128f, shake_192s, shake_192f, shake_256s, shake_256f]

/-- A row of FIPS 205 Table 2: `(n, h, d, h′, a, k, lg_w, m, pk bytes, sig bytes)`. -/
structure Table2Row where
  n : ℕ
  h : ℕ
  d : ℕ
  h' : ℕ
  a : ℕ
  k : ℕ
  lgw : ℕ
  m : ℕ
  pkBytes : ℕ
  sigBytes : ℕ
  deriving DecidableEq, Repr

/-- FIPS 205 Table 2, in the order 128s, 128f, 192s, 192f, 256s, 256f (the
    table is the same for the SHA2 and SHAKE instantiations). -/
def table2 : List Table2Row :=
  [⟨16, 63, 7, 9, 12, 14, 4, 30, 32, 7856⟩,
   ⟨16, 66, 22, 3, 6, 33, 4, 34, 32, 17088⟩,
   ⟨24, 63, 7, 9, 14, 17, 4, 39, 48, 16224⟩,
   ⟨24, 66, 22, 3, 8, 33, 4, 42, 48, 35664⟩,
   ⟨32, 64, 8, 8, 14, 22, 4, 47, 64, 29792⟩,
   ⟨32, 68, 17, 4, 9, 35, 4, 49, 64, 49856⟩]

/-- The row of Table 2 that a code parameter set realises. -/
def Params.table2Row (P : Params) : Table2Row :=
  ⟨P.n, P.h, P.d, P.treeHeight, P.a, P.k, 4, P.m, P.verificationKeySize, P.signatureSize⟩

/-- The SHA2 parameter sets match FIPS 205 Table 2 row by row (including
    `h′ = h/d`, the public-key size `2n` and the signature size). -/
theorem sha2_table2 :
    [sha2_128s, sha2_128f, sha2_192s, sha2_192f, sha2_256s, sha2_256f].map
      Params.table2Row = table2 := by decide +kernel

/-- The SHAKE parameter sets match FIPS 205 Table 2 row by row. -/
theorem shake_table2 :
    [shake_128s, shake_128f, shake_192s, shake_192f, shake_256s, shake_256f].map
      Params.table2Row = table2 := by decide +kernel

theorem hash_families :
    [sha2_128s, sha2_128f, sha2_192s, sha2_192f, sha2_256s, sha2_256f].all
      (·.hash = .sha2) ∧
    [shake_128s, shake_128f, shake_192s, shake_192f, shake_256s, shake_256f].all
      (·.hash = .shake) := by decide +kernel

/-- The module-initialisation checks (lines 115–119) pass for all twelve sets,
    so `Make` never raises `Invalid_argument` at initialisation. -/
theorem initChecks_all : ∀ P ∈ allParams, P.initChecksPass := by decide +kernel

/-- Every parameter set uses one of the three values `n ∈ {16, 24, 32}`. -/
theorem n_cases : ∀ P ∈ allParams, P.n = 16 ∨ P.n = 24 ∨ P.n = 32 := by decide +kernel

section log

private theorem log2_480 : Nat.log 2 480 = 8 := by
  rw [Nat.log_eq_iff (by norm_num)]; norm_num
private theorem log2_720 : Nat.log 2 720 = 9 := by
  rw [Nat.log_eq_iff (by norm_num)]; norm_num
private theorem log2_960 : Nat.log 2 960 = 9 := by
  rw [Nat.log_eq_iff (by norm_num)]; norm_num

/-- `wots_len1 = 2n` and `wots_len2 = 3` agree with the FIPS 205 formulas
    (5.1)–(5.4) for `lg_w = 4` for every parameter set. -/
theorem len_fips : ∀ P ∈ allParams, P.len1 = P.fipsLen1 ∧ P.len2 = P.fipsLen2 := by
  intro P hP
  simp only [allParams, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Params.len1, Params.len2, Params.fipsLen1, Params.fipsLen2, sha2_128s, sha2_128f,
      sha2_192s, sha2_192f, sha2_256s, sha2_256f, shake_128s, shake_128f, shake_192s,
      shake_192f, shake_256s, shake_256f, log2_480, log2_720, log2_960]

/-- The signature size equals FIPS 205's `(1 + k(1 + a) + h + d·len)·n`
    (Algorithm 20 line 1) for every parameter set. -/
theorem signatureSize_fips : ∀ P ∈ allParams, P.signatureSize = P.fipsSignatureSize := by
  intro P hP
  simp only [allParams, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Params.signatureSize, Params.fipsSignatureSize, Params.fipsLen1, Params.fipsLen2,
      Params.forsSignatureSize, Params.wotsSignatureSize, Params.len, Params.len1,
      Params.len2, Params.treeHeight, sha2_128s, sha2_128f,
      sha2_192s, sha2_192f, sha2_256s, sha2_256f, shake_128s, shake_128f, shake_192s,
      shake_192f, shake_256s, shake_256f, log2_480, log2_720, log2_960]

end log

/-- The digest split sizes agree with FIPS 205 Algorithm 19 lines 6–8:
    `fors_message_bytes = ⌈k·a/8⌉`, `tree_bits = h − h/d`,
    `tree_bytes = ⌈(h − h/d)/8⌉`, `leaf_bytes = ⌈h/(8d)⌉`. -/
theorem digest_split_fips : ∀ P ∈ allParams,
    P.treeBits = P.h - P.h / P.d ∧ P.treeBytes = P.fipsTreeBytes ∧
      P.leafBytes = P.fipsLeafBytes := by decide +kernel

/-- For every `d ∣ h`, `tree_bits = (h/d)·(d − 1)` equals FIPS 205's `h − h/d`. -/
theorem treeBits_eq (P : Params) (hd : P.d ∣ P.h) : P.treeBits = P.h - P.h / P.d := by
  obtain ⟨q, hq⟩ := hd
  unfold Params.treeBits Params.treeHeight
  rcases Nat.eq_zero_or_pos P.d with h0 | hpos
  · simp [h0] at hq ⊢; exact hq.symm
  · rw [hq, Nat.mul_div_cancel_left _ hpos, Nat.mul_sub, mul_one, mul_comm]

/-- The per-set constants that bound the integer intermediates of the code:
    everything that is later used as an OCaml `int` is far below `2^30`. -/
theorem sizes_portable : ∀ P ∈ allParams,
    P.signatureSize < 2 ^ 30 ∧ P.k * 2 ^ P.a < 2 ^ 30 ∧ 2 ^ P.treeHeight < 2 ^ 30 ∧
      P.a ≤ 14 ∧ P.treeHeight ≤ 9 ∧ P.d ≤ 22 ∧ 1 ≤ P.treeHeight ∧ 1 ≤ P.a ∧
      P.len ≤ 67 ∧ 1 ≤ P.d ∧ P.k ≥ 2 := by decide +kernel

/-- `k·a + 7 ≤ 8·fors_message_bytes`, i.e. the FORS digest has at least the
    `k·a` bits that `base_2b` consumes, and exactly `⌈k·a/8⌉` bytes. -/
theorem forsMessageBytes_spec (P : Params) :
    P.k * P.a ≤ 8 * P.forsMessageBytes ∧ 8 * P.forsMessageBytes < P.k * P.a + 8 := by
  unfold Params.forsMessageBytes; omega

end OcamlPq.SLHDSA
