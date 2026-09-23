import OcamlPq.MLDSA.Arith

/-!
# NTT constants: `bit_reverse_8`, `zetas`, `inverse_n`

Models of mldsa/mldsa_engine.ml:196–204 and the FIPS 204 constants they
must equal (§7.5 and Appendix B): `zetas[k] = ζ^BitRev8(k) mod q` with
`ζ = 1753` a primitive 512-th root of unity, and `256⁻¹ = 8347681`.
-/

namespace OcamlPq.MLDSA

/-- `ℤ_q`. -/
abbrev Zq := ZMod 8380417

/-! ## Bit reversal -/

/-- Model of `bit_reverse_8` (mldsa/mldsa_engine.ml:196–201):
    `for bit = 0 to 7 do result := (!result lsl 1) lor ((value lsr bit) land 1) done`. -/
def bitReverse8 (value : ℕ) : ℕ :=
  (List.range 8).foldl (fun result bit => (result <<< 1) ||| ((value >>> bit) &&& 1)) 0

/-- FIPS 204 `BitRev8(m)` (§2.3): if `m = b0 + 2 b1 + … + 128 b7` then
    `BitRev8(m) = b7 + 2 b6 + … + 128 b0`. -/
def bitRev8 (m : ℕ) : ℕ := ((List.range 8).map fun i => (m / 2 ^ i % 2) * 2 ^ (7 - i)).sum

theorem bitReverse8_eq_bitRev8 : ∀ m < 256, bitReverse8 m = bitRev8 m := by decide +kernel

theorem bitRev8_lt : ∀ m < 256, bitRev8 m < 256 := by decide +kernel

/-- The result of `bit_reverse_8` stays below `2^8`. -/
theorem bitReverse8_lt : ∀ m < 256, bitReverse8 m < 256 := by decide +kernel

/-- Every intermediate `!result` of `bit_reverse_8` (after `n` iterations)
    is below `2^n ≤ 256`, so `!result lsl 1 < 512` is portable. -/
theorem bitReverse8_intermediate_lt : ∀ m < 256, ∀ n ≤ 8,
    (List.range n).foldl (fun result bit => (result <<< 1) ||| ((m >>> bit) &&& 1)) 0 < 2 ^ n := by
  decide +kernel

/-! ## `zetas` -/

/-- Model of the `zetas` table (mldsa/mldsa_engine.ml:203):
    `Array.init n (fun index -> pow_mod 1753 (bit_reverse_8 index))`. -/
def zetas (index : ℕ) : ℤ := powMod 1753 (bitReverse8 index)

/-- `ζ = 1753` (FIPS 204 §7.5). -/
def ζ : Zq := 1753

/-- FIPS 204 `zetas[k] = ζ^BitRev8(k) mod q` (§7.5, Appendix B). -/
def zetaSpec (k : ℕ) : Zq := ζ ^ bitRev8 k

theorem zetas_eq (k : ℕ) (hk : k < 256) : zetas k = 1753 ^ bitRev8 k % q := by
  rw [zetas, powMod_eq, bitReverse8_eq_bitRev8 k hk]

theorem zetas_cast (k : ℕ) (hk : k < 256) : ((zetas k : ℤ) : Zq) = zetaSpec k := by
  rw [zetas, powMod_cast, bitReverse8_eq_bitRev8 k hk, zetaSpec, ζ]; push_cast; rfl

theorem zetas_nonneg (k : ℕ) : 0 ≤ zetas k := by
  rw [zetas, powMod_eq]; exact Int.emod_nonneg _ (by decide)

theorem zetas_lt (k : ℕ) : zetas k < q := by
  rw [zetas, powMod_eq]; exact Int.emod_lt_of_pos _ q_pos

/-- Spot checks against the table in FIPS 204 Appendix B (entries 1–15). -/
theorem zetas_appendixB :
    zetas 1 = 4808194 ∧ zetas 2 = 3765607 ∧ zetas 3 = 3761513 ∧ zetas 4 = 5178923 ∧
    zetas 5 = 5496691 ∧ zetas 6 = 5234739 ∧ zetas 7 = 5178987 ∧ zetas 8 = 7778734 ∧
    zetas 9 = 3542485 ∧ zetas 10 = 2682288 ∧ zetas 11 = 2129892 ∧ zetas 12 = 3764867 ∧
    zetas 13 = 7375178 ∧ zetas 14 = 557458 ∧ zetas 15 = 7159240 := by
  simp only [zetas_eq _ (by norm_num : (1 : ℕ) < 256), zetas_eq _ (by norm_num : (2 : ℕ) < 256),
    zetas_eq _ (by norm_num : (3 : ℕ) < 256), zetas_eq _ (by norm_num : (4 : ℕ) < 256),
    zetas_eq _ (by norm_num : (5 : ℕ) < 256), zetas_eq _ (by norm_num : (6 : ℕ) < 256),
    zetas_eq _ (by norm_num : (7 : ℕ) < 256), zetas_eq _ (by norm_num : (8 : ℕ) < 256),
    zetas_eq _ (by norm_num : (9 : ℕ) < 256), zetas_eq _ (by norm_num : (10 : ℕ) < 256),
    zetas_eq _ (by norm_num : (11 : ℕ) < 256), zetas_eq _ (by norm_num : (12 : ℕ) < 256),
    zetas_eq _ (by norm_num : (13 : ℕ) < 256), zetas_eq _ (by norm_num : (14 : ℕ) < 256),
    zetas_eq _ (by norm_num : (15 : ℕ) < 256), q]
  decide

/-! ## `ζ` is a primitive 512-th root of unity -/

theorem zeta_pow_256 : ζ ^ 256 = -1 := by
  rw [eq_neg_iff_add_eq_zero, ζ]
  have h : ((1753 ^ 256 + 1 : ℕ) : Zq) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; decide
  exact_mod_cast h

theorem zeta_pow_512 : ζ ^ 512 = 1 := by
  rw [show 512 = 256 * 2 by rfl, pow_mul, zeta_pow_256]; norm_num

theorem neg_one_ne_one : (-1 : Zq) ≠ 1 := by decide

theorem zeta_orderOf : orderOf ζ = 512 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 8) (x := ζ)
    (by rw [show 2 ^ 8 = 256 by rfl, zeta_pow_256]; exact neg_one_ne_one)
    (by rw [show 2 ^ (8 + 1) = 512 by rfl, zeta_pow_512])
  rw [h]; rfl

/-- Powers of `ζ` below 512 are pairwise distinct. -/
theorem zeta_pow_inj {a b : ℕ} (ha : a < 512) (hb : b < 512) (h : ζ ^ a = ζ ^ b) : a = b := by
  have := pow_injOn_Iio_orderOf (x := ζ)
  rw [zeta_orderOf] at this
  exact this ha hb h

theorem zeta_pow_mod (n : ℕ) : ζ ^ n = ζ ^ (n % 512) := by
  conv_lhs => rw [← Nat.div_add_mod n 512, pow_add, pow_mul, zeta_pow_512, one_pow, one_mul]

/-! ## `inverse_n` -/

/-- Model of `inverse_n` (mldsa/mldsa_engine.ml:204): `pow_mod n (q - 2)`. -/
def inverseN : ℤ := powMod 256 (q - 2).toNat

/-- Fermat: `256^(q-2) = 8347681` in `ℤ_q`. -/
theorem pow_256_q_sub_two : (256 : Zq) ^ 8380415 = 8347681 := by
  have h1 : (256 : Zq) ^ (8380417 - 1) = 1 := ZMod.pow_card_sub_one_eq_one (by decide)
  have h2 : (256 : Zq) ^ 8380415 * 256 = 1 := by rw [← pow_succ]; exact h1
  have h3 : (8347681 : Zq) * 256 = 1 := by decide
  have hu : IsUnit (256 : Zq) := IsUnit.of_mul_eq_one (8347681 : Zq) (by rw [mul_comm]; exact h3)
  exact hu.mul_left_cancel (by rw [mul_comm, h2, mul_comm, h3])

theorem inverseN_eq : inverseN = 8347681 := by
  have h0 : 0 ≤ inverseN := by rw [inverseN, powMod_eq]; exact Int.emod_nonneg _ (by decide)
  have h1 : inverseN < q := by rw [inverseN, powMod_eq]; exact Int.emod_lt_of_pos _ q_pos
  have hcast : ((inverseN : ℤ) : Zq) = ((8347681 : ℤ) : Zq) := by
    rw [inverseN, powMod_cast, show (q - 2).toNat = 8380415 by rfl]
    push_cast
    exact pow_256_q_sub_two
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
  simp only [q] at h1
  push_cast at hcast
  omega

/-- `inverse_n = 256⁻¹` in `ℤ_q` (FIPS 204 Algorithm 42, `f = 8347681`). -/
theorem inverseN_mul : ((inverseN : ℤ) : Zq) * 256 = 1 := by
  rw [inverseN_eq]; decide

end OcamlPq.MLDSA
