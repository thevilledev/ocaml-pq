import OcamlPq.Common.Int

/-!
# ML-KEM field arithmetic

Models of the scalar field operations of `lib/mlkem_engine.ml`
(lines 105–123) and proofs that they compute the operations of
`ℤ_q = ZMod 3329` (FIPS 203 §2.4) on canonical representatives.

* `fieldReduceOnce` — the `Int32` sign-mask conditional subtraction. Correct
  whenever `a - q` fits in an `Int32`; in particular for `0 ≤ a < 2q`.
* `fieldReduce` — the `Int64` Barrett reduction `a - ⌊5039a/2²⁴⌋·q`.
  Correct exactly for `0 ≤ a < 7035·q = 23 419 515` (`fieldReduce_eq_emod`,
  and `fieldReduce_first_failure` shows the bound is tight); every caller
  stays below `2q² = 22 164 482`.
* `fieldAdd`, `fieldSub`, `fieldMul`, `fieldMulSub`, `fieldAddMul` — correct
  and canonical on canonical inputs, with every `int` intermediate `Portable`.
-/

namespace OcamlPq.MLKEM

/-- The ML-KEM modulus, `let q = 3329` (`lib/mlkem_engine.ml` line 61). -/
def q : ℤ := 3329

/-- `ℤ_q` of FIPS 203. -/
abbrev Zq := ZMod 3329

instance fact_prime_3329 : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- `a` is a canonical representative of `ℤ_q`: `0 ≤ a < q`. -/
def Canon (a : ℤ) : Prop := 0 ≤ a ∧ a < q

theorem Canon.portable {a : ℤ} (h : Canon a) : Portable a := by
  unfold Canon q at h; unfold Portable; omega

theorem Canon.nonneg {a : ℤ} (h : Canon a) : 0 ≤ a := h.1

theorem Canon.lt {a : ℤ} (h : Canon a) : a < 3329 := h.2

theorem canon_emod (a : ℤ) : Canon (a % q) := by
  unfold Canon q; omega

theorem cast_emod_q (a : ℤ) : (((a % q : ℤ)) : Zq) = (a : Zq) := by
  have := ZMod.intCast_mod a 3329
  simpa [q] using this

/-- Two canonical representatives with the same image in `ℤ_q` are equal. -/
theorem Canon.eq_of_cast_eq {a b : ℤ} (ha : Canon a) (hb : Canon b)
    (h : (a : Zq) = (b : Zq)) : a = b := by
  have h' := (ZMod.intCast_eq_intCast_iff_dvd_sub a b 3329).1 h
  unfold Canon q at ha hb
  obtain ⟨k, hk⟩ := h'
  have : k = 0 := by
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · have : (3329 : ℤ) * k ≤ -3329 := by nlinarith
      push_cast at hk; omega
    · exact hk0
    · have : (3329 : ℤ) * k ≥ 3329 := by nlinarith
      push_cast at hk; omega
  subst this; push_cast at hk; omega

/-! ## `field_reduce_once` -/

/-- The sign mask `Int32.to_int (Int32.shift_right (Int32.of_int x) 31)`:
    `Int32.of_int` keeps the low 32 bits (`BitVec.ofInt 32`),
    `Int32.shift_right` is the arithmetic shift (`BitVec.sshiftRight`), and
    `Int32.to_int` sign-extends (`BitVec.toInt`). -/
def signMask32 (x : ℤ) : ℤ := ((BitVec.ofInt 32 x).sshiftRight 31).toInt

/-- Model of `field_reduce_once` (`lib/mlkem_engine.ml` lines 105–108):
```
let field_reduce_once a =
  let x = a - q in
  let sign = Int32.to_int (Int32.shift_right (Int32.of_int x) 31) in
  x + (sign land q)
```
`land` on `int` is `Int.land`. -/
def fieldReduceOnce (a : ℤ) : ℤ :=
  let x := a - q
  let sign := signMask32 x
  x + Int.land sign q

theorem signMask32_eq {x : ℤ} (h0 : -(2 ^ 31) ≤ x) (h1 : x < 2 ^ 31) :
    signMask32 x = if x < 0 then -1 else 0 := by
  unfold signMask32
  rw [BitVec.toInt_sshiftRight, BitVec.toInt_ofInt,
    Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega),
    Int.shiftRight_eq_div_pow]
  split_ifs <;> push_cast <;> omega

theorem land_neg_one_q : Int.land (-1) q = q := by unfold q; decide +kernel

theorem land_zero_q : Int.land 0 q = 0 := by unfold q; decide +kernel

/-- `field_reduce_once` is a conditional subtraction of `q` whenever `a - q`
    fits in an `Int32` (so that `Int32.of_int` does not truncate). -/
theorem fieldReduceOnce_eq_ite {a : ℤ} (h0 : -(2 ^ 31) ≤ a - q) (h1 : a - q < 2 ^ 31) :
    fieldReduceOnce a = if a < q then a else a - q := by
  unfold fieldReduceOnce
  simp only
  rw [signMask32_eq h0 h1]
  by_cases h : a - q < 0
  · have h' : a < q := by omega
    simp only [h, h', ite_true, land_neg_one_q]; ring
  · have h' : ¬ a < q := by omega
    simp only [h, h', ite_false, land_zero_q]; ring

/-- The `Int32.of_int` truncation matters: when `a - q ≥ 2³¹` (possible only
    with 63-bit native `int`) the result is not reduced. No caller does this;
    see `fieldReduceOnce_eq_emod` for the range actually used. -/
theorem fieldReduceOnce_int32_wrap : fieldReduceOnce (q + 2 ^ 31) = q + 2 ^ 31 := by
  unfold fieldReduceOnce signMask32 q; decide +kernel

/-- On `0 ≤ a < 2q`, `field_reduce_once a = a mod q`. -/
theorem fieldReduceOnce_eq_emod {a : ℤ} (h0 : 0 ≤ a) (h1 : a < 2 * q) :
    fieldReduceOnce a = a % q := by
  rw [fieldReduceOnce_eq_ite (by unfold q at *; omega) (by unfold q at *; omega)]
  unfold q at *
  split_ifs <;> omega

theorem fieldReduceOnce_canon {a : ℤ} (h0 : 0 ≤ a) (h1 : a < 2 * q) :
    Canon (fieldReduceOnce a) := by
  rw [fieldReduceOnce_eq_emod h0 h1]; exact canon_emod a

/-- Every `int` value computed by `field_reduce_once` on `0 ≤ a < 2q` is
    `Portable`: `a`, `x = a - q`, `sign`, `sign land q` and the result. -/
theorem fieldReduceOnce_portable {a : ℤ} (h0 : 0 ≤ a) (h1 : a < 2 * q) :
    Portable a ∧ Portable (a - q) ∧ Portable (signMask32 (a - q)) ∧
      Portable (Int.land (signMask32 (a - q)) q) ∧ Portable (fieldReduceOnce a) := by
  have hs := signMask32_eq (x := a - q) (by unfold q at *; omega) (by unfold q at *; omega)
  have hr := fieldReduceOnce_canon h0 h1
  refine ⟨?_, ?_, ?_, ?_, hr.portable⟩
  · unfold Portable q at *; omega
  · unfold Portable q at *; omega
  · rw [hs]; split_ifs <;> decide
  · rw [hs]; split_ifs
    · rw [land_neg_one_q]; unfold q; decide
    · rw [land_zero_q]; decide

/-! ## `field_add` and `field_sub` -/

/-- Model of `field_add` (`lib/mlkem_engine.ml` line 110). -/
def fieldAdd (a b : ℤ) : ℤ := fieldReduceOnce (a + b)

/-- Model of `field_sub` (`lib/mlkem_engine.ml` line 111). -/
def fieldSub (a b : ℤ) : ℤ := fieldReduceOnce (a - b + q)

theorem fieldAdd_eq {a b : ℤ} (ha : Canon a) (hb : Canon b) :
    fieldAdd a b = (a + b) % q := by
  unfold Canon at ha hb
  exact fieldReduceOnce_eq_emod (by omega) (by omega)

theorem fieldAdd_canon {a b : ℤ} (ha : Canon a) (hb : Canon b) : Canon (fieldAdd a b) := by
  rw [fieldAdd_eq ha hb]; exact canon_emod _

theorem fieldAdd_cast {a b : ℤ} (ha : Canon a) (hb : Canon b) :
    ((fieldAdd a b : ℤ) : Zq) = (a : Zq) + (b : Zq) := by
  rw [fieldAdd_eq ha hb, cast_emod_q]; push_cast; ring

/-- `field_sub a b = (a - b) mod q` whenever `0 ≤ a - b + q < 2q`; this covers
    canonical `a, b` and the small operands of `sample_cbd`. -/
theorem fieldSub_eq_of_range {a b : ℤ} (h0 : 0 ≤ a - b + q) (h1 : a - b + q < 2 * q) :
    fieldSub a b = (a - b) % q := by
  unfold fieldSub
  rw [fieldReduceOnce_eq_emod h0 h1]
  unfold q; omega

theorem fieldSub_eq {a b : ℤ} (ha : Canon a) (hb : Canon b) :
    fieldSub a b = (a - b) % q := by
  unfold Canon at ha hb
  exact fieldSub_eq_of_range (by omega) (by omega)

theorem fieldSub_canon_of_range {a b : ℤ} (h0 : 0 ≤ a - b + q) (h1 : a - b + q < 2 * q) :
    Canon (fieldSub a b) := by
  rw [fieldSub_eq_of_range h0 h1]; exact canon_emod _

theorem fieldSub_canon {a b : ℤ} (ha : Canon a) (hb : Canon b) : Canon (fieldSub a b) := by
  rw [fieldSub_eq ha hb]; exact canon_emod _

theorem fieldSub_cast_of_range {a b : ℤ} (h0 : 0 ≤ a - b + q) (h1 : a - b + q < 2 * q) :
    ((fieldSub a b : ℤ) : Zq) = (a : Zq) - (b : Zq) := by
  rw [fieldSub_eq_of_range h0 h1, cast_emod_q]; push_cast; ring

theorem fieldSub_cast {a b : ℤ} (ha : Canon a) (hb : Canon b) :
    ((fieldSub a b : ℤ) : Zq) = (a : Zq) - (b : Zq) := by
  unfold Canon at ha hb
  exact fieldSub_cast_of_range (by omega) (by omega)

/-- `int` intermediates of `field_add` / `field_sub` on canonical inputs. -/
theorem fieldAdd_portable {a b : ℤ} (ha : Canon a) (hb : Canon b) :
    Portable (a + b) ∧ Portable (fieldAdd a b) := by
  unfold Canon q at ha hb
  exact ⟨Portable.of_bounds (lo := 0) (hi := 6658) (by norm_num) (by norm_num) (by omega)
    (by omega), (fieldAdd_canon ha hb).portable⟩

theorem fieldSub_portable {a b : ℤ} (ha : Canon a) (hb : Canon b) :
    Portable (a - b) ∧ Portable (a - b + q) ∧ Portable (fieldSub a b) := by
  have hc := fieldSub_canon ha hb
  unfold Canon q at ha hb
  refine ⟨?_, ?_, hc.portable⟩ <;> simp only [Portable, q] <;> omega

/-! ## `field_reduce` (Barrett reduction) -/

/-- Model of `field_reduce` (`lib/mlkem_engine.ml` lines 113–117):
```
let field_reduce a =
  let open Int64 in
  let a64 = of_int a in
  let quotient = shift_right_logical (mul a64 5039L) 24 in
  field_reduce_once (to_int (sub a64 (mul quotient 3329L)))
```
`Int64` arithmetic is `BitVec 64` (wrapping), `shift_right_logical` is `>>>`
(`BitVec.ushiftRight`), and `Int64.of_int` is `BitVec.ofInt 64`. `Int64.to_int`
is modelled as `BitVec.toInt`; `fieldReduce_portable` proves the value is
`Portable`, so the platform's truncation to `int` is the identity. -/
def fieldReduce (a : ℤ) : ℤ :=
  let a64 : BitVec 64 := BitVec.ofInt 64 a
  let quotient := (a64 * 5039#64) >>> 24
  fieldReduceOnce (a64 - quotient * 3329#64).toInt

/-- The exact domain of the Barrett step: `0 ≤ a < 7035·q`. -/
def barrettBound : ℤ := 7035 * 3329

/-- Barrett estimate, arithmetic core: if `c = ⌊5039n/2²⁴⌋` and
    `n < 7035·q`, then `c` is `⌊n/q⌋` or `⌊n/q⌋ - 1`, so `n - c·q ∈ [0, 2q)`. -/
theorem barrett_core (n c : ℕ) (hc1 : c * 16777216 ≤ n * 5039)
    (hc2 : n * 5039 < c * 16777216 + 16777216) (h : n < 23419515) :
    c * 3329 ≤ n ∧ n - c * 3329 < 6658 := by
  obtain ⟨Q, R, hR, rfl⟩ : ∃ Q R, R < 3329 ∧ n = R + 3329 * Q :=
    ⟨n / 3329, n % 3329, Nat.mod_lt _ (by norm_num), (Nat.mod_add_div n 3329).symm⟩
  have hQ : Q ≤ 7034 := by omega
  have h1 : c ≤ Q := by
    by_contra hcq
    have : (Q + 1) * 16777216 ≤ c * 16777216 := Nat.mul_le_mul_right _ (by omega)
    omega
  have h2 : Q ≤ c + 1 := by
    by_contra hcq
    have : (c + 2) * 16777216 ≤ Q * 16777216 := Nat.mul_le_mul_right _ (by omega)
    omega
  omega

theorem barrett_nat (n : ℕ) (h : n < 7035 * 3329) :
    n * 5039 / 2 ^ 24 * 3329 ≤ n ∧ n - n * 5039 / 2 ^ 24 * 3329 < 2 * 3329 := by
  have hc1 : n * 5039 / 2 ^ 24 * 2 ^ 24 ≤ n * 5039 := Nat.div_mul_le_self _ _
  have hc2 : n * 5039 < n * 5039 / 2 ^ 24 * 2 ^ 24 + 2 ^ 24 := Nat.lt_div_mul_add (by norm_num)
  exact barrett_core n _ hc1 hc2 h

/-- The `Int64` value `sub a64 (mul quotient 3329L)` that `field_reduce`
    converts back to `int`. -/
def barrettRem (a : ℤ) : ℤ :=
  let a64 : BitVec 64 := BitVec.ofInt 64 a
  let quotient := (a64 * 5039#64) >>> 24
  (a64 - quotient * 3329#64).toInt

theorem fieldReduce_eq_barrettRem (a : ℤ) : fieldReduce a = fieldReduceOnce (barrettRem a) := rfl

theorem barrettRem_toNat (n : ℕ) (h : n < 7035 * 3329) :
    ((BitVec.ofNat 64 n) - (((BitVec.ofNat 64 n) * 5039#64) >>> 24) * 3329#64).toNat
      = n - n * 5039 / 2 ^ 24 * 3329 := by
  have hc := (barrett_nat n h).1
  simp only [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  have h1 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  have h2 : n * (5039 % 2 ^ 64) % 2 ^ 64 = n * 5039 := by
    rw [Nat.mod_eq_of_lt (a := 5039) (by norm_num), Nat.mod_eq_of_lt (by omega)]
  have h3 : n * 5039 / 2 ^ 24 * (3329 % 2 ^ 64) % 2 ^ 64 = n * 5039 / 2 ^ 24 * 3329 := by
    rw [Nat.mod_eq_of_lt (a := 3329) (by norm_num), Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2, h3]
  rw [show 2 ^ 64 - n * 5039 / 2 ^ 24 * 3329 + n = (n - n * 5039 / 2 ^ 24 * 3329) + 2 ^ 64 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- On `0 ≤ a < 7035·q` the `Int64` remainder is `a - ⌊5039a/2²⁴⌋·q`, lies in
    `[0, 2q)`, and is congruent to `a` modulo `q`. -/
theorem barrettRem_spec {a : ℤ} (h0 : 0 ≤ a) (h1 : a < 7035 * q) :
    0 ≤ barrettRem a ∧ barrettRem a < 2 * q ∧ barrettRem a % q = a % q := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  have hn : n < 7035 * 3329 := by unfold q at h1; omega
  have hb := barrett_nat n hn
  unfold barrettRem
  simp only
  rw [BitVec.ofInt_natCast, BitVec.toInt_eq_toNat_cond, barrettRem_toNat n hn]
  have hlt : 2 * (n - n * 5039 / 2 ^ 24 * 3329) < 2 ^ 64 := by omega
  simp only [hlt, ite_true]
  unfold q
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.cast_sub hb.1]
  push_cast
  omega

/-- `field_reduce a = a mod q` for every `0 ≤ a < 7035·q = 23 419 515`. -/
theorem fieldReduce_eq_emod {a : ℤ} (h0 : 0 ≤ a) (h1 : a < 7035 * q) :
    fieldReduce a = a % q := by
  obtain ⟨r0, r1, r2⟩ := barrettRem_spec h0 h1
  rw [fieldReduce_eq_barrettRem, fieldReduceOnce_eq_emod r0 r1, r2]

/-- The bound `7035·q` is tight: at `a = 7035·q` the Barrett remainder is `2q`
    and `field_reduce` returns the non-canonical value `q`. -/
theorem fieldReduce_first_failure : fieldReduce (7035 * q) = q := by
  unfold fieldReduce fieldReduceOnce signMask32 q; decide +kernel

/-- Every caller's argument is below `2q²`, which is inside the Barrett
    domain. -/
theorem two_q_sq_lt_barrett : 2 * q * q < 7035 * q := by unfold q; norm_num

theorem fieldReduce_canon {a : ℤ} (h0 : 0 ≤ a) (h1 : a < 7035 * q) : Canon (fieldReduce a) := by
  rw [fieldReduce_eq_emod h0 h1]; exact canon_emod a

theorem fieldReduce_cast {a : ℤ} (h0 : 0 ≤ a) (h1 : a < 7035 * q) :
    ((fieldReduce a : ℤ) : Zq) = (a : Zq) := by
  rw [fieldReduce_eq_emod h0 h1, cast_emod_q]

/-- `int` intermediates of `field_reduce` on `0 ≤ a < 7035·q`: the argument,
    the value returned by `Int64.to_int`, the intermediates of
    `field_reduce_once`, and the result. -/
theorem fieldReduce_portable {a : ℤ} (h0 : 0 ≤ a) (h1 : a < 7035 * q) :
    Portable a ∧ Portable (barrettRem a) ∧ Portable (barrettRem a - q) ∧
      Portable (signMask32 (barrettRem a - q)) ∧
      Portable (Int.land (signMask32 (barrettRem a - q)) q) ∧ Portable (fieldReduce a) := by
  obtain ⟨r0, r1, -⟩ := barrettRem_spec h0 h1
  obtain ⟨p1, p2, p3, p4, p5⟩ := fieldReduceOnce_portable r0 r1
  refine ⟨?_, p1, p2, p3, p4, p5⟩
  unfold Portable; unfold q at h1; omega

/-! ## `field_mul`, `field_mul_sub`, `field_add_mul` -/

/-- Model of `field_mul` (`lib/mlkem_engine.ml` line 119). -/
def fieldMul (a b : ℤ) : ℤ := fieldReduce (a * b)

/-- Model of `field_mul_sub` (`lib/mlkem_engine.ml` line 121). -/
def fieldMulSub (a b c : ℤ) : ℤ := fieldReduce (a * (b - c + q))

/-- Model of `field_add_mul` (`lib/mlkem_engine.ml` line 123). -/
def fieldAddMul (a b c d : ℤ) : ℤ := fieldReduce (a * b + c * d)

theorem mul_canon_bounds {a b : ℤ} (ha : Canon a) (hb : Canon b) :
    0 ≤ a * b ∧ a * b ≤ 3328 * 3328 := by
  unfold Canon q at ha hb
  constructor
  · exact mul_nonneg ha.1 hb.1
  · exact mul_le_mul (by omega) (by omega) hb.1 (by norm_num)

theorem fieldMul_arg {a b : ℤ} (ha : Canon a) (hb : Canon b) :
    0 ≤ a * b ∧ a * b < 7035 * q := by
  have := mul_canon_bounds ha hb
  unfold q; omega

theorem fieldMul_eq {a b : ℤ} (ha : Canon a) (hb : Canon b) : fieldMul a b = a * b % q :=
  fieldReduce_eq_emod (fieldMul_arg ha hb).1 (fieldMul_arg ha hb).2

theorem fieldMul_canon {a b : ℤ} (ha : Canon a) (hb : Canon b) : Canon (fieldMul a b) :=
  fieldReduce_canon (fieldMul_arg ha hb).1 (fieldMul_arg ha hb).2

theorem fieldMul_cast {a b : ℤ} (ha : Canon a) (hb : Canon b) :
    ((fieldMul a b : ℤ) : Zq) = (a : Zq) * (b : Zq) := by
  unfold fieldMul; rw [fieldReduce_cast (fieldMul_arg ha hb).1 (fieldMul_arg ha hb).2]; push_cast; rfl

theorem fieldMul_portable {a b : ℤ} (ha : Canon a) (hb : Canon b) :
    Portable (a * b) ∧ Portable (fieldMul a b) :=
  ⟨(fieldReduce_portable (fieldMul_arg ha hb).1 (fieldMul_arg ha hb).2).1,
    (fieldMul_canon ha hb).portable⟩

theorem fieldMulSub_arg {a b c : ℤ} (ha : Canon a) (hb : Canon b) (hc : Canon c) :
    0 ≤ b - c + q ∧ b - c + q < 2 * q ∧ 0 ≤ a * (b - c + q) ∧ a * (b - c + q) < 7035 * q := by
  unfold Canon q at *
  have h1 : 0 ≤ b - c + 3329 := by omega
  have h2 : b - c + 3329 ≤ 6657 := by omega
  refine ⟨h1, by omega, mul_nonneg ha.1 h1, ?_⟩
  have : a * (b - c + 3329) ≤ 3328 * 6657 := mul_le_mul (by omega) h2 h1 (by norm_num)
  omega

theorem fieldMulSub_eq {a b c : ℤ} (ha : Canon a) (hb : Canon b) (hc : Canon c) :
    fieldMulSub a b c = a * (b - c) % q := by
  obtain ⟨-, -, h0, h1⟩ := fieldMulSub_arg ha hb hc
  unfold fieldMulSub
  rw [fieldReduce_eq_emod h0 h1]
  rw [show a * (b - c + q) = a * (b - c) + a * q by ring, Int.add_mul_emod_self_right]

theorem fieldMulSub_canon {a b c : ℤ} (ha : Canon a) (hb : Canon b) (hc : Canon c) :
    Canon (fieldMulSub a b c) := by
  rw [fieldMulSub_eq ha hb hc]; exact canon_emod _

theorem fieldMulSub_cast {a b c : ℤ} (ha : Canon a) (hb : Canon b) (hc : Canon c) :
    ((fieldMulSub a b c : ℤ) : Zq) = (a : Zq) * ((b : Zq) - (c : Zq)) := by
  rw [fieldMulSub_eq ha hb hc, cast_emod_q]; push_cast; ring

theorem fieldMulSub_portable {a b c : ℤ} (ha : Canon a) (hb : Canon b) (hc : Canon c) :
    Portable (b - c) ∧ Portable (b - c + q) ∧ Portable (a * (b - c + q)) ∧
      Portable (fieldMulSub a b c) := by
  obtain ⟨h0, h1, h2, h3⟩ := fieldMulSub_arg ha hb hc
  have hp := (fieldReduce_portable h2 h3).1
  unfold Canon q at *
  refine ⟨?_, ?_, hp, (fieldMulSub_canon ha hb hc).portable⟩ <;> simp only [Portable] <;> omega

theorem fieldAddMul_arg {a b c d : ℤ} (ha : Canon a) (hb : Canon b) (hc : Canon c)
    (hd : Canon d) : 0 ≤ a * b + c * d ∧ a * b + c * d < 7035 * q := by
  have h1 := mul_canon_bounds ha hb
  have h2 := mul_canon_bounds hc hd
  unfold q; omega

theorem fieldAddMul_eq {a b c d : ℤ} (ha : Canon a) (hb : Canon b) (hc : Canon c)
    (hd : Canon d) : fieldAddMul a b c d = (a * b + c * d) % q :=
  fieldReduce_eq_emod (fieldAddMul_arg ha hb hc hd).1 (fieldAddMul_arg ha hb hc hd).2

theorem fieldAddMul_canon {a b c d : ℤ} (ha : Canon a) (hb : Canon b) (hc : Canon c)
    (hd : Canon d) : Canon (fieldAddMul a b c d) :=
  fieldReduce_canon (fieldAddMul_arg ha hb hc hd).1 (fieldAddMul_arg ha hb hc hd).2

theorem fieldAddMul_cast {a b c d : ℤ} (ha : Canon a) (hb : Canon b) (hc : Canon c)
    (hd : Canon d) :
    ((fieldAddMul a b c d : ℤ) : Zq) = (a : Zq) * (b : Zq) + (c : Zq) * (d : Zq) := by
  unfold fieldAddMul
  rw [fieldReduce_cast (fieldAddMul_arg ha hb hc hd).1 (fieldAddMul_arg ha hb hc hd).2]
  push_cast; ring

theorem fieldAddMul_portable {a b c d : ℤ} (ha : Canon a) (hb : Canon b) (hc : Canon c)
    (hd : Canon d) :
    Portable (a * b) ∧ Portable (c * d) ∧ Portable (a * b + c * d) ∧
      Portable (fieldAddMul a b c d) := by
  have h1 := mul_canon_bounds ha hb
  have h2 := mul_canon_bounds hc hd
  refine ⟨?_, ?_, ?_, (fieldAddMul_canon ha hb hc hd).portable⟩ <;> simp only [Portable] <;> omega

end OcamlPq.MLKEM
