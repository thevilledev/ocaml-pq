import OcamlPq.Common.Int

/-!
# ML-DSA modular arithmetic

Models of the scalar helpers of `mldsa/mldsa_engine.ml` (lines 171–194):
`norm`, `center`, `add_mod`, `sub_mod`, `mul_mod` and `pow_mod`, with
proofs that they compute the intended operations of `ℤ_q` (FIPS 204 §2.3,
`q = 8380417`), that their outputs are canonical, and that every `int`
intermediate is `Portable` on the inputs the code passes.
-/

namespace OcamlPq.MLDSA

/-- The ML-DSA modulus `q = 2^23 - 2^13 + 1` (FIPS 204, §4 Table 1;
    `let q = 8_380_417`, mldsa/mldsa_engine.ml:111). -/
def q : ℤ := 8380417

theorem q_eq : q = 8380417 := rfl

theorem q_pos : 0 < q := by decide

/-- `q` is prime (so `ZMod 8380417` is a field). -/
theorem q_prime : Nat.Prime 8380417 := by norm_num

instance : Fact (Nat.Prime 8380417) := ⟨q_prime⟩

/-- OCaml's `mod` by a positive divisor, expressed through Lean's `%`. -/
theorem ocamlMod_pos_eq (a b : ℤ) (hb : 0 < b) :
    ocamlMod a b = if 0 ≤ a ∨ a % b = 0 then a % b else a % b - b := by
  unfold ocamlMod
  rw [Int.tmod_eq_emod]
  have hd : (b ∣ a) ↔ a % b = 0 := Int.dvd_iff_emod_eq_zero
  have hn : ((b.natAbs : ℕ) : ℤ) = b := Int.natAbs_of_nonneg hb.le
  by_cases h1 : 0 ≤ a
  · simp [h1]
  · by_cases h2 : a % b = 0
    · simp [h2, hd.mpr h2]
    · simp [h1, h2, hd, hn]

/-- OCaml's `/` by a positive divisor of a non-negative dividend. -/
theorem ocamlDiv_nonneg_eq (a b : ℤ) (ha : 0 ≤ a) : ocamlDiv a b = a / b :=
  ocamlDiv_of_nonneg ha

/-! ## `norm` and `center` -/

/-- Model of `norm` (mldsa/mldsa_engine.ml:171–173):
    `let value = value mod q in if value < 0 then value + q else value`. -/
def norm (value : ℤ) : ℤ :=
  let value := ocamlMod value q
  if value < 0 then value + q else value

/-- Model of `center` (mldsa/mldsa_engine.ml:175–177):
    `let value = norm value in if value > (q - 1) / 2 then value - q else value`. -/
def center (value : ℤ) : ℤ :=
  let value := norm value
  if value > ocamlDiv (q - 1) 2 then value - q else value

/-- `norm` is the canonical representative `value mod q` for every integer
    input (in particular every OCaml `int` on every platform). -/
theorem norm_eq (value : ℤ) : norm value = value % q := by
  unfold norm
  rw [ocamlMod_pos_eq _ _ q_pos]
  simp only [q] at *
  split_ifs <;> omega

theorem norm_nonneg (value : ℤ) : 0 ≤ norm value := by
  rw [norm_eq]; exact Int.emod_nonneg _ (by decide)

theorem norm_lt (value : ℤ) : norm value < q := by
  rw [norm_eq]; exact Int.emod_lt_of_pos _ q_pos

theorem norm_of_canonical {value : ℤ} (h0 : 0 ≤ value) (h1 : value < q) :
    norm value = value := by
  rw [norm_eq]; exact Int.emod_eq_of_lt h0 h1

/-- Reduction modulo `q` does not change the image in `ZMod q`. -/
theorem cast_emod_q (a : ℤ) : ((a % q : ℤ) : ZMod 8380417) = (a : ZMod 8380417) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]; push_cast; simp only [q]; omega

/-- `norm` as a map to `ZMod q`: it is the identity on residues. -/
theorem norm_cast (value : ℤ) : ((norm value : ℤ) : ZMod 8380417) = (value : ZMod 8380417) := by
  rw [norm_eq]; exact cast_emod_q value

/-- The intermediates of `norm` are portable when the input is: the
    truncated remainder lies in `(-q, q)` and the corrected value in `[0, q)`. -/
theorem norm_portable (value : ℤ) :
    Portable (ocamlMod value q) ∧ Portable (ocamlMod value q + q) ∧ Portable (norm value) := by
  rw [ocamlMod_pos_eq _ _ q_pos]
  have h1 := norm_nonneg value
  have h2 := norm_lt value
  simp only [q, Portable] at *
  refine ⟨?_, ?_, ?_⟩ <;> (try split_ifs) <;> omega

/-- `center` returns the representative of `value mod q` in
    `[-(q-1)/2, (q-1)/2]`, i.e. `value mod± q` (FIPS 204 §2.3). -/
theorem center_eq (value : ℤ) :
    center value = if value % q > 4190208 then value % q - q else value % q := by
  unfold center
  rw [norm_eq]
  simp only [ocamlDiv, q]
  norm_num

theorem center_bounds (value : ℤ) : -4190208 ≤ center value ∧ center value ≤ 4190208 := by
  rw [center_eq]; simp only [q]; split_ifs <;> omega

theorem center_emod (value : ℤ) : center value % q = value % q := by
  rw [center_eq]; simp only [q]; split_ifs <;> omega

theorem center_cast (value : ℤ) :
    ((center value : ℤ) : ZMod 8380417) = (value : ZMod 8380417) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have h := center_emod value
  push_cast; simp only [q] at *; omega

/-- `center` is the identity on `[-(q-1)/2, (q-1)/2]`. -/
theorem center_of_small {value : ℤ} (h0 : -4190208 ≤ value) (h1 : value ≤ 4190208) :
    center value = value := by
  rw [center_eq]; simp only [q]; split_ifs <;> omega

theorem center_center (value : ℤ) : center (center value) = center value := by
  obtain ⟨h0, h1⟩ := center_bounds value
  exact center_of_small h0 h1

/-- Characterisation of `center` used by `omega`-based proofs: the result is
    the unique representative of `value` modulo `q` in `[-(q-1)/2, (q-1)/2]`. -/
theorem center_spec (value : ℤ) :
    -4190208 ≤ center value ∧ center value ≤ 4190208 ∧ (value - center value) % q = 0 := by
  refine ⟨(center_bounds value).1, (center_bounds value).2, ?_⟩
  rw [center_eq]; simp only [q]; split_ifs <;> omega

theorem center_portable (value : ℤ) :
    Portable (norm value) ∧ Portable (norm value - q) ∧ Portable (center value) := by
  have h1 := norm_nonneg value
  have h2 := norm_lt value
  have h3 := center_bounds value
  simp only [q, Portable] at *
  omega

/-! ## `add_mod` and `sub_mod` -/

/-- Model of `add_mod` (mldsa/mldsa_engine.ml:179). -/
def addMod (left right : ℤ) : ℤ := norm (left + right)

/-- Model of `sub_mod` (mldsa/mldsa_engine.ml:180). -/
def subMod (left right : ℤ) : ℤ := norm (left - right)

theorem addMod_eq (a b : ℤ) : addMod a b = (a + b) % q := norm_eq _
theorem subMod_eq (a b : ℤ) : subMod a b = (a - b) % q := norm_eq _

theorem addMod_cast (a b : ℤ) :
    ((addMod a b : ℤ) : ZMod 8380417) = (a : ZMod 8380417) + b := by
  rw [addMod, norm_cast]; push_cast; ring

theorem subMod_cast (a b : ℤ) :
    ((subMod a b : ℤ) : ZMod 8380417) = (a : ZMod 8380417) - b := by
  rw [subMod, norm_cast]; push_cast; ring

/-- The sum and difference computed by `add_mod`/`sub_mod` are portable
    whenever both operands are below `2^29` in absolute value (every caller
    passes canonical values in `[0, q)` or small signed values). -/
theorem addMod_portable {a b : ℤ} (ha : |a| < 2 ^ 29) (hb : |b| < 2 ^ 29) :
    Portable (a + b) ∧ Portable (a - b) := by
  rw [abs_lt] at ha hb
  constructor <;> constructor <;> norm_num at * <;> omega

/-! ## `mul_mod` (via `Int64`) -/

/-- OCaml's `Int64.of_int` on a native `int` (sign extension, exact). -/
def int64OfInt (x : ℤ) : BitVec 64 := BitVec.ofInt 64 x

/-- Model of `mul_mod` (mldsa/mldsa_engine.ml:182–183):
    `Int64.(to_int (rem (mul (of_int (norm left)) (of_int (norm right))) (of_int q)))`.
    `Int64.mul` wraps modulo `2^64` (`BitVec` multiplication), `Int64.rem`
    truncates (`BitVec.srem`), and `Int64.to_int` returns the signed value
    (`BitVec.toInt`); `mulMod_int64_exact` shows the latter is exact on
    every platform. -/
def mulModInt64 (left right : ℤ) : BitVec 64 :=
  BitVec.srem (int64OfInt (norm left) * int64OfInt (norm right)) (int64OfInt q)

def mulMod (left right : ℤ) : ℤ := (mulModInt64 left right).toInt

theorem mulMod_eq (a b : ℤ) : mulMod a b = (a * b) % q := by
  have ha0 := norm_nonneg a
  have ha1 := norm_lt a
  have hb0 := norm_nonneg b
  have hb1 := norm_lt b
  have hprod0 : 0 ≤ norm a * norm b := mul_nonneg ha0 hb0
  have hprod1 : norm a * norm b < 2 ^ 63 := by
    have : norm a * norm b ≤ (q - 1) * (q - 1) :=
      mul_le_mul (by omega) (by omega) hb0 (by simp only [q]; omega)
    simp only [q] at this; omega
  unfold mulMod mulModInt64 int64OfInt
  rw [BitVec.toInt_srem, ← BitVec.ofInt_mul, BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)]
  rw [Int.bmod_eq_of_le (by simp only [q]; norm_num) (by simp only [q]; norm_num)]
  rw [Int.tmod_eq_emod_of_nonneg hprod0, norm_eq, norm_eq, ← Int.mul_emod]

theorem mulMod_cast (a b : ℤ) :
    ((mulMod a b : ℤ) : ZMod 8380417) = (a : ZMod 8380417) * b := by
  rw [mulMod_eq, cast_emod_q]; push_cast; ring

theorem mulMod_nonneg (a b : ℤ) : 0 ≤ mulMod a b := by
  rw [mulMod_eq]; exact Int.emod_nonneg _ (by decide)

theorem mulMod_lt (a b : ℤ) : mulMod a b < q := by
  rw [mulMod_eq]; exact Int.emod_lt_of_pos _ q_pos

/-- No `Int64` operation in `mul_mod` overflows: the product of the two
    canonical operands is below `2^63`, and the `int` returned by
    `Int64.to_int` is portable, so the conversion is exact on every
    platform (`wrap p.intBits` is the identity). -/
theorem mulMod_int64_exact (a b : ℤ) :
    (int64OfInt (norm a) * int64OfInt (norm b)).toInt = norm a * norm b ∧
    0 ≤ norm a * norm b ∧ norm a * norm b < 2 ^ 63 ∧
    Portable (mulMod a b) ∧ ∀ p : Platform, wrap p.intBits (mulMod a b) = mulMod a b := by
  have ha0 := norm_nonneg a
  have ha1 := norm_lt a
  have hb0 := norm_nonneg b
  have hb1 := norm_lt b
  have hprod0 : 0 ≤ norm a * norm b := mul_nonneg ha0 hb0
  have hprod1 : norm a * norm b < 2 ^ 63 := by
    have : norm a * norm b ≤ (q - 1) * (q - 1) :=
      mul_le_mul (by omega) (by omega) hb0 (by simp only [q]; omega)
    simp only [q] at this; omega
  have hport : Portable (mulMod a b) := by
    have := mulMod_nonneg a b
    have := mulMod_lt a b
    simp only [q, Portable] at *; omega
  refine ⟨?_, hprod0, hprod1, hport, fun p => hport.wrap_platform p⟩
  unfold int64OfInt
  rw [← BitVec.ofInt_mul, BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)

/-! ## `pow_mod` -/

/-- Model of the inner `loop` of `pow_mod` (mldsa/mldsa_engine.ml:185–194).
    The exponent is a non-negative `int`; `exponent land 1` and
    `exponent lsr 1` are `&&& 1` and `>>> 1` on `ℕ`. -/
def powModLoop (accumulator base : ℤ) (exponent : ℕ) : ℤ :=
  if exponent = 0 then accumulator
  else
    let accumulator := if exponent &&& 1 = 1 then mulMod accumulator base else accumulator
    powModLoop accumulator (mulMod base base) (exponent >>> 1)
termination_by exponent
decreasing_by
  rw [Nat.shiftRight_eq_div_pow]; omega

/-- Model of `pow_mod` (mldsa/mldsa_engine.ml:185–194). -/
def powMod (base : ℤ) (exponent : ℕ) : ℤ := powModLoop 1 base exponent

theorem powModLoop_eq (exponent : ℕ) :
    ∀ (accumulator base : ℤ), 0 ≤ accumulator → accumulator < q →
      powModLoop accumulator base exponent = (accumulator * base ^ exponent) % q := by
  induction exponent using Nat.strong_induction_on with
  | _ e ih =>
    intro acc base h0 h1
    rw [powModLoop]
    by_cases he : e = 0
    · subst he; simp [Int.emod_eq_of_lt h0 h1]
    · simp only [he, ite_false]
      have hlt : e >>> 1 < e := by rw [Nat.shiftRight_eq_div_pow]; omega
      have hand : e &&& 1 = e % 2 := Nat.and_one_is_mod e
      have hshr : e >>> 1 = e / 2 := by simp [Nat.shiftRight_eq_div_pow]
      have hsplit : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
      have hsq : ∀ k : ℕ, Int.ModEq q ((base * base % q) ^ k) (base ^ (2 * k)) := by
        intro k
        rw [pow_mul, sq]
        exact (Int.mod_modEq (base * base) q).pow k
      split_ifs with hodd
      · rw [ih _ hlt _ _ (mulMod_nonneg _ _) (mulMod_lt _ _), mulMod_eq, mulMod_eq, hshr]
        rw [hand] at hodd
        have := ((hsq (e / 2)).mul_left (acc * base % q)).trans
          (((Int.mod_modEq (acc * base) q).mul_right (base ^ (2 * (e / 2)))))
        rw [Int.ModEq] at this
        rw [this]
        conv_rhs => rw [hsplit, hodd]
        congr 1; ring
      · rw [ih _ hlt _ _ h0 h1, mulMod_eq, hshr]
        rw [hand] at hodd
        have hodd' : e % 2 = 0 := by omega
        have := (hsq (e / 2)).mul_left acc
        rw [Int.ModEq] at this
        rw [this]
        conv_rhs => rw [hsplit, hodd', add_zero]

theorem powMod_eq (base : ℤ) (exponent : ℕ) : powMod base exponent = base ^ exponent % q := by
  rw [powMod, powModLoop_eq _ _ _ (by decide) (by decide), one_mul]

theorem powMod_cast (base : ℤ) (exponent : ℕ) :
    ((powMod base exponent : ℤ) : ZMod 8380417) = (base : ZMod 8380417) ^ exponent := by
  rw [powMod_eq, cast_emod_q]; push_cast; ring

/-- The accumulator and base of `pow_mod`'s loop stay canonical (hence
    portable) at every step, whatever the (canonical) starting values. -/
theorem powModLoop_step_portable (accumulator base : ℤ) :
    Portable (mulMod accumulator base) ∧ Portable (mulMod base base) :=
  ⟨(mulMod_int64_exact _ _).2.2.2.1, (mulMod_int64_exact _ _).2.2.2.1⟩

end OcamlPq.MLDSA
