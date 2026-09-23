import OcamlPq.MLKEM.Field

/-!
# ML-KEM compression and decompression

Models of `compress` and `decompress` (`lib/mlkem_engine.ml` lines 125–137)
and proofs that they compute FIPS 203 `Compress_d` / `Decompress_d`
(§4.2.1, equations (4.7) and (4.8)), where `⌈·⌋` rounds to the nearest
integer with ties rounded up (FIPS 203 §2.3; Mathlib's `round`).

* `compress_eq_spec`: for `0 ≤ x < q` and every `d ≤ 12` (the library uses
  `d ∈ {1, 4, 5, 10, 11}`).
* `decompress_eq_spec`, `decompress_lt_q`: for `1 ≤ d ≤ 12` and `y < 2^d`.
* `compress_decompress_error`: the FIPS 203 rounding-error bound
  `|(Decompress_d(Compress_d(x)) − x) mod± q| ≤ ⌈q/2^(d+1)⌋` for the five
  values of `d` used.
-/

namespace OcamlPq.MLKEM

/-! ## Specification -/

/-- FIPS 203 eq. (4.7): `Compress_d(x) = ⌈(2^d/q)·x⌋ mod 2^d`, where `x ∈ ℤ_q`
    is represented by `x.val ∈ [0, q)`. -/
def compressSpec (d : ℕ) (x : Zq) : ℤ := round ((2 : ℚ) ^ d / 3329 * x.val) % 2 ^ d

/-- FIPS 203 eq. (4.8): `Decompress_d(y) = ⌈(q/2^d)·y⌋` for `y ∈ ℤ_{2^d}`. -/
def decompressSpec (d : ℕ) (y : ℤ) : ℤ := round ((3329 : ℚ) / 2 ^ d * y)

/-- `m mod± q` for odd `q` (FIPS 203 §2.3): the representative of `m` in
    `[-(q-1)/2, (q-1)/2]`. -/
def modPm (m : ℤ) : ℤ := if m % 3329 ≤ 1664 then m % 3329 else m % 3329 - 3329

/-- `⌈x⌋ = ⌊x + 1/2⌋` of a rational `a/b` in integer arithmetic. -/
theorem round_div (a : ℤ) (b : ℕ) (hb : 0 < b) :
    round ((a : ℚ) / b) = (2 * a + b) / (2 * b : ℕ) := by
  rw [round_eq]
  have : (a : ℚ) / b + 1 / 2 = ((2 * a + b : ℤ) : ℚ) / ((2 * b : ℕ) : ℚ) := by
    have : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp; push_cast; ring
  rw [this, Rat.floor_intCast_div_natCast]

theorem compressSpec_eq_int (d : ℕ) (x : Zq) :
    compressSpec d x = (2 * (2 ^ d * x.val) + 3329) / 6658 % 2 ^ d := by
  unfold compressSpec
  have := round_div ((2 ^ d * x.val : ℕ) : ℤ) 3329 (by norm_num)
  push_cast at this
  rw [show (2 : ℚ) ^ d / 3329 * (x.val : ℚ) = (2 ^ d * (x.val : ℚ)) / 3329 by ring, this]

theorem decompressSpec_eq_int (d : ℕ) (y : ℤ) :
    decompressSpec d y = (2 * (3329 * y) + 2 ^ d) / (2 * 2 ^ d) := by
  unfold decompressSpec
  have := round_div (3329 * y) (2 ^ d) (by positivity)
  push_cast at this
  rw [show (3329 : ℚ) / 2 ^ d * (y : ℚ) = (3329 * (y : ℚ)) / 2 ^ d by ring, this]

/-! ## `compress` -/

/-- The helper `inc` of `compress` (`lib/mlkem_engine.ml` lines 130–131):
```
let inc threshold =
  to_int (logand (shift_right_logical (sub (of_int threshold) remainder) 63) 1L)
```
`Int64.to_int` is `BitVec.toInt` (the value is `0` or `1`). -/
def compressInc (remainder : BitVec 64) (threshold : ℤ) : ℤ :=
  (((BitVec.ofInt 64 threshold - remainder) >>> 63) &&& 1#64).toInt

/-- Model of `compress` (`lib/mlkem_engine.ml` lines 125–133):
```
let compress x d =
  let open Int64 in
  let dividend = shift_left (of_int x) d in
  let quotient = shift_right_logical (mul dividend 5039L) 24 in
  let remainder = sub dividend (mul quotient 3329L) in
  let inc threshold = ... in
  (to_int quotient + inc (q / 2) + inc (q + (q / 2))) land ((1 lsl d) - 1)
```
`Int64` values are `BitVec 64`; `shift_left` is `<<<`, `shift_right_logical`
is `>>>` (logical); `/` on `int` is `ocamlDiv`, `1 lsl d` is `(1 : ℤ) <<< d`
and `land` is `Int.land`. `to_int quotient` is `BitVec.toInt` (proved
`Portable` below). -/
def compress (x : ℤ) (d : ℕ) : ℤ :=
  let dividend : BitVec 64 := BitVec.ofInt 64 x <<< d
  let quotient := (dividend * 5039#64) >>> 24
  let remainder := dividend - quotient * 3329#64
  Int.land (quotient.toInt + compressInc remainder (ocamlDiv q 2)
      + compressInc remainder (q + ocamlDiv q 2)) (((1 : ℤ) <<< d) - 1)

theorem compressInc_eq (r t : ℕ) (hr : r < 2 ^ 62) (ht : t < 2 ^ 62) :
    compressInc (BitVec.ofNat 64 r) t = if t < r then 1 else 0 := by
  unfold compressInc
  have hV : ((BitVec.ofInt 64 (t : ℤ)) - BitVec.ofNat 64 r).toNat =
      if t < r then 2 ^ 64 - (r - t) else t - r := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := r) (by omega), Nat.mod_eq_of_lt (a := t) (by omega)]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [show 2 ^ 64 - r + t = (t - r) + 2 ^ 64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
  have hS : (((BitVec.ofInt 64 (t : ℤ)) - BitVec.ofNat 64 r) >>> 63 &&& 1#64).toNat =
      if t < r then 1 else 0 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, hV, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    split_ifs with h
    · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]; rfl
    · rw [Nat.div_eq_of_lt (by omega)]; rfl
  rw [BitVec.toInt_eq_toNat_cond, hS]
  split_ifs <;> simp_all

/-- The `Int64` values inside `compress x d` for `0 ≤ x < q`, `d ≤ 12`:
    with `D = x·2^d` and `c = ⌊5039·D/2²⁴⌋`, `dividend = D`,
    `quotient = c`, `remainder = D - c·q ∈ [0, 2q)`. -/
theorem compress_internals (n d : ℕ) (hn : n < 3329) (hd : d ≤ 12) :
    let dividend : BitVec 64 := BitVec.ofInt 64 (n : ℤ) <<< d
    let quotient := (dividend * 5039#64) >>> 24
    dividend.toNat = n * 2 ^ d ∧
      quotient.toNat = n * 2 ^ d * 5039 / 2 ^ 24 ∧
      (dividend - quotient * 3329#64) =
        BitVec.ofNat 64 (n * 2 ^ d - n * 2 ^ d * 5039 / 2 ^ 24 * 3329) ∧
      n * 2 ^ d * 5039 / 2 ^ 24 * 3329 ≤ n * 2 ^ d ∧
      n * 2 ^ d - n * 2 ^ d * 5039 / 2 ^ 24 * 3329 < 2 * 3329 := by
  intro dividend quotient
  have hP : 2 ^ d ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hd
  have hD : n * 2 ^ d < 3329 * 2 ^ 12 := by
    calc n * 2 ^ d < 3329 * 2 ^ d := Nat.mul_lt_mul_of_pos_right hn (by positivity)
      _ ≤ 3329 * 2 ^ 12 := Nat.mul_le_mul_left _ hP
  set D := n * 2 ^ d with hDdef
  have hb := barrett_nat D (by omega)
  have h1 : dividend.toNat = D := by
    simp only [dividend, BitVec.ofInt_natCast, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt (by omega)]
  have h2 : quotient.toNat = D * 5039 / 2 ^ 24 := by
    simp only [quotient, BitVec.toNat_ushiftRight, BitVec.toNat_mul, h1, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (a := 5039) (by norm_num), Nat.mod_eq_of_lt (by omega)]
  refine ⟨h1, h2, ?_, hb.1, hb.2⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_mul, h1, h2, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := 3329) (by norm_num), Nat.mod_eq_of_lt (a := D * 5039 / 2 ^ 24 * 3329)
    (by omega), Nat.mod_eq_of_lt (a := D - D * 5039 / 2 ^ 24 * 3329) (by omega),
    show 2 ^ 64 - D * 5039 / 2 ^ 24 * 3329 + D = (D - D * 5039 / 2 ^ 24 * 3329) + 2 ^ 64 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The sum `to_int quotient + inc (q/2) + inc (q + q/2)` before masking is
    `⌈(2^d/q)·x⌋` without the final `mod 2^d`. -/
theorem compress_sum (n d : ℕ) (hn : n < 3329) (hd : d ≤ 12) :
    let dividend : BitVec 64 := BitVec.ofInt 64 (n : ℤ) <<< d
    let quotient := (dividend * 5039#64) >>> 24
    let remainder := dividend - quotient * 3329#64
    quotient.toInt + compressInc remainder (ocamlDiv q 2)
        + compressInc remainder (q + ocamlDiv q 2) =
      (2 * (n * 2 ^ d) + 3329) / 6658 := by
  intro dividend quotient remainder
  obtain ⟨h1, h2, h3, h4, h5⟩ := compress_internals n d hn hd
  have hP : 2 ^ d ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hd
  have hD : n * 2 ^ d < 3329 * 2 ^ 12 := by
    calc n * 2 ^ d < 3329 * 2 ^ d := Nat.mul_lt_mul_of_pos_right hn (by positivity)
      _ ≤ 3329 * 2 ^ 12 := Nat.mul_le_mul_left _ hP
  set D := n * 2 ^ d
  set c := D * 5039 / 2 ^ 24
  have hq : quotient.toInt = (c : ℤ) := by
    rw [BitVec.toInt_eq_toNat_cond, h2]
    have : 2 * c < 2 ^ 64 := by omega
    simp only [this, ite_true]
  have hr : remainder = BitVec.ofNat 64 (D - c * 3329) := h3
  have e1 : ocamlDiv q 2 = ((1664 : ℕ) : ℤ) := by unfold ocamlDiv q; decide
  have e2 : q + ocamlDiv q 2 = ((4993 : ℕ) : ℤ) := by unfold ocamlDiv q; decide
  rw [hq, hr, e2, e1, compressInc_eq _ _ (by omega) (by norm_num),
    compressInc_eq _ _ (by omega) (by norm_num)]
  have key : (2 * D + 3329) / 6658 = c + (if 1664 < D - c * 3329 then 1 else 0) +
      (if 4993 < D - c * 3329 then 1 else 0) := by
    split_ifs <;> omega
  have : ((2 * ((n : ℤ) * 2 ^ d) + 3329) / 6658) = (((2 * D + 3329) / 6658 : ℕ) : ℤ) := by
    simp only [D]; push_cast; rfl
  rw [this, key]
  split_ifs <;> push_cast <;> ring

theorem int_land_two_pow_sub_one (s : ℤ) (hs : 0 ≤ s) (d : ℕ) :
    Int.land s (((1 : ℤ) <<< d) - 1) = s % 2 ^ d := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hs
  have h1 : ((1 : ℤ) <<< d) - 1 = ((2 ^ d - 1 : ℕ) : ℤ) := by
    rw [Int.shiftLeft_eq, Nat.cast_sub (Nat.one_le_two_pow)]; push_cast; ring
  rw [h1]
  change ((m &&& (2 ^ d - 1) : ℕ) : ℤ) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]; push_cast; rfl

/-- `compress x d` equals FIPS 203 `Compress_d(x)` for canonical `x` and every
    `d ≤ 12`. -/
theorem compress_eq_spec {x : ℤ} {d : ℕ} (hx : Canon x) (hd : d ≤ 12) :
    compress x d = compressSpec d (x : Zq) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hn : n < 3329 := by have := hx.2; unfold q at this; omega
  have hval : ((n : ℤ) : Zq).val = n := by
    rw [Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hn]
  rw [compressSpec_eq_int, hval]
  unfold compress
  simp only
  rw [compress_sum n d hn hd, int_land_two_pow_sub_one _ (by positivity)]
  ring_nf

theorem compress_range {x : ℤ} {d : ℕ} (hx : Canon x) (hd : d ≤ 12) :
    0 ≤ compress x d ∧ compress x d < 2 ^ d := by
  rw [compress_eq_spec hx hd]; unfold compressSpec
  exact ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩

/-- `int` intermediates of `compress x d` (`0 ≤ x < q`, `d ≤ 12`): `x`, `d`,
    `to_int quotient`, both `inc` values, the sum, `1 lsl d`, `(1 lsl d) - 1`
    and the result. The constants `q / 2 = 1664` and `q + q / 2 = 4993` are
    immediate. -/
theorem compress_portable {x : ℤ} {d : ℕ} (hx : Canon x) (hd : d ≤ 12) :
    let dividend : BitVec 64 := BitVec.ofInt 64 x <<< d
    let quotient := (dividend * 5039#64) >>> 24
    let remainder := dividend - quotient * 3329#64
    Portable x ∧ Portable (d : ℤ) ∧ Portable quotient.toInt ∧
      Portable (compressInc remainder (ocamlDiv q 2)) ∧
      Portable (compressInc remainder (q + ocamlDiv q 2)) ∧
      Portable (quotient.toInt + compressInc remainder (ocamlDiv q 2)
        + compressInc remainder (q + ocamlDiv q 2)) ∧
      Portable ((1 : ℤ) <<< d) ∧ Portable (((1 : ℤ) <<< d) - 1) ∧
      Portable (compress x d) := by
  intro dividend quotient remainder
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hn : n < 3329 := by have := hx.2; unfold q at this; omega
  obtain ⟨h1, h2, h3, h4, h5⟩ := compress_internals n d hn hd
  have hsum := compress_sum n d hn hd
  have hP : 2 ^ d ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hd
  have hD : n * 2 ^ d < 3329 * 2 ^ 12 := by
    calc n * 2 ^ d < 3329 * 2 ^ d := Nat.mul_lt_mul_of_pos_right hn (by positivity)
      _ ≤ 3329 * 2 ^ 12 := Nat.mul_le_mul_left _ hP
  have hq : quotient.toInt = ((n * 2 ^ d * 5039 / 2 ^ 24 : ℕ) : ℤ) := by
    rw [BitVec.toInt_eq_toNat_cond, h2]
    have : 2 * (n * 2 ^ d * 5039 / 2 ^ 24) < 2 ^ 64 := by omega
    simp only [this, ite_true]
  have hr : remainder = BitVec.ofNat 64 (n * 2 ^ d - n * 2 ^ d * 5039 / 2 ^ 24 * 3329) := h3
  have e1 : ocamlDiv q 2 = ((1664 : ℕ) : ℤ) := by unfold ocamlDiv q; decide
  have e2 : q + ocamlDiv q 2 = ((4993 : ℕ) : ℤ) := by unfold ocamlDiv q; decide
  have i1 : compressInc remainder (ocamlDiv q 2) = 0 ∨ compressInc remainder (ocamlDiv q 2) = 1 := by
    rw [hr, e1, compressInc_eq _ _ (by omega) (by norm_num)]; split_ifs <;> simp
  have i2 : compressInc remainder (q + ocamlDiv q 2) = 0 ∨
      compressInc remainder (q + ocamlDiv q 2) = 1 := by
    rw [hr, e2, compressInc_eq _ _ (by omega) (by norm_num)]; split_ifs <;> simp
  have hc := compress_range hx hd
  have hshift : (1 : ℤ) <<< d = ((2 ^ d : ℕ) : ℤ) := by rw [Int.shiftLeft_eq]; push_cast; ring
  have hsum' : quotient.toInt + compressInc remainder (ocamlDiv q 2)
      + compressInc remainder (q + ocamlDiv q 2) = (2 * ((n : ℤ) * 2 ^ d) + 3329) / 6658 := by
    have := hsum; push_cast at this ⊢; exact this
  have hP' : ((2 ^ d : ℕ) : ℤ) ≤ 4096 := by exact_mod_cast hP
  have hP0 : (0 : ℤ) < ((2 ^ d : ℕ) : ℤ) := by positivity
  have hD' : ((n : ℤ) * 2 ^ d) < 3329 * 4096 := by exact_mod_cast hD
  refine ⟨hx.portable, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Portable; push_cast; omega
  · rw [hq]; unfold Portable; push_cast; omega
  · unfold Portable; rcases i1 with h | h <;> rw [h] <;> norm_num
  · unfold Portable; rcases i2 with h | h <;> rw [h] <;> norm_num
  · rw [hsum']; unfold Portable; omega
  · rw [hshift]; unfold Portable; omega
  · rw [hshift]; unfold Portable; omega
  · have : (2 : ℤ) ^ d ≤ 4096 := by exact_mod_cast hP
    unfold Portable; omega

/-! ## `decompress` -/

/-- Model of `decompress` (`lib/mlkem_engine.ml` lines 135–137):
```
let decompress y d =
  let dividend = y * q in
  (dividend lsr d) + ((dividend lsr (d - 1)) land 1)
```
Modelled over `ℕ`: the only caller passes `y = Int64.to_int acc land mask ≥ 0`
and `d ≥ 1`, so `dividend ≥ 0` (where `lsr` is `Nat.shiftRight`) and `d - 1`
does not underflow. -/
def decompress (y d : ℕ) : ℕ :=
  let dividend := y * 3329
  (dividend >>> d) + ((dividend >>> (d - 1)) &&& 1)

theorem half_round (A P : ℕ) (hP : 0 < P) : A / (2 * P) + (A / P) % 2 = (A + P) / (2 * P) := by
  rw [Nat.mul_comm 2 P, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    Nat.add_div_right _ hP]
  omega

/-- `decompress y d = ⌈(q/2^d)·y⌋` (FIPS 203 `Decompress_d`) for `d ≥ 1`. -/
theorem decompress_eq_spec (y d : ℕ) (hd : 1 ≤ d) :
    (decompress y d : ℤ) = decompressSpec d y := by
  rw [decompressSpec_eq_int]
  unfold decompress
  simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [show e + 1 - 1 = e by omega, pow_succ, show 2 ^ e * 2 = 2 * 2 ^ e by ring,
    half_round _ _ (by positivity)]
  push_cast
  rw [show 2 * (3329 * (y : ℤ)) + 2 ^ (e + 1) = 2 * (y * 3329 + 2 ^ e) by ring,
    show (2 : ℤ) * 2 ^ (e + 1) = 2 * (2 * 2 ^ e) by ring,
    Int.mul_ediv_mul_of_pos _ _ (by norm_num)]

/-- For `y < 2^d` and `1 ≤ d ≤ 12`, `decompress y d < q`: the output is a
    canonical element of `ℤ_q`. -/
theorem decompress_lt_q (y d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ 12) (hy : y < 2 ^ d) :
    decompress y d < 3329 := by
  have hP : 2 ^ d ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hd
  have := decompress_eq_spec y d hd1
  rw [decompressSpec_eq_int] at this
  have h2 : (2 * (3329 * (y : ℤ)) + 2 ^ d) / (2 * 2 ^ d) < 3329 := by
    rw [Int.ediv_lt_iff_lt_mul (by positivity)]
    have : (y : ℤ) + 1 ≤ 2 ^ d := by exact_mod_cast hy
    have : (2 : ℤ) ^ d ≤ 4096 := by exact_mod_cast hP
    nlinarith
  omega

theorem decompress_canon (y d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ 12) (hy : y < 2 ^ d) :
    Canon (decompress y d : ℤ) := by
  have := decompress_lt_q y d hd1 hd hy
  unfold Canon q; omega

/-- `int` intermediates of `decompress y d` (`y < 2^d`, `1 ≤ d ≤ 12`). -/
theorem decompress_portable (y d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ 12) (hy : y < 2 ^ d) :
    Portable (y : ℤ) ∧ Portable ((y * 3329 : ℕ) : ℤ) ∧ Portable (((y * 3329) >>> d : ℕ) : ℤ) ∧
      Portable ((((y * 3329) >>> (d - 1)) &&& 1 : ℕ) : ℤ) ∧ Portable (decompress y d : ℤ) := by
  have hP : 2 ^ d ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hd
  have hy' : y < 4096 := by omega
  have h1 : (y * 3329) >>> d ≤ y * 3329 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  have h2 : ((y * 3329) >>> (d - 1)) &&& 1 ≤ 1 := by rw [Nat.and_one_is_mod]; omega
  have h3 := decompress_lt_q y d hd1 hd hy
  refine ⟨Portable.of_nat_lt (by omega), Portable.of_nat_lt (by omega),
    Portable.of_nat_lt (by omega), Portable.of_nat_lt (by omega), Portable.of_nat_lt (by omega)⟩

/-! ## Rounding error of `Decompress ∘ Compress` -/

set_option maxRecDepth 100000 in
/-- The error bound of `compress_decompress_error` in integer form, checked
    for all `x < q` by kernel evaluation (`decide +kernel`, no
    `native_decide`). -/
theorem compress_decompress_error_int (d : ℕ) (hd : d ∈ ({1, 4, 5, 10, 11} : Finset ℕ)) :
    ∀ n : ℕ, n < 3329 →
      |modPm ((2 * (3329 * ((2 * (2 ^ d * (n : ℤ)) + 3329) / 6658 % 2 ^ d)) + 2 ^ d) /
          (2 * 2 ^ d) - n)| ≤ (2 * 3329 + 2 ^ (d + 1)) / (2 * 2 ^ (d + 1)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- FIPS 203 §4.2.1: `|(Decompress_d(Compress_d(x)) − x) mod± q| ≤ ⌈q/2^(d+1)⌋`,
    for each `d` used by ML-KEM-512/768/1024 and every `x ∈ ℤ_q`. -/
theorem compress_decompress_error (d : ℕ) (hd : d ∈ ({1, 4, 5, 10, 11} : Finset ℕ)) (x : Zq) :
    |modPm (decompressSpec d (compressSpec d x) - (x.val : ℤ))| ≤
      round ((3329 : ℚ) / 2 ^ (d + 1)) := by
  have hB := round_div 3329 (2 ^ (d + 1)) (by positivity)
  push_cast at hB
  rw [hB, decompressSpec_eq_int, compressSpec_eq_int]
  have := compress_decompress_error_int d hd x.val (ZMod.val_lt x)
  push_cast at this ⊢
  exact this

set_option maxRecDepth 100000 in
/-- Integer form of `compress_decompress_roundtrip`, by kernel evaluation. -/
theorem compress_decompress_roundtrip_int (d : ℕ) (hd : d ∈ ({1, 4, 5, 10, 11} : Finset ℕ)) :
    ∀ y : ℕ, y < 2 ^ d →
      (2 * (2 ^ d * ((2 * (3329 * (y : ℤ)) + 2 ^ d) / (2 * 2 ^ d) % 3329)) + 3329) / 6658
        % 2 ^ d = y := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- `Compress_d(Decompress_d(y)) = y` for every `y ∈ ℤ_{2^d}` and each `d`
    used by ML-KEM (FIPS 203 §4.2.1). -/
theorem compress_decompress_roundtrip (d : ℕ) (hd : d ∈ ({1, 4, 5, 10, 11} : Finset ℕ))
    (y : ℕ) (hy : y < 2 ^ d) :
    compressSpec d ((decompressSpec d y : ℤ) : Zq) = y := by
  rw [compressSpec_eq_int, ZMod.val_intCast, decompressSpec_eq_int]
  exact compress_decompress_roundtrip_int d hd y hy

end OcamlPq.MLKEM
