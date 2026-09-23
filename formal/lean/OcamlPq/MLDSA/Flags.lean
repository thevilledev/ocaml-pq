import OcamlPq.MLDSA.Sign

/-!
# Norm checks and small arithmetic in signing and verification

* `norm_violation_flag` / `vector_norm_violation_flag`
  (mldsa/mldsa_engine.ml:456–468) compute `[‖v‖∞ ≥ bound]`;
* `z = y + cs1` (mldsa/mldsa_engine.ml:760–765) is portable and is its own
  centered representative;
* `value lsl d` on `t1` coefficients (mldsa/mldsa_engine.ml:853–857) stays
  below `q`.
-/

namespace OcamlPq.MLDSA

/-! ## `norm_violation_flag` -/

/-- Model of `norm_violation_flag` (mldsa/mldsa_engine.ml:456–462). The
    OCaml `for` loop over the array is a left fold over the coefficient
    list; `lor` on the 0/1 flags is `|||` on `ℕ`. OCaml's `abs` is `|·|`
    here because `center` outputs are portable (`center_portable`), so the
    `abs min_int` corner case cannot arise. -/
def normViolationFlag (polynomial : List ℤ) (bound : ℤ) : ℕ :=
  polynomial.foldl
    (fun violation value =>
      let exceeds := if |center value| ≥ bound then 1 else 0
      violation ||| exceeds)
    0

/-- Model of `vector_norm_violation_flag` (mldsa/mldsa_engine.ml:464–468). -/
def vectorNormViolationFlag (vector : List (List ℤ)) (bound : ℤ) : ℕ :=
  vector.foldl (fun violation polynomial => violation ||| normViolationFlag polynomial bound) 0

/-- `‖v‖∞ ≥ b` for a vector of polynomials (FIPS 204 §2.3): some
    coefficient has `|w mod± q| ≥ b`. -/
def infNormGe (vector : List (List ℤ)) (bound : ℤ) : Prop :=
  ∃ p ∈ vector, ∃ x ∈ p, coeffNorm x ≥ bound

instance (vector : List (List ℤ)) (bound : ℤ) : Decidable (infNormGe vector bound) := by
  unfold infNormGe; infer_instance

theorem flag_or (a : ℕ) (P Q : Prop) [Decidable P] [Decidable Q] :
    a ||| (if P then 1 else 0) ||| (if Q then 1 else 0) =
      a ||| (if P ∨ Q then 1 else 0) := by
  rw [Nat.or_assoc]
  congr 1
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem normViolationFlag_foldl (p : List ℤ) (bound : ℤ) (acc : ℕ) :
    p.foldl (fun violation value =>
        let exceeds := if |center value| ≥ bound then 1 else 0
        violation ||| exceeds) acc =
      acc ||| (if ∃ x ∈ p, |center x| ≥ bound then 1 else 0) := by
  induction p generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, flag_or]
    congr 2
    simp

/-- `norm_violation_flag p b = 1` iff some coefficient has
    `|center p_i| ≥ b`, and `0` otherwise. -/
theorem normViolationFlag_eq (p : List ℤ) (bound : ℤ) :
    normViolationFlag p bound = if ∃ x ∈ p, |center x| ≥ bound then 1 else 0 := by
  rw [normViolationFlag, normViolationFlag_foldl]; simp

theorem vectorNormViolationFlag_foldl (v : List (List ℤ)) (bound : ℤ) (acc : ℕ) :
    v.foldl (fun violation polynomial => violation ||| normViolationFlag polynomial bound) acc =
      acc ||| (if ∃ p ∈ v, ∃ x ∈ p, |center x| ≥ bound then 1 else 0) := by
  induction v generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, normViolationFlag_eq, flag_or]
    congr 2
    simp

/-- `vector_norm_violation_flag v b = 1` iff `‖v‖∞ ≥ b` (FIPS 204). -/
theorem vectorNormViolationFlag_eq (v : List (List ℤ)) (bound : ℤ) :
    vectorNormViolationFlag v bound = if infNormGe v bound then 1 else 0 := by
  rw [vectorNormViolationFlag, vectorNormViolationFlag_foldl]
  simp only [infNormGe, coeffNorm_eq]
  simp

/-- The flags are `0`/`1`, so `lor`-accumulation never grows beyond `1`
    (portable). -/
theorem vectorNormViolationFlag_le_one (v : List (List ℤ)) (bound : ℤ) :
    vectorNormViolationFlag v bound ≤ 1 := by
  rw [vectorNormViolationFlag_eq]; split_ifs <;> simp

/-! ## `z = y + cs1` -/

/-- The masking coefficient `y ∈ (-γ1, γ1]` (the range `unpack_z` produces)
    plus `cs1 = center (…)` is portable for every `cs1` the code can
    produce; if moreover `|cs1| ≤ β` (true for honest keys, `‖c·s1‖∞ ≤ τη`)
    then `center z = z`, so the code's `abs (center z)` test is `|z|`. -/
theorem z_portable_center (γ1 β y cs1 : ℤ) (hγ1 : γ1 = 2 ^ 17 ∨ γ1 = 2 ^ 19)
    (hy0 : -γ1 < y) (hy1 : y ≤ γ1) (hβ : 0 ≤ β ∧ β ≤ 196) :
    Portable (y + center cs1) ∧
    (|cs1| ≤ β → center (y + cs1) = y + cs1 ∧ Portable (y + cs1)) := by
  have hc := center_bounds cs1
  refine ⟨?_, fun hcs => ?_⟩
  · unfold Portable; rcases hγ1 with rfl | rfl <;> norm_num at * <;> omega
  · rw [abs_le] at hcs
    constructor
    · apply center_of_small <;> rcases hγ1 with rfl | rfl <;> norm_num at * <;> omega
    · unfold Portable; rcases hγ1 with rfl | rfl <;> norm_num at * <;> omega

/-- In verification, decoded `z` coefficients lie in `(-γ1, γ1]`, so
    `center z = z`. -/
theorem z_decoded_center (γ1 z : ℤ) (hγ1 : γ1 = 2 ^ 17 ∨ γ1 = 2 ^ 19)
    (h0 : -γ1 < z) (h1 : z ≤ γ1) : center z = z ∧ Portable z := by
  constructor
  · apply center_of_small <;> rcases hγ1 with rfl | rfl <;> norm_num at * <;> omega
  · unfold Portable; rcases hγ1 with rfl | rfl <;> norm_num at * <;> omega

/-! ## `value lsl d` in verification -/

/-- Model of `value lsl d` for the non-negative `t1` coefficients:
    `Nat.shiftLeft`. -/
def shiftT1 (value : ℕ) : ℕ := value <<< d

/-- A `t1` coefficient (10 bits, from `unpack_t1`) shifted by `d = 13`
    stays in `[0, q)`, so it is already canonical and portable; `lsl` does
    not overflow on any platform. -/
theorem shiftT1_lt_q (value : ℕ) (h : value < 2 ^ 10) :
    shiftT1 value = value * 2 ^ 13 ∧ (shiftT1 value : ℤ) < q ∧
      Portable (shiftT1 value : ℤ) := by
  unfold shiftT1 d
  rw [Nat.shiftLeft_eq]
  refine ⟨rfl, ?_, ?_⟩
  · simp only [q]; push_cast; omega
  · apply Portable.of_nat_lt; omega

end OcamlPq.MLDSA
