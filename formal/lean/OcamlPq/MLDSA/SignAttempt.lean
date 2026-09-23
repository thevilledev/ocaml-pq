import OcamlPq.MLDSA.Flags

/-!
# One signing attempt: code versus FIPS 204 Algorithm 7

The body of `attempt` in `sign_mu_with_randomness`
(mldsa/mldsa_engine.ml:728–798), from the point where `w`, `z`, `cs2` and
`ct0` are known, against FIPS 204 Algorithm 7 lines 17–29 (the rejection
tests and the hint).

The `w`-side state is given per coefficient as a triple
`(w, cs2, ct0)` at the same `(row, index)`: the OCaml loops read
`w.(row).(index)`, `cs2.(row).(index)` and `ct0.(row).(index)` together,
so a vector of such triples is exactly the data they consume.
-/

namespace OcamlPq.MLDSA

/-- `(w, cs2, ct0)` at one `(row, index)`. -/
abbrev WCoeff := ℤ × ℤ × ℤ

/-- The code's `r0` coefficient: `center (w0 - cs2)` with
    `(w1, w0) = decompose w` (mldsa/mldsa_engine.ml:735–747, 772–777). -/
def codeR0 (γ2 : ℤ) (e : WCoeff) : ℤ := center ((decompose γ2 e.1).2 - e.2.1)

/-- The code's hint coefficient (mldsa/mldsa_engine.ml:789–790). -/
def codeHint (γ2 : ℤ) (e : WCoeff) : ℤ :=
  makeHint γ2 (center (codeR0 γ2 e + e.2.2)) (decompose γ2 e.1).1

/-- Model of the tail of `attempt` (mldsa/mldsa_engine.ml:766–798): all four
    rejection flags are computed and ORed; the hint count is accumulated
    row by row. Returns `some (z, hints)` when the candidate is accepted. -/
def signAttempt (γ1 γ2 β ω : ℤ) (z : List (List ℤ)) (rows : List (List WCoeff)) :
    Option (List (List ℤ) × List (List ℤ)) :=
  let rejection := vectorNormViolationFlag z (γ1 - β)
  let r0 := rows.map (List.map (codeR0 γ2))
  let rejection := rejection ||| vectorNormViolationFlag r0 (γ2 - β)
  let ct0 := rows.map (List.map fun e => e.2.2)
  let rejection := rejection ||| vectorNormViolationFlag ct0 γ2
  let hints := rows.map (List.map (codeHint γ2))
  let hintCount := (hints.map fun row => row.foldl (· + ·) 0).foldl (· + ·) 0
  let tooManyHints := if hintCount > ω then 1 else 0
  let rejection := rejection ||| tooManyHints
  if rejection ≠ 0 then none else some (z, hints)

/-- FIPS 204 Algorithm 7, lines 17–29 (for fixed `w`, `z`, `cs2`, `ct0`):
    `r0 ← LowBits(w - cs2)`; reject if `‖z‖∞ ≥ γ1 - β` or `‖r0‖∞ ≥ γ2 - β`;
    otherwise `h ← MakeHint(-ct0, w - cs2 + ct0)` and reject if
    `‖ct0‖∞ ≥ γ2` or `h` has more than `ω` ones. -/
def signAttemptSpec (γ1 γ2 β ω : ℤ) (z : List (List ℤ)) (rows : List (List WCoeff)) :
    Option (List (List ℤ) × List (List ℤ)) :=
  let r0 := rows.map (List.map fun e => lowBits γ2 (e.1 - e.2.1))
  if infNormGe z (γ1 - β) ∨ infNormGe r0 (γ2 - β) then none
  else
    let ct0 := rows.map (List.map fun e => e.2.2)
    let h := rows.map (List.map fun e => makeHintSpec γ2 (-e.2.2) (e.1 - e.2.1 + e.2.2))
    if infNormGe ct0 γ2 ∨ (h.map fun row => row.sum).sum > ω then none else some (z, h)

theorem foldl_add_eq_sum (l : List ℤ) : l.foldl (· + ·) 0 = l.sum := by
  rw [List.foldl_eq_foldr, List.sum_eq_foldr]

theorem ite_or_ite (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if P then 1 else 0 : ℕ) ||| (if Q then 1 else 0)) = if P ∨ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem ite_one_zero_ne_zero (P : Prop) [Decidable P] : ((if P then 1 else 0 : ℕ) ≠ 0) ↔ P := by
  by_cases hP : P <;> simp [hP]

theorem infNormGe_map {α : Type} (f : α → ℤ) (rows : List (List α)) (b : ℤ) :
    infNormGe (rows.map (List.map f)) b ↔ ∃ row ∈ rows, ∃ e ∈ row, coeffNorm (f e) ≥ b := by
  unfold infNormGe
  constructor
  · rintro ⟨p, hp, x, hx, h⟩
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact ⟨row, hrow, e, he, h⟩
  · rintro ⟨row, hrow, e, he, h⟩
    exact ⟨_, List.mem_map.mpr ⟨row, hrow, rfl⟩, _, List.mem_map.mpr ⟨e, he, rfl⟩, h⟩

/-- **Obligation 5 (check order).** For every candidate with
    `‖cs2‖∞ ≤ β`, the code's attempt (all flags ORed, hints always computed)
    accepts exactly when FIPS 204 Algorithm 7 accepts, and then returns the
    same `z` and the same hint vector. -/
theorem signAttempt_eq_spec {γ2 β : ℤ} (hp : ParamOk γ2 β) (γ1 ω : ℤ)
    (z : List (List ℤ)) (rows : List (List WCoeff))
    (hcs2 : ∀ row ∈ rows, ∀ e ∈ row, |center e.2.1| ≤ β) :
    signAttempt γ1 γ2 β ω z rows = signAttemptSpec γ1 γ2 β ω z rows := by
  -- the `r0` tests agree coefficientwise
  have hR : infNormGe (rows.map (List.map (codeR0 γ2))) (γ2 - β) ↔
      infNormGe (rows.map (List.map fun e => lowBits γ2 (e.1 - e.2.1))) (γ2 - β) := by
    rw [infNormGe_map, infNormGe_map]
    constructor
    · rintro ⟨row, hrow, e, he, hx⟩
      refine ⟨row, hrow, e, he, ?_⟩
      rw [coeffNorm_eq] at hx
      exact (r0_reject_iff hp e.1 e.2.1 (hcs2 row hrow e he)).mp hx
    · rintro ⟨row, hrow, e, he, hx⟩
      refine ⟨row, hrow, e, he, ?_⟩
      rw [coeffNorm_eq]
      exact (r0_reject_iff hp e.1 e.2.1 (hcs2 row hrow e he)).mpr hx
  -- when the `r0` and `ct0` tests pass, the hints agree
  have hH : ¬ infNormGe (rows.map (List.map (codeR0 γ2))) (γ2 - β) →
      ¬ infNormGe (rows.map (List.map fun e => e.2.2)) γ2 →
      rows.map (List.map (codeHint γ2)) =
        rows.map (List.map fun e => makeHintSpec γ2 (-e.2.2) (e.1 - e.2.1 + e.2.2)) := by
    intro h1 h2
    rw [infNormGe_map] at h1 h2
    simp only [not_exists, not_and, coeffNorm_eq] at h1 h2
    apply List.map_congr_left
    intro row hrow
    apply List.map_congr_left
    intro e he
    have hr0 : |center (codeR0 γ2 e)| < γ2 - β := lt_of_not_ge (h1 row hrow e he)
    have hct0 : |center e.2.2| < γ2 := lt_of_not_ge (h2 row hrow e he)
    exact hint_eq_spec hp e.1 e.2.1 e.2.2 (hcs2 row hrow e he) hr0 hct0
  unfold signAttempt signAttemptSpec
  simp only [vectorNormViolationFlag_eq, foldl_add_eq_sum, ite_or_ite, ite_one_zero_ne_zero]
  by_cases hA1 : infNormGe z (γ1 - β)
  · simp [hA1]
  by_cases hA2 : infNormGe (rows.map (List.map fun e => lowBits γ2 (e.1 - e.2.1))) (γ2 - β)
  · simp [hA1, hA2, hR.mpr hA2]
  have hA2' : ¬ infNormGe (rows.map (List.map (codeR0 γ2))) (γ2 - β) := fun h => hA2 (hR.mp h)
  by_cases hC : infNormGe (rows.map (List.map fun e => e.2.2)) γ2
  · simp [hA1, hA2, hA2', hC]
  rw [hH hA2' hC]
  simp [hA1, hA2, hA2', hC]

/-! ## Portability of the `int` arithmetic in the attempt -/

/-- The `int` expressions of the attempt body are portable for every input
    the code can produce: `w0 - cs2` (line 775) with `cs2 = center …`,
    `r0 + ct0` (line 789) with both operands `center` outputs, and
    `abs (center x)` in the norm checks (line 459). -/
theorem attempt_portable {γ2 : ℤ} (hγ : Gamma2Ok γ2) (w x y z : ℤ) :
    Portable ((decompose γ2 w).2 - center x) ∧
    Portable (center y + center z) ∧
    Portable |center y| := by
  have hd := decomposeSpec_range hγ w
  rw [← decompose_eq_spec hγ] at hd
  have hx := center_bounds x
  have hy := center_bounds y
  have hz := center_bounds z
  refine ⟨?_, ?_, ?_⟩
  · unfold Portable; rcases hγ with rfl | rfl <;> omega
  · unfold Portable; omega
  · unfold Portable; rw [abs_eq_max_neg]; omega

theorem codeHint_zero_or_one (γ2 : ℤ) (e : WCoeff) : codeHint γ2 e = 0 ∨ codeHint γ2 e = 1 := by
  unfold codeHint makeHint; split_ifs <;> simp

/-- `hint_count` (lines 786–792) never exceeds the number of coefficients
    (`k·n ≤ 8·256`), so it is portable. -/
theorem hintCount_bounds (γ2 : ℤ) (rows : List (List WCoeff)) :
    0 ≤ ((rows.map (List.map (codeHint γ2))).map fun row => row.sum).sum ∧
    ((rows.map (List.map (codeHint γ2))).map fun row => row.sum).sum ≤
      ((rows.map List.length).sum : ℤ) := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hrow : 0 ≤ (row.map (codeHint γ2)).sum ∧ (row.map (codeHint γ2)).sum ≤ (row.length : ℤ) := by
      induction row with
      | nil => simp
      | cons e row ihr =>
        rcases codeHint_zero_or_one γ2 e with h | h <;>
          simp only [List.map_cons, List.sum_cons, h, List.length_cons] <;> push_cast <;> omega
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    omega

end OcamlPq.MLDSA
