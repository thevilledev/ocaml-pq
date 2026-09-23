import OcamlPq.MLDSA.Rounding

/-!
# ML-DSA signing: the reference-implementation shortcuts

`sign_mu_with_randomness` (mldsa/mldsa_engine.ml:713–800; the
`attempt` body is 728–798) deviates from the
letter of FIPS 204 Algorithm 7 in three ways:

* it computes `r0 = center (w0 - cs2)` from the `Decompose(w) = (w1, w0)`
  it already has, instead of `r0 = LowBits(w - cs2)`;
* it computes the hint as `make_hint (center (r0 + ct0)) w1` instead of
  `MakeHint(-ct0, w - cs2 + ct0)`;
* it evaluates all four rejection conditions and ORs them together, whereas
  FIPS 204 computes `ct0` and the hint only when the first two conditions
  pass.

This file proves that none of this changes the accept/reject decision or
the signature, for both values of `γ2` and every `β ≤ 196` (the library
uses `β = 78, 196, 120`).
-/

namespace OcamlPq.MLDSA

/-- Admissible parameters: `γ2 ∈ {(q-1)/88, (q-1)/32}` and `0 ≤ β ≤ 196`.
    This covers ML-DSA-44 (`γ2 = 95232`, `β = 78`), ML-DSA-65 (`261888`,
    `196`) and ML-DSA-87 (`261888`, `120`). -/
def ParamOk (γ2 β : ℤ) : Prop := Gamma2Ok γ2 ∧ 0 ≤ β ∧ β ≤ 196

theorem paramOk_44 : ParamOk 95232 (39 * 2) := ⟨Or.inl rfl, by norm_num, by norm_num⟩
theorem paramOk_65 : ParamOk 261888 (49 * 4) := ⟨Or.inr rfl, by norm_num, by norm_num⟩
theorem paramOk_87 : ParamOk 261888 (60 * 2) := ⟨Or.inr rfl, by norm_num, by norm_num⟩

/-! ## Helper facts about `center`, `mod± q` and congruence -/

theorem center_eq_modPM (x : ℤ) : center x = modPM x q := by
  rw [center_eq]; unfold modPM; simp only [q]; norm_num

theorem coeffNorm_eq (x : ℤ) : coeffNorm x = |center x| := by
  rw [coeffNorm, center_eq_modPM]

theorem center_congr {x y : ℤ} (h : x % q = y % q) : center x = center y := by
  rw [center_eq, center_eq, h]

theorem highBits_congr (γ2 : ℤ) {x y : ℤ} (h : x % q = y % q) : highBits γ2 x = highBits γ2 y := by
  unfold highBits; rw [decomposeSpec_congr γ2 x y h]

theorem lowBits_congr (γ2 : ℤ) {x y : ℤ} (h : x % q = y % q) : lowBits γ2 x = lowBits γ2 y := by
  unfold lowBits; rw [decomposeSpec_congr γ2 x y h]

theorem makeHintSpec_congr (γ2 : ℤ) {z z' r r' : ℤ} (hz : z % q = z' % q) (hr : r % q = r' % q) :
    makeHintSpec γ2 z r = makeHintSpec γ2 z' r' := by
  unfold makeHintSpec
  rw [highBits_congr γ2 hr, highBits_congr γ2 (show (r + z) % q = (r' + z') % q by
    rw [Int.add_emod, hr, hz, ← Int.add_emod])]

theorem useHintSpec_congr (γ2 h : ℤ) {r r' : ℤ} (hr : r % q = r' % q) :
    useHintSpec γ2 h r = useHintSpec γ2 h r' := by
  unfold useHintSpec; rw [decomposeSpec_congr γ2 r r' hr]

theorem emod_sub_center (a b : ℤ) : (a - b) % q = (a - center b) % q :=
  (Int.ModEq.sub_left a (center_emod b)).symm

theorem emod_add_center (a b : ℤ) : (a + b) % q = (a + center b) % q :=
  (Int.ModEq.add_left a (center_emod b)).symm

theorem emod_neg_center (b : ℤ) : (-b) % q = (-center b) % q :=
  (Int.ModEq.neg (center_emod b)).symm

theorem center_sub_congr (a b : ℤ) : center (a - b) = center (a - center b) :=
  center_congr (emod_sub_center a b)

theorem center_add_congr (a b : ℤ) : center (a + b) = center (a + center b) :=
  center_congr (emod_add_center a b)

theorem modPM_q_of_small {x : ℤ} (h0 : -4190208 ≤ x) (h1 : x ≤ 4190208) : modPM x q = x := by
  rw [← center_eq_modPM]; exact center_of_small h0 h1

/-! ## Per-coefficient equivalences (obligation 5 (a)–(c)) -/

section Coefficient

variable {γ2 β : ℤ}

/-- Core case analysis: with `(w1, w0) = Decompose(w)` and `|c| ≤ β`, the
    low part of `w - c` either is `w0 - c` with the same high part (when
    `|w0 - c| < γ2 - β`), or both `|w0 - c|` and `|LowBits(w - c)|` are at
    least `γ2 - β`. -/
theorem lowBits_sub_small (hp : ParamOk γ2 β) (w c : ℤ) (hc0 : -β ≤ c) (hc1 : c ≤ β) :
    (|(decomposeSpec γ2 w).2 - c| < γ2 - β →
        highBits γ2 (w - c) = (decomposeSpec γ2 w).1 ∧
        lowBits γ2 (w - c) = (decomposeSpec γ2 w).2 - c) ∧
    (|(decomposeSpec γ2 w).2 - c| ≥ γ2 - β ↔ |lowBits γ2 (w - c)| ≥ γ2 - β) := by
  obtain ⟨hγ, hβ0, hβ1⟩ := hp
  obtain ⟨a1, a0, ha, hca⟩ := decomposeSpec_cases hγ w
  obtain ⟨b1, b0, hb, hcb⟩ := decomposeSpec_cases hγ (w - c)
  unfold highBits lowBits
  rw [ha, hb]
  simp only
  have hv0 : 0 ≤ w % q := Int.emod_nonneg _ (by decide)
  have hv1 : w % q < q := Int.emod_lt_of_pos _ q_pos
  rw [show w - c = w + -c by ring, ← Int.emod_add_emod] at hcb
  generalize w % q = x at *
  have hγ' := hγ
  rcases hγ' with rfl | rfl <;>
    rcases emod_q_cases (x + -c) (by simp only [q] at *; omega) (by simp only [q] at *; omega) with
      ⟨_, hw⟩ | ⟨_, _, hw⟩ | ⟨_, hw⟩ <;> rw [hw] at hcb
  all_goals
    simp only [q, abs_lt, le_abs] at *
    norm_num at *
    omega

/-- **(a)** The code's `r0` rejection test,
    `abs (center r0) >= γ2 - β` with `r0 = center (w0 - cs2)`, is
    equivalent to FIPS 204's `‖LowBits(w - cs2)‖∞ ≥ γ2 - β`, for every `w`
    and every `cs2` with `‖cs2‖∞ ≤ β`. -/
theorem r0_reject_iff (hp : ParamOk γ2 β) (w cs2 : ℤ) (hcs2 : |center cs2| ≤ β) :
    |center (center ((decompose γ2 w).2 - cs2))| ≥ γ2 - β ↔
      coeffNorm (lowBits γ2 (w - cs2)) ≥ γ2 - β := by
  have hγ := hp.1
  have hc := abs_le.mp hcs2
  have key := (lowBits_sub_small hp w (center cs2) hc.1 hc.2).2
  have hlb := decomposeSpec_range hγ (w - center cs2)
  have hw := decomposeSpec_range hγ w
  have hβ := hp.2
  have e1 : center ((decomposeSpec γ2 w).2 - center cs2) = (decomposeSpec γ2 w).2 - center cs2 := by
    apply center_of_small <;>
    rcases hγ with rfl | rfl <;> simp only [q] at * <;> norm_num at * <;> omega
  have e2 : center (lowBits γ2 (w - center cs2)) = lowBits γ2 (w - center cs2) := by
    unfold lowBits
    apply center_of_small <;>
    rcases hγ with rfl | rfl <;> simp only [q] at * <;> norm_num at * <;> omega
  rw [center_center, center_sub_congr, decompose_eq_spec hγ, e1, coeffNorm_eq,
    lowBits_congr γ2 (emod_sub_center w cs2), e2]
  exact key

/-- **(b)** When the `r0` test passes, `HighBits(w - cs2) = w1` and
    `LowBits(w - cs2) = center (w0 - cs2)`. -/
theorem highBits_of_not_reject (hp : ParamOk γ2 β) (w cs2 : ℤ) (hcs2 : |center cs2| ≤ β)
    (hok : |center (center ((decompose γ2 w).2 - cs2))| < γ2 - β) :
    highBits γ2 (w - cs2) = (decompose γ2 w).1 ∧
      lowBits γ2 (w - cs2) = center ((decompose γ2 w).2 - cs2) := by
  have hγ := hp.1
  have hc := abs_le.mp hcs2
  have hw := decomposeSpec_range hγ w
  have hβ := hp.2
  rw [center_center, center_sub_congr, decompose_eq_spec hγ] at hok
  rw [center_sub_congr, decompose_eq_spec hγ,
    highBits_congr γ2 (emod_sub_center w cs2), lowBits_congr γ2 (emod_sub_center w cs2)]
  have hsmall : center ((decomposeSpec γ2 w).2 - center cs2) =
      (decomposeSpec γ2 w).2 - center cs2 := by
    apply center_of_small <;>
    rcases hγ with rfl | rfl <;> simp only [q] at * <;> norm_num at * <;> omega
  rw [hsmall] at hok ⊢
  exact (lowBits_sub_small hp w (center cs2) hc.1 hc.2).1 hok

/-- **(c)** When the `r0` and `ct0` tests pass, the code's hint
    `make_hint (center (r0 + ct0)) w1`, with `r0 = center (w0 - cs2)`, equals
    FIPS 204's `MakeHint(-ct0, w - cs2 + ct0)`. -/
theorem hint_eq_spec (hp : ParamOk γ2 β) (w cs2 ct0 : ℤ) (hcs2 : |center cs2| ≤ β)
    (hok : |center (center ((decompose γ2 w).2 - cs2))| < γ2 - β)
    (hct0 : |center ct0| < γ2) :
    makeHint γ2 (center (center ((decompose γ2 w).2 - cs2) + ct0)) (decompose γ2 w).1 =
      makeHintSpec γ2 (-ct0) (w - cs2 + ct0) := by
  have hγ := hp.1
  have hβ := hp.2
  obtain ⟨hhigh, hlow⟩ := highBits_of_not_reject hp w cs2 hcs2 hok
  rw [center_center] at hok
  have hct := abs_lt.mp hct0
  have hr0 := abs_lt.mp hok
  -- replace `ct0` by its centered representative everywhere
  rw [center_add_congr, makeHintSpec_congr γ2 (z' := -center ct0) (r' := w - cs2 + center ct0)
    (emod_neg_center ct0) (emod_add_center (w - cs2) ct0)]
  rw [← hlow, ← hhigh]
  rw [center_of_small]
  · apply makeHint_eq_spec hγ
    · rw [hlow]; omega
    · rw [hlow]; omega
  · rw [hlow]; rcases hγ with rfl | rfl <;> omega
  · rw [hlow]; rcases hγ with rfl | rfl <;> omega

end Coefficient

end OcamlPq.MLDSA
