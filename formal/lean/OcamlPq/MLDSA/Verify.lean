import OcamlPq.MLDSA.SignAttempt

/-!
# Verification recovers the signer's `w1`

`verify_mu` (mldsa/mldsa_engine.ml:844–884) computes
`w'_approx = NTT⁻¹(Â·ẑ − ĉ·NTT(t1·2^d))` and `w'1 = use_hint w'_approx h`.
For an honestly generated signature, `Az − c·t1·2^d = w − c·s2 + c·t0`
(because `t = A·s1 + s2 = t1·2^d + t0`); this algebraic identity is taken
as the hypothesis `happrox` (modulo `q`). Under it, and when the signer
accepted the candidate, the verifier's `w'1` equals the signer's `w1`.
-/

namespace OcamlPq.MLDSA

section

variable {γ2 β : ℤ}

theorem makeHint_zero_or_one (γ2 low high : ℤ) :
    makeHint γ2 low high = 0 ∨ makeHint γ2 low high = 1 := by
  unfold makeHint; split_ifs <;> simp

/-- **Obligation 6 (per coefficient).** If the signer accepted
    (`|center r0| < γ2 - β`, `|center ct0| < γ2`, `‖cs2‖∞ ≤ β`) and the
    verifier's `w'_approx ≡ w - cs2 + ct0 (mod q)`, then the code's
    `use_hint w'_approx h` with the code's hint `h` returns the signer's
    `w1 = HighBits(w)`. -/
theorem useHint_recovers_w1 (hp : ParamOk γ2 β) (w cs2 ct0 wApprox : ℤ)
    (hcs2 : |center cs2| ≤ β)
    (hok : |center (codeR0 γ2 (w, cs2, ct0))| < γ2 - β)
    (hct0 : |center ct0| < γ2)
    (happrox : wApprox % q = (w - cs2 + ct0) % q) :
    useHint γ2 wApprox (codeHint γ2 (w, cs2, ct0)) = (decompose γ2 w).1 := by
  have hγ := hp.1
  have hhint : codeHint γ2 (w, cs2, ct0) = makeHintSpec γ2 (-ct0) (w - cs2 + ct0) :=
    hint_eq_spec hp w cs2 ct0 hcs2 hok hct0
  have h01 : codeHint γ2 (w, cs2, ct0) = 0 ∨ codeHint γ2 (w, cs2, ct0) = 1 :=
    makeHint_zero_or_one _ _ _
  rw [useHint_eq_spec hγ _ _ h01, useHintSpec_congr γ2 _ happrox, hhint,
    makeHintSpec_congr γ2 (z' := -center ct0) (r' := w - cs2 + ct0) (emod_neg_center ct0) rfl]
  have hc := abs_lt.mp hct0
  rw [useHint_makeHint hγ _ _ (by omega) (by omega)]
  have hcong : (w - cs2 + ct0 + -center ct0) % q = (w - cs2) % q := by
    have h1 : (w - cs2 + ct0 + -center ct0) = (w - cs2) + (ct0 - center ct0) := by ring
    have h2 : (ct0 - center ct0) % q = 0 := by
      have := center_emod ct0
      rw [Int.sub_emod, this, sub_self, Int.zero_emod]
    rw [h1, Int.add_emod, h2, add_zero, Int.emod_emod_of_dvd _ (dvd_refl q)]
  rw [highBits_congr γ2 hcong]
  exact (highBits_of_not_reject hp w cs2 hcs2 hok).1

/-- **Obligation 6 (vector form).** Coefficientwise over the whole `w`
    vector: the verifier's reconstructed `w'1` (`use_hint` applied to each
    `w'_approx` coefficient with the signer's hint) is the signer's `w1`, so
    `w1Encode` and hence `c̃` agree. Each entry is
    `((w, cs2, ct0), w'_approx)`. -/
theorem verify_recovers_w1 (hp : ParamOk γ2 β)
    (rows : List (List (WCoeff × ℤ)))
    (hcs2 : ∀ row ∈ rows, ∀ e ∈ row, |center e.1.2.1| ≤ β)
    (hok : ∀ row ∈ rows, ∀ e ∈ row, |center (codeR0 γ2 e.1)| < γ2 - β)
    (hct0 : ∀ row ∈ rows, ∀ e ∈ row, |center e.1.2.2| < γ2)
    (happrox : ∀ row ∈ rows, ∀ e ∈ row, e.2 % q = (e.1.1 - e.1.2.1 + e.1.2.2) % q) :
    rows.map (List.map fun e => useHint γ2 e.2 (codeHint γ2 e.1)) =
      rows.map (List.map fun e => (decompose γ2 e.1.1).1) := by
  apply List.map_congr_left
  intro row hrow
  apply List.map_congr_left
  intro e he
  have := useHint_recovers_w1 hp e.1.1 e.1.2.1 e.1.2.2 e.2 (hcs2 row hrow e he)
    (hok row hrow e he) (hct0 row hrow e he) (happrox row hrow e he)
  exact this

/-- The signer's accepted `z` also passes the verifier's `z` test: both run
    `vector_norm_violation_flag z (γ1 - β)` on the same `z`. -/
theorem verify_z_check_of_accepted {γ1 ω : ℤ} (z : List (List ℤ)) (rows : List (List WCoeff))
    (zs hs : List (List ℤ)) (h : signAttempt γ1 γ2 β ω z rows = some (zs, hs)) :
    zs = z ∧ vectorNormViolationFlag z (γ1 - β) = 0 := by
  unfold signAttempt at h
  simp only [vectorNormViolationFlag_eq, foldl_add_eq_sum, ite_or_ite, ite_one_zero_ne_zero] at h
  split_ifs at h with hrej
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  refine ⟨h.1.symm, ?_⟩
  rw [vectorNormViolationFlag_eq]
  simp only [not_or] at hrej
  simp [hrej.1.1.1]

/-- **Obligation 6 (end to end).** If the code's signing attempt accepts
    (returning hints `hs`), and the verifier's `w'_approx` coefficients are
    congruent to `w - cs2 + ct0`, then `hs` is the code's hint vector and
    `use_hint` on `w'_approx` with those hints reproduces the signer's `w1`
    in every coefficient. -/
theorem verify_recovers_w1_of_accepted (hp : ParamOk γ2 β) {γ1 ω : ℤ} (z : List (List ℤ))
    (rows : List (List (WCoeff × ℤ))) (zs hs : List (List ℤ))
    (hacc : signAttempt γ1 γ2 β ω z (rows.map (List.map Prod.fst)) = some (zs, hs))
    (hcs2 : ∀ row ∈ rows, ∀ e ∈ row, |center e.1.2.1| ≤ β)
    (happrox : ∀ row ∈ rows, ∀ e ∈ row, e.2 % q = (e.1.1 - e.1.2.1 + e.1.2.2) % q) :
    hs = (rows.map (List.map Prod.fst)).map (List.map (codeHint γ2)) ∧
    rows.map (List.map fun e => useHint γ2 e.2 (codeHint γ2 e.1)) =
      rows.map (List.map fun e => (decompose γ2 e.1.1).1) := by
  unfold signAttempt at hacc
  simp only [vectorNormViolationFlag_eq, foldl_add_eq_sum, ite_or_ite, ite_one_zero_ne_zero]
    at hacc
  split_ifs at hacc with hrej
  simp only [Option.some.injEq, Prod.mk.injEq] at hacc
  refine ⟨hacc.2.symm, ?_⟩
  simp only [not_or] at hrej
  obtain ⟨⟨⟨_, hR⟩, hC⟩, _⟩ := hrej
  rw [infNormGe_map] at hR hC
  simp only [not_exists, not_and, coeffNorm_eq, List.mem_map] at hR hC
  apply verify_recovers_w1 hp rows hcs2 _ _ happrox
  · intro row hrow e he
    exact lt_of_not_ge (hR _ ⟨row, hrow, rfl⟩ e.1 (List.mem_map.mpr ⟨e, he, rfl⟩))
  · intro row hrow e he
    exact lt_of_not_ge (hC _ ⟨row, hrow, rfl⟩ e.1 (List.mem_map.mpr ⟨e, he, rfl⟩))

end

end OcamlPq.MLDSA
