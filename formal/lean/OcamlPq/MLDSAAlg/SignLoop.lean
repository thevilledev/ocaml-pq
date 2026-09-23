import OcamlPq.MLDSAAlg.Expand

/-!
# The signing rejection loop (`attempt`, `mldsa_engine.ml` lines 728–800)

The per-iteration computation (from the mask vector `y` to either a
signature or a rejection) is abstracted as a function `iter`; another module
proves that the implementation's rejection test and outputs equal FIPS 204's.
This module proves the properties of the loop itself:

* `nonce_lt`, `nonces_injective`, `mask_inputs_injective`: the mask nonces
  `κ + r = i·ℓ + r` (`i ≤ 820`, `r < ℓ`) are pairwise distinct and `< 2^16`,
  so `u16_le` never truncates and no two mask polynomials of one signing
  call share an XOF input (no mask reuse);
* `attempt_ok_iff`, `attempt_error_iff`: the loop runs at most 821
  iterations; it returns the first accepted candidate and fails with
  `Signing_failed` iff all 821 candidates are rejected;
* `attempt_eq_alg7`: given `iter` agrees with the FIPS 204 per-iteration
  step and `mask_polynomial` with `ExpandMask`, the loop returns exactly what
  FIPS 204 Algorithm 7 returns whenever Algorithm 7 finishes within 821
  iterations;
* `loop_bound_*`: FIPS 204 Appendix C requires a loop bound of at least 814;
  with per-iteration success probability at least `1/5.1` (the worst
  expected-repetition figure of Table 1) the failure probability is
  `< 2^-258` for 821 iterations, and 814 is the least bound giving
  `< 2^-256`.
-/

namespace OcamlPq.MLDSAAlg

/-- The OCaml `error` type (`mldsa_engine.ml`, lines 1–5). -/
inductive MLDSAError
  | invalidLength (what : String) (expected actual : ℕ)
  | invalidEncoding (message : String)
  | contextTooLong (length : ℕ)
  | signingFailed
  deriving DecidableEq

/-- The OCaml `attempt iteration` (`mldsa_engine.ml`, lines 728–800).
    `mask nonce` is `mask_polynomial rho_prime nonce`; `iter y` is the rest of
    the body (lines 733–799), returning `some σ` for `Ok (encode_signature …)`
    and `none` when `!rejection <> 0`. -/
def attempt {σ : Type} (l : ℕ) (mask : ℕ → Poly) (iter : (ℕ → Poly) → Option σ)
    (iteration : ℕ) : Except MLDSAError σ :=
  if iteration ≥ 821 then .error .signingFailed
  else
    let kappa := iteration * l
    let y := fun row => mask (kappa + row)
    match iter y with
    | some sig => .ok sig
    | none => attempt l mask iter (iteration + 1)
termination_by 821 - iteration

/-- The mask vector of iteration `i`: `y[row] = mask (i·ℓ + row)`. -/
def maskVector (l : ℕ) (mask : ℕ → Poly) (i : ℕ) : ℕ → Poly := fun row => mask (i * l + row)

theorem maskVector_eq (l : ℕ) (mask : ℕ → Poly) (i : ℕ) :
    maskVector l mask i = fun row => mask (i * l + row) := rfl

/-! ## Loop semantics -/

theorem attempt_ok_aux {σ : Type} (l : ℕ) (mask : ℕ → Poly) (iter : (ℕ → Poly) → Option σ) :
    ∀ k i (sig : σ), i + k = 821 →
      (attempt l mask iter i = .ok sig ↔
        ∃ j, i ≤ j ∧ j < 821 ∧ iter (maskVector l mask j) = some sig ∧
          ∀ j', i ≤ j' → j' < j → iter (maskVector l mask j') = none) := by
  intro k
  induction k with
  | zero =>
    intro i sig hi
    rw [attempt, ite_eq_left (by omega)]
    constructor
    · intro h; cases h
    · rintro ⟨j, h1, h2, -⟩; omega
  | succ k ih =>
    intro i sig hi
    rw [attempt, ite_eq_right (by omega)]
    simp only
    cases hit : iter (fun row => mask (i * l + row)) with
    | some s =>
      simp only
      constructor
      · rintro ⟨⟩
        exact ⟨i, le_rfl, by omega, hit, fun j' h1 h2 => by omega⟩
      · rintro ⟨j, h1, h2, h3, h4⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · rw [maskVector_eq, hit] at h3; rw [Option.some.inj h3]
        · have := h4 i le_rfl hlt
          rw [maskVector_eq, hit] at this; cases this
    | none =>
      simp only
      rw [ih (i + 1) sig (by omega)]
      constructor
      · rintro ⟨j, h1, h2, h3, h4⟩
        refine ⟨j, by omega, h2, h3, fun j' h1' h2' => ?_⟩
        rcases Nat.eq_or_lt_of_le h1' with rfl | hlt
        · exact hit
        · exact h4 j' (by omega) h2'
      · rintro ⟨j, h1, h2, h3, h4⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · rw [maskVector_eq, hit] at h3; cases h3
        · exact ⟨j, by omega, h2, h3, fun j' h1' h2' => h4 j' (by omega) h2'⟩

/-- **`attempt 0` returns `Ok σ` iff some iteration `i < 821` accepts with
    `σ` and every earlier iteration rejects.** In particular the loop
    performs at most 821 iterations and returns the first accepted
    candidate. -/
theorem attempt_ok_iff {σ : Type} (l : ℕ) (mask : ℕ → Poly) (iter : (ℕ → Poly) → Option σ)
    (sig : σ) :
    attempt l mask iter 0 = .ok sig ↔
      ∃ i < 821, iter (maskVector l mask i) = some sig ∧
        ∀ j < i, iter (maskVector l mask j) = none := by
  rw [attempt_ok_aux l mask iter 821 0 sig (by omega)]
  constructor
  · rintro ⟨j, -, h2, h3, h4⟩; exact ⟨j, h2, h3, fun j' h => h4 j' (by omega) h⟩
  · rintro ⟨j, h2, h3, h4⟩; exact ⟨j, by omega, h2, h3, fun j' _ h => h4 j' h⟩

theorem attempt_error_aux {σ : Type} (l : ℕ) (mask : ℕ → Poly) (iter : (ℕ → Poly) → Option σ) :
    ∀ k i (e : MLDSAError), i + k = 821 →
      (attempt l mask iter i = .error e ↔
        e = .signingFailed ∧ ∀ j, i ≤ j → j < 821 → iter (maskVector l mask j) = none) := by
  intro k
  induction k with
  | zero =>
    intro i e hi
    rw [attempt, ite_eq_left (by omega)]
    constructor
    · rintro ⟨⟩; exact ⟨rfl, fun j h1 h2 => by omega⟩
    · rintro ⟨rfl, -⟩; rfl
  | succ k ih =>
    intro i e hi
    rw [attempt, ite_eq_right (by omega)]
    simp only
    cases hit : iter (fun row => mask (i * l + row)) with
    | some s =>
      simp only
      constructor
      · intro h; cases h
      · rintro ⟨-, h⟩
        have := h i le_rfl (by omega)
        rw [maskVector_eq, hit] at this; cases this
    | none =>
      simp only
      rw [ih (i + 1) e (by omega)]
      constructor
      · rintro ⟨rfl, h⟩
        refine ⟨rfl, fun j h1 h2 => ?_⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · exact hit
        · exact h j (by omega) h2
      · rintro ⟨rfl, h⟩; exact ⟨rfl, fun j h1 h2 => h j (by omega) h2⟩

/-- **`attempt 0` fails iff it fails with `Signing_failed`, iff all 821
    candidates are rejected.** No other error is possible. -/
theorem attempt_error_iff {σ : Type} (l : ℕ) (mask : ℕ → Poly) (iter : (ℕ → Poly) → Option σ)
    (e : MLDSAError) :
    attempt l mask iter 0 = .error e ↔
      e = .signingFailed ∧ ∀ i < 821, iter (maskVector l mask i) = none := by
  rw [attempt_error_aux l mask iter 821 0 e (by omega)]
  simp

/-! ## Nonces -/

/-- Every mask nonce `κ + r = i·ℓ + r` (`i ≤ 820`, `r < ℓ`, `ℓ ∈ {4, 5, 7}`)
    is below `2^16` (at most `5746`), so `u16_le` is exact. -/
theorem nonce_lt {P : Params} (hP : P.Valid) {i r : ℕ} (hi : i < 821) (hr : r < P.l) :
    i * P.l + r ≤ 5746 ∧ i * P.l + r < 2 ^ 16 := by
  obtain ⟨hl, -⟩ := hP.facts
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with h | h | h <;> rw [h] at hr ⊢ <;> omega

/-- **Mask nonces are pairwise distinct** across all iterations and rows. -/
theorem nonces_injective {l i i' r r' : ℕ} (hr : r < l) (hr' : r' < l)
    (h : i * l + r = i' * l + r') : i = i' ∧ r = r' := by
  have hl : 0 < l := by omega
  have e1 : (i * l + r) / l = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hl, Nat.div_eq_of_lt hr, zero_add]
  have e2 : (i' * l + r') / l = i' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hl, Nat.div_eq_of_lt hr', zero_add]
  have hi : i = i' := by rw [← e1, ← e2, h]
  subst hi
  exact ⟨rfl, by omega⟩

/-- **No mask reuse.** Within one signing call (fixed `ρ″`), two mask
    polynomials computed in iterations `i, i' < 821`, rows `r, r' < ℓ` have
    the same SHAKE256 input only if they are the same polynomial of the same
    iteration. -/
theorem mask_inputs_injective {P : Params} (hP : P.Valid) (rhoPrime : Bytes)
    {i i' r r' : ℕ} (hi : i < 821) (hi' : i' < 821) (hr : r < P.l) (hr' : r' < P.l)
    (h : rhoPrime ++ u16le (i * P.l + r) = rhoPrime ++ u16le (i' * P.l + r')) :
    i = i' ∧ r = r' := by
  have h' := List.append_cancel_left h
  exact nonces_injective hr hr' (u16le_inj (nonce_lt hP hi hr).2 (nonce_lt hP hi' hr').2 h')

/-- The `int` intermediates of the loop control are `Portable`:
    `iteration + 1 ≤ 821`, `kappa = iteration * P.l ≤ 5740`,
    `kappa + row ≤ 5746`. -/
theorem attempt_portable {P : Params} (hP : P.Valid) {i r : ℕ} (hi : i < 821) (hr : r < P.l) :
    Portable ((i + 1 : ℕ) : ℤ) ∧ Portable ((i * P.l : ℕ) : ℤ) ∧
      Portable ((i * P.l + r : ℕ) : ℤ) := by
  have := (nonce_lt hP hi hr).1
  exact ⟨Portable.of_nat_lt (by omega), Portable.of_nat_lt (by nlinarith),
    Portable.of_nat_lt (by omega)⟩

/-! ## Relation to FIPS 204 Algorithm 7 -/

/-- The `while (z, h) = ⊥` loop of FIPS 204 Algorithm 7 (lines 10–32), run for
    at most `fuel` iterations starting from `κ`: `y ← ExpandMask(ρ″, κ)`, the
    body `step y` (lines 12–30, `none` = `(z, h) ← ⊥`), then `κ ← κ + ℓ`.
    `expandMask κ r` is `ExpandMask(ρ″, κ)[r]`. -/
def alg7Loop {σ : Type} (l : ℕ) (expandMask : ℕ → ℕ → Poly) (step : (ℕ → Poly) → Option σ) :
    ℕ → ℕ → Option σ
  | 0, _ => none
  | fuel + 1, kappa =>
    match step (expandMask kappa) with
    | some sig => some sig
    | none => alg7Loop l expandMask step fuel (kappa + l)

theorem alg7Loop_eq {σ : Type} (l : ℕ) (expandMask : ℕ → ℕ → Poly)
    (step : (ℕ → Poly) → Option σ) :
    ∀ fuel i (sig : σ), alg7Loop l expandMask step fuel (i * l) = some sig ↔
      ∃ j, i ≤ j ∧ j < i + fuel ∧ step (expandMask (j * l)) = some sig ∧
        ∀ j', i ≤ j' → j' < j → step (expandMask (j' * l)) = none := by
  intro fuel
  induction fuel with
  | zero => intro i sig; simp [alg7Loop]; intro j h1 h2; omega
  | succ f ih =>
    intro i sig
    rw [alg7Loop]
    cases hs : step (expandMask (i * l)) with
    | some s =>
      simp only
      constructor
      · rintro ⟨⟩; exact ⟨i, le_rfl, by omega, hs, fun j' h1 h2 => by omega⟩
      · rintro ⟨j, h1, h2, h3, h4⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · rw [hs] at h3; exact h3
        · have := h4 i le_rfl hlt; rw [hs] at this; cases this
    | none =>
      simp only
      rw [show i * l + l = (i + 1) * l by ring, ih (i + 1) sig]
      constructor
      · rintro ⟨j, h1, h2, h3, h4⟩
        refine ⟨j, by omega, by omega, h3, fun j' h1' h2' => ?_⟩
        rcases Nat.eq_or_lt_of_le h1' with rfl | hlt
        · exact hs
        · exact h4 j' (by omega) h2'
      · rintro ⟨j, h1, h2, h3, h4⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · rw [hs] at h3; cases h3
        · exact ⟨j, by omega, by omega, h3, fun j' h1' h2' => h4 j' (by omega) h2'⟩

/-- **Obligation 6 (loop refinement).** Suppose the implementation's
    per-iteration computation `iter` agrees with FIPS 204's `step` on the mask
    vectors it is given, and `mask (κ + r) = ExpandMask(ρ″, κ)[r]` (proved in
    `maskPolynomial_eq`). Then
    * if Algorithm 7 returns `σ` within `fuel ≤ 821` iterations, the OCaml loop
      returns `Ok σ`;
    * if the OCaml loop returns `Ok σ`, Algorithm 7 returns `σ` within 821
      iterations;
    * the OCaml loop returns `Error Signing_failed` iff Algorithm 7 does not
      finish within 821 iterations. -/
theorem attempt_eq_alg7 {σ : Type} (l : ℕ) (mask : ℕ → Poly) (iter : (ℕ → Poly) → Option σ)
    (expandMask : ℕ → ℕ → Poly) (step : (ℕ → Poly) → Option σ)
    (hmask : ∀ kappa r, r < l → mask (kappa + r) = expandMask kappa r)
    (hiter : ∀ y y' : ℕ → Poly, (∀ r < l, y r = y' r) → iter y = step y') :
    (∀ fuel ≤ 821, ∀ sig, alg7Loop l expandMask step fuel 0 = some sig →
        attempt l mask iter 0 = .ok sig) ∧
    (∀ sig, attempt l mask iter 0 = .ok sig → alg7Loop l expandMask step 821 0 = some sig) ∧
    (∀ e, attempt l mask iter 0 = .error e ↔
        e = .signingFailed ∧ alg7Loop l expandMask step 821 0 = none) := by
  have hy : ∀ i, iter (maskVector l mask i) = step (expandMask (i * l)) :=
    fun i => hiter _ _ (fun r hr => hmask _ _ hr)
  have h0 : ∀ fuel (sig : σ), alg7Loop l expandMask step fuel 0 = some sig ↔
      ∃ j, j < fuel ∧ step (expandMask (j * l)) = some sig ∧
        ∀ j' < j, step (expandMask (j' * l)) = none := by
    intro fuel sig
    have := alg7Loop_eq l expandMask step fuel 0 sig
    simpa using this
  refine ⟨fun fuel hf sig h => ?_, fun sig h => ?_, fun e => ?_⟩
  · obtain ⟨j, h1, h2, h3⟩ := (h0 fuel sig).mp h
    exact (attempt_ok_iff l mask iter sig).mpr ⟨j, by omega, by rw [hy]; exact h2,
      fun j' hj' => by rw [hy]; exact h3 j' hj'⟩
  · obtain ⟨j, h1, h2, h3⟩ := (attempt_ok_iff l mask iter sig).mp h
    exact (h0 821 sig).mpr ⟨j, h1, by rw [← hy]; exact h2, fun j' hj' => by rw [← hy]; exact h3 j' hj'⟩
  · rw [attempt_error_iff]
    constructor
    · rintro ⟨rfl, h⟩
      refine ⟨rfl, ?_⟩
      cases hl : alg7Loop l expandMask step 821 0 with
      | none => rfl
      | some sig =>
        obtain ⟨j, h1, h2, -⟩ := (h0 821 sig).mp hl
        rw [← hy, h j h1] at h2; cases h2
    · rintro ⟨rfl, h⟩
      refine ⟨rfl, fun i hi => ?_⟩
      -- the first accepted iteration would make Algorithm 7 return
      by_contra hne
      obtain ⟨sig, hsig⟩ := Option.ne_none_iff_exists'.mp hne
      classical
      let j := Nat.find (p := fun j => ∃ sig, iter (maskVector l mask j) = some sig) ⟨i, sig, hsig⟩
      have hj : ∃ sig, iter (maskVector l mask j) = some sig := Nat.find_spec
        (p := fun j => ∃ sig, iter (maskVector l mask j) = some sig) ⟨i, sig, hsig⟩
      have hjle : j ≤ i := Nat.find_min' (p := fun j => ∃ sig, iter (maskVector l mask j) = some sig)
        ⟨i, sig, hsig⟩ ⟨sig, hsig⟩
      obtain ⟨sig', hsig'⟩ := hj
      have hmin : ∀ j' < j, iter (maskVector l mask j') = none := by
        intro j' hj'
        have := Nat.find_min (p := fun j => ∃ sig, iter (maskVector l mask j) = some sig)
          ⟨i, sig, hsig⟩ hj'
        cases hc : iter (maskVector l mask j') with
        | none => rfl
        | some s => exact absurd ⟨s, hc⟩ this
      have := (h0 821 sig').mpr ⟨j, by omega, by rw [← hy]; exact hsig',
        fun j' hj' => by rw [← hy]; exact hmin j' hj'⟩
      rw [h] at this; cases this

/-! ## Loop bound -/

/-- With per-iteration success probability at least `1/5.1 = 10/51` (the
    worst case, ML-DSA-65, of the expected-repetition row of FIPS 204
    Table 1), all 821 iterations fail with probability at most
    `(41/51)^821 < 2^-258`. -/
theorem loop_bound_821 : (41 : ℕ) ^ 821 * 2 ^ 258 < 51 ^ 821 := by decide +kernel

/-- 814, the minimum loop bound FIPS 204 Appendix C permits, is exactly the
    least `n` with `(41/51)^n < 2^-256`. -/
theorem loop_bound_814_minimal :
    (41 : ℕ) ^ 814 * 2 ^ 256 < 51 ^ 814 ∧ ¬ ((41 : ℕ) ^ 813 * 2 ^ 256 < 51 ^ 813) := by
  constructor <;> decide +kernel

/-- For ML-DSA-44 (4.25 expected repetitions, success `≥ 4/17`) and ML-DSA-87
    (3.85, success `≥ 20/77`) the 821-iteration failure bound is below
    `2^-317` and `2^-356` respectively. -/
theorem loop_bound_821_44_87 :
    (13 : ℕ) ^ 821 * 2 ^ 317 < 17 ^ 821 ∧ (57 : ℕ) ^ 821 * 2 ^ 356 < 77 ^ 821 := by
  constructor <;> decide +kernel

/-- The implementation's bound (821) is at least FIPS 204's minimum (814). -/
theorem bound_ge_fips : 814 ≤ 821 := by decide

end OcamlPq.MLDSAAlg
