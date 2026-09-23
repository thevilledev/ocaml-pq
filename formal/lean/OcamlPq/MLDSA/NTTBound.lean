import OcamlPq.MLDSA.NTTMul

/-!
# `‖c·s‖∞ ≤ τη`: the values `cs1`, `cs2` computed by the signer

The signer computes `cs1`/`cs2` as
`Array.map center (inverse_ntt (pointwise (ntt c) (ntt s)))`
(mldsa/mldsa_engine.ml:755–759, 767–771, with `poly_product_ntt` at 262–263).
For a challenge `c` with at most `τ` nonzero coefficients in `{-1, 0, 1}`
and `s` with coefficients in `[-η, η]`, this is the integer negacyclic
product `c·s` and each coefficient is at most `τη = β` in absolute value.
This discharges the hypothesis `‖cs2‖∞ ≤ β` of the signing theorems
(`r0_reject_iff`, `signAttempt_eq_spec`, …) and `|cs1| ≤ β` of
`z_portable_center`.
-/

namespace OcamlPq.MLDSA

open Polynomial

/-- The negacyclic product in `ℤ[X]/(X^256 + 1)`, coefficient `k`. -/
def negacyclic (a b : ℕ → ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range 256, a i * (if i ≤ k then b (k - i) else -b (k + 256 - i))

theorem coeff_toPoly (w : ℕ → Zq) (k : ℕ) (hk : k < 256) : (toPoly w).coeff k = w k := by
  unfold toPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp
  · intro b _ hb
    apply iteF
    intro h
    apply hb
    exact Fin.ext h.symm
  · simp

theorem toPoly_inj {v w : ℕ → Zq} (h : toPoly v = toPoly w) (k : ℕ) (hk : k < 256) : v k = w k := by
  rw [← coeff_toPoly v k hk, ← coeff_toPoly w k hk, h]

/-- For fixed `i < 256`, the `i`-th row of the negacyclic sum, evaluated at
    `ω_k`, is `Σ_j b_j ω^(i+j)`. -/
theorem negacyclic_row (b : ℕ → Zq) (x : Zq) (hx : x ^ 256 = -1) (i : ℕ) (hi : i < 256) :
    ∑ m ∈ Finset.range 256, (if i ≤ m then b (m - i) else -b (m + 256 - i)) * x ^ m =
      ∑ j ∈ Finset.range 256, b j * x ^ (i + j) := by
  have split1 : ∀ f : ℕ → Zq, ∑ m ∈ Finset.range 256, f m =
      ∑ m ∈ Finset.range i, f m + ∑ t ∈ Finset.range (256 - i), f (i + t) := by
    intro f; rw [← Finset.sum_range_add, Nat.add_sub_cancel' hi.le]
  have split2 : ∀ f : ℕ → Zq, ∑ m ∈ Finset.range 256, f m =
      ∑ t ∈ Finset.range (256 - i), f t + ∑ t ∈ Finset.range i, f (256 - i + t) := by
    intro f; rw [← Finset.sum_range_add, Nat.sub_add_cancel hi.le]
  rw [split1, split2, add_comm]
  have h1 : ∑ t ∈ Finset.range (256 - i),
      (if i ≤ i + t then b (i + t - i) else -b (i + t + 256 - i)) * x ^ (i + t) =
      ∑ t ∈ Finset.range (256 - i), b t * x ^ (i + t) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [iteT (by omega), show i + t - i = t by omega]
  have h2 : ∑ t ∈ Finset.range i, (if i ≤ t then b (t - i) else -b (t + 256 - i)) * x ^ t =
      ∑ t ∈ Finset.range i, b (256 - i + t) * x ^ (i + (256 - i + t)) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    rw [iteF (by omega), show t + 256 - i = 256 - i + t by omega,
      show i + (256 - i + t) = 256 + t by omega, pow_add, hx]
    ring
  rw [h1, h2]

theorem negacyclic_cast (a b : ℕ → ℤ) (m : ℕ) :
    ((negacyclic a b m : ℤ) : Zq) = ∑ i ∈ Finset.range 256,
      (a i : Zq) * (if i ≤ m then (b (m - i) : Zq) else -(b (m + 256 - i) : Zq)) := by
  unfold negacyclic
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem negacyclic_eval (a b : ℕ → ℤ) (x : Zq) (hx : x ^ 256 = -1) :
    (toPoly (castArr (negacyclic a b))).eval x =
      (toPoly (castArr a)).eval x * (toPoly (castArr b)).eval x := by
  rw [toPoly_eval, toPoly_eval, toPoly_eval, Finset.sum_mul_sum]
  simp only [castArr, negacyclic_cast, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have := negacyclic_row (fun j => (b j : Zq)) x hx i hi
  calc ∑ m ∈ Finset.range 256, (a i : Zq) *
          (if i ≤ m then (b (m - i) : Zq) else -(b (m + 256 - i) : Zq)) * x ^ m
      = (a i : Zq) * ∑ m ∈ Finset.range 256,
          (if i ≤ m then (b (m - i) : Zq) else -(b (m + 256 - i) : Zq)) * x ^ m := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
    _ = (a i : Zq) * ∑ j ∈ Finset.range 256, (b j : Zq) * x ^ (i + j) := by rw [this]
    _ = ∑ j ∈ Finset.range 256, (a i : Zq) * x ^ i * ((b j : Zq) * x ^ j) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [pow_add]; ring

theorem eval_modByMonic_X256 (p : Zq[X]) (k : ℕ) :
    (p %ₘ (X ^ 256 + 1)).eval (ω k) = p.eval (ω k) := by
  conv_rhs => rw [← modByMonic_add_div p (X ^ 256 + 1)]
  rw [eval_add, eval_mul, eval_X256_ω, zero_mul, add_zero]

set_option maxRecDepth 20000 in
/-- The negacyclic product is multiplication in `ℤ_q[X]/(X^256 + 1)`. -/
theorem toPoly_negacyclic (a b : ℕ → ℤ) :
    toPoly (castArr (negacyclic a b)) =
      (toPoly (castArr a) * toPoly (castArr b)) %ₘ (X ^ 256 + 1) := by
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq ((Finset.range 256).image ω)
  · have hcard : ((Finset.range 256).image ω).card = 256 := by
      rw [Finset.card_image_of_injOn]
      · exact Finset.card_range 256
      · intro x hx y hy hxy
        simp only [Finset.coe_range, Set.mem_Iio] at hx hy
        exact ω_injOn x y hx hy hxy
    rw [hcard]
    calc (toPoly (castArr (negacyclic a b)) -
            (toPoly (castArr a) * toPoly (castArr b)) %ₘ (X ^ 256 + 1)).degree
        ≤ max (toPoly (castArr (negacyclic a b))).degree
            ((toPoly (castArr a) * toPoly (castArr b)) %ₘ (X ^ 256 + 1)).degree :=
          degree_sub_le _ _
      _ < ((256 : ℕ) : WithBot ℕ) := by
          apply max_lt (toPoly_degree _)
          have := degree_modByMonic_lt (toPoly (castArr a) * toPoly (castArr b)) monic_X256
          have hdeg : (X ^ 256 + 1 : Zq[X]).degree = ((256 : ℕ) : WithBot ℕ) := by
            have h := degree_X_pow_add_C (R := Zq) (n := 256) (by norm_num) (1 : Zq)
            rw [map_one] at h
            exact h
          rw [hdeg] at this
          exact this
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    rw [negacyclic_eval a b _ (ω_pow_256 k), ← eval_mul, eval_modByMonic_X256]

/-- `|(c·s)_k| ≤ τη` for a sparse ternary `c` and `η`-bounded `s`. -/
theorem negacyclic_bound (c s : ℕ → ℤ) (τ η : ℤ)
    (hc : ∀ i < 256, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hτ : (((Finset.range 256).filter fun i => c i ≠ 0).card : ℤ) ≤ τ)
    (hs : ∀ j < 256, |s j| ≤ η) (k : ℕ) (hk : k < 256) :
    |negacyclic c s k| ≤ τ * η := by
  have hη : 0 ≤ η := le_trans (abs_nonneg _) (hs 0 (by norm_num))
  unfold negacyclic
  calc |∑ i ∈ Finset.range 256, c i * (if i ≤ k then s (k - i) else -s (k + 256 - i))|
      ≤ ∑ i ∈ Finset.range 256, |c i * (if i ≤ k then s (k - i) else -s (k + 256 - i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range 256, (if c i ≠ 0 then η else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        have hsi : |(if i ≤ k then s (k - i) else -s (k + 256 - i))| ≤ η := by
          split_ifs
          · exact hs _ (by omega)
          · rw [abs_neg]; exact hs _ (by omega)
        rw [abs_mul]
        by_cases hci : c i = 0
        · simp [hci]
        · rw [iteT hci]
          have h1 : |c i| = 1 := by rcases hc i hi with h | h | h <;> simp_all
          rw [h1, one_mul]; exact hsi
    _ = (((Finset.range 256).filter fun i => c i ≠ 0).card : ℤ) * η := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ τ * η := mul_le_mul_of_nonneg_right hτ hη

/-- **The signer's `cs1`/`cs2` are exact and bounded.** For a challenge `c`
    with at most `τ` nonzero coefficients, all in `{-1, 0, 1}`, and `s` with
    `|s_j| ≤ η`, if `τη ≤ (q-1)/2` then
    `center (inverse_ntt (pointwise (ntt c) (ntt s)))` is the integer
    negacyclic product `c·s`, and every coefficient is at most `τη`. -/
theorem center_cs (c s : ℕ → ℤ) (τ η : ℤ)
    (hc : ∀ i < 256, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hτ : (((Finset.range 256).filter fun i => c i ≠ 0).card : ℤ) ≤ τ)
    (hs : ∀ j < 256, |s j| ≤ η) (hsmall : τ * η ≤ 4190208) (k : ℕ) (hk : k < 256) :
    center (inverseNtt (pointwise (ntt c) (ntt s)) k) = negacyclic c s k ∧
      |center (inverseNtt (pointwise (ntt c) (ntt s)) k)| ≤ τ * η := by
  have hb := negacyclic_bound c s τ η hc hτ hs k hk
  have hcast : castArr (inverseNtt (pointwise (ntt c) (ntt s))) k =
      castArr (negacyclic c s) k := by
    apply toPoly_inj _ k hk
    rw [inverseNtt_pointwise, toPoly_negacyclic]
  simp only [castArr] at hcast
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
  have e : center (inverseNtt (pointwise (ntt c) (ntt s)) k) = negacyclic c s k := by
    have h1 := center_spec (inverseNtt (pointwise (ntt c) (ntt s)) k)
    rw [abs_le] at hb
    simp only [q] at h1
    push_cast at hcast
    omega
  exact ⟨e, e ▸ hb⟩

/-- Instantiation for the three parameter sets: `β = τη ∈ {78, 196, 120}`. -/
theorem center_cs_beta (c s : ℕ → ℤ) (τ η : ℤ)
    (hp : (τ = 39 ∧ η = 2) ∨ (τ = 49 ∧ η = 4) ∨ (τ = 60 ∧ η = 2))
    (hc : ∀ i < 256, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hτ : (((Finset.range 256).filter fun i => c i ≠ 0).card : ℤ) ≤ τ)
    (hs : ∀ j < 256, |s j| ≤ η) (k : ℕ) (hk : k < 256) :
    |center (inverseNtt (pointwise (ntt c) (ntt s)) k)| ≤ τ * η :=
  (center_cs c s τ η hc hτ hs
    (by rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num) k hk).2

/-- The hypothesis `‖cs2‖∞ ≤ β` used by `signAttempt_eq_spec` holds for the
    coefficients the code computes (`center` of the `inverse_ntt` output). -/
theorem cs_hyp (c s : ℕ → ℤ) (τ η : ℤ)
    (hp : (τ = 39 ∧ η = 2) ∨ (τ = 49 ∧ η = 4) ∨ (τ = 60 ∧ η = 2))
    (hc : ∀ i < 256, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hτ : (((Finset.range 256).filter fun i => c i ≠ 0).card : ℤ) ≤ τ)
    (hs : ∀ j < 256, |s j| ≤ η) (k : ℕ) (hk : k < 256) :
    |center (center (inverseNtt (pointwise (ntt c) (ntt s)) k))| ≤ τ * η := by
  rw [center_center]; exact center_cs_beta c s τ η hp hc hτ hs k hk

end OcamlPq.MLDSA
