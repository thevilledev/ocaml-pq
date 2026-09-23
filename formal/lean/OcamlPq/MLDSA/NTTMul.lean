import OcamlPq.MLDSA.NTTMath

/-!
# NTT as evaluation, and multiplication in `ℤ_q[X]/(X^256 + 1)`

`NTT(w)[k] = w(ω_k)` with `ω_k = ζ^(2·BitRev8(k)+1)`; consequently
`NTT⁻¹(NTT(a) ∘ NTT(b)) = a·b mod (X^256 + 1)`, for the FIPS 204
specification and for the OCaml `ntt`/`pointwise`/`inverse_ntt`.
-/

namespace OcamlPq.MLDSA

open Polynomial

/-! ## The layer invariant -/

/-- After some layers, entry `k` holds the reduction of `w` modulo
    `X^B - c(k / B)` evaluated at position `k mod B`:
    `Σ_{t<N} w(k mod B + t·B) · c(k / B)^t`. -/
def StageEq (w x : ℕ → Zq) (B N : ℕ) (c : ℕ → Zq) : Prop :=
  ∀ k < 256, x k = ∑ t ∈ Finset.range N, w (k % B + t * B) * c (k / B) ^ t

theorem sum_range_two_mul (f : ℕ → Zq) (N : ℕ) :
    ∑ t ∈ Finset.range (2 * N), f t = ∑ t ∈ Finset.range N, (f (2 * t) + f (2 * t + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

theorem stage_step (len : ℕ) (hL : IsLen len) (B N : ℕ) (hB : B = 2 * len)
    (hN : 256 / (2 * len) = N) (w x : ℕ → Zq) (c zf : ℕ → Zq)
    (hx : StageEq w x B N c) (hz : ∀ b < N, zf b ^ 2 = c b) :
    StageEq w (layerF len zf x) len (2 * N)
      (fun b' => if b' % 2 = 0 then zf (b' / 2) else -zf (b' / 2)) := by
  subst hB
  intro k hk
  have hm := Nat.mod_lt k (show 0 < 2 * len by have := hL.pos; omega)
  obtain ⟨P1, P2⟩ := partner_arith hL k hk
  have hb := blk_lt hL k hk
  rw [hN] at hb
  unfold layerF
  rw [iteT hk, sum_range_two_mul]
  rcases Nat.lt_or_ge (k % (2 * len)) len with c' | c'
  · obtain ⟨e1, e2, e3, e4, e5⟩ := P1 c'
    rw [iteT c', hx k hk, hx (k + len) e1, e2, e3, e4, e5]
    have hzb := hz _ hb
    generalize k / (2 * len) = b at *
    generalize k % (2 * len) = p at *
    simp only [show 2 * b % 2 = 0 by omega, show 2 * b / 2 = b by omega, iteT]
    rw [← hzb, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [show p + 2 * t * len = p + t * (2 * len) by ring,
      show p + (2 * t + 1) * len = p + len + t * (2 * len) by ring]
    ring
  · obtain ⟨e1, e2, e3, e4, e5⟩ := P2 c'
    rw [iteF (by omega), hx k hk, hx (k - len) (by omega), e2, e3, e4, e5]
    have hzb := hz _ hb
    generalize k / (2 * len) = b at *
    generalize k % (2 * len) = p at *
    simp only [show (2 * b + 1) % 2 = 1 by omega, show (2 * b + 1) / 2 = b by omega,
      show (1 = 0) = False by simp, ite_false]
    rw [← hzb, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [show p - len + 2 * t * len = p - len + t * (2 * len) by ring,
      show p - len + (2 * t + 1) * len = p + t * (2 * len) by
        rw [add_mul, one_mul, show p - len + (2 * t * len + len) = p - len + len + 2 * t * len by ring,
          Nat.sub_add_cancel c']; ring]
    have n1 : (-zf b) ^ (2 * t) = zf b ^ (2 * t) := Even.neg_pow ⟨t, by ring⟩ _
    have n2 : (-zf b) ^ (2 * t + 1) = -(zf b ^ (2 * t + 1)) := Odd.neg_pow ⟨t, rfl⟩ _
    rw [n1, n2]
    ring

/-! ## `NTT(w)[k] = w(ω_k)` -/

/-- The evaluation points: `ω_k = ζ^(2·BitRev8(k)+1)`. -/
def ω (k : ℕ) : Zq := ζ ^ (2 * bitRev8 k + 1)

theorem zeta_sq_layer (s : ℕ) (hs : s < 8) (hs1 : 1 ≤ s) (N : ℕ) (hN : N = 2 ^ s) :
    ∀ b < N, (fun b => zetaSpec (2 ^ s + b)) b ^ 2 =
      (fun b' => if b' % 2 = 0 then (fun b => zetaSpec (2 ^ (s - 1) + b)) (b' / 2)
        else -(fun b => zetaSpec (2 ^ (s - 1) + b)) (b' / 2)) b := by
  intro b hb
  subst hN
  exact zeta_sq s hs hs1 b hb

theorem nttSpec_eval (w : ℕ → Zq) (k : ℕ) (hk : k < 256) :
    nttSpec w k = ∑ t ∈ Finset.range 256, w t * ω k ^ t := by
  have h0 : StageEq w w 256 1 (fun _ => -1) := by
    intro k hk
    simp [Nat.mod_eq_of_lt hk]
  have h1 := stage_step _ (isLen_layer 0 (by norm_num)) 256 1 (by norm_num) (by norm_num) w w _
    (fun b => zetaSpec (2 ^ 0 + b)) h0
    (by intro b hb; have : b = 0 := by omega
        subst this; simp only [zetaSpec]; rw [← pow_mul]; exact zeta_pow_256)
  have h2 := stage_step _ (isLen_layer 1 (by norm_num)) _ _ (by norm_num) (by norm_num) w _ _
    (fun b => zetaSpec (2 ^ 1 + b)) h1 (zeta_sq_layer 1 (by norm_num) le_rfl _ (by norm_num))
  have h3 := stage_step _ (isLen_layer 2 (by norm_num)) _ _ (by norm_num) (by norm_num) w _ _
    (fun b => zetaSpec (2 ^ 2 + b)) h2 (zeta_sq_layer 2 (by norm_num) (by norm_num) _ (by norm_num))
  have h4 := stage_step _ (isLen_layer 3 (by norm_num)) _ _ (by norm_num) (by norm_num) w _ _
    (fun b => zetaSpec (2 ^ 3 + b)) h3 (zeta_sq_layer 3 (by norm_num) (by norm_num) _ (by norm_num))
  have h5 := stage_step _ (isLen_layer 4 (by norm_num)) _ _ (by norm_num) (by norm_num) w _ _
    (fun b => zetaSpec (2 ^ 4 + b)) h4 (zeta_sq_layer 4 (by norm_num) (by norm_num) _ (by norm_num))
  have h6 := stage_step _ (isLen_layer 5 (by norm_num)) _ _ (by norm_num) (by norm_num) w _ _
    (fun b => zetaSpec (2 ^ 5 + b)) h5 (zeta_sq_layer 5 (by norm_num) (by norm_num) _ (by norm_num))
  have h7 := stage_step _ (isLen_layer 6 (by norm_num)) _ _ (by norm_num) (by norm_num) w _ _
    (fun b => zetaSpec (2 ^ 6 + b)) h6 (zeta_sq_layer 6 (by norm_num) (by norm_num) _ (by norm_num))
  have h8 := stage_step _ (isLen_layer 7 (by norm_num)) _ _ (by norm_num) (by norm_num) w _ _
    (fun b => zetaSpec (2 ^ 7 + b)) h7 (zeta_sq_layer 7 (by norm_num) (by norm_num) _ (by norm_num))
  have e := h8 k hk
  have hc : ∀ t : ℕ, (fun b' => if b' % 2 = 0 then zetaSpec (2 ^ 7 + b' / 2)
      else -zetaSpec (2 ^ 7 + b' / 2)) (k / 2 ^ (7 - 7)) ^ t = ω k ^ t := by
    intro t
    congr 1
    simp only [show 2 ^ (7 - 7) = 1 by norm_num, Nat.div_one]
    unfold ω zetaSpec
    have hl := bitRev8_last k hk
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · rw [h] at hl
      simp only [h, ite_true]
      rw [show bitRev8 (2 ^ 7 + k / 2) = 2 * bitRev8 k + 1 by
        rw [show 2 ^ 7 = 128 by rfl]; omega]
    · rw [h] at hl
      simp only [h, one_ne_zero, ite_false]
      rw [show 2 ^ 7 = 128 by rfl, ← hl, pow_add, zeta_pow_256]; ring
  rw [nttSpec_eq_layers]
  unfold fwdLayer
  refine e.trans ?_
  rw [show 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * 1))))))) = 256 by norm_num]
  apply Finset.sum_congr rfl
  intro t _
  rw [hc t, show 2 ^ (7 - 7) = 1 by norm_num, Nat.mod_one, mul_one, zero_add]

theorem ω_pow_256 (k : ℕ) : ω k ^ 256 = -1 := by
  unfold ω
  rw [← pow_mul, show (2 * bitRev8 k + 1) * 256 = 256 * (2 * bitRev8 k + 1) by ring, pow_mul,
    zeta_pow_256, pow_succ, pow_mul]
  norm_num

theorem ω_injOn (k k' : ℕ) (hk : k < 256) (hk' : k' < 256) (h : ω k = ω k') : k = k' := by
  have b1 := bitRev8_lt k hk
  have b2 := bitRev8_lt k' hk'
  have := zeta_pow_inj (by omega) (by omega) h
  have e : bitRev8 k = bitRev8 k' := by omega
  rw [← bitRev8_invol k hk, ← bitRev8_invol k' hk', e]

/-! ## Polynomials -/

/-- The polynomial `Σ_{i<256} w_i X^i` of a coefficient array. -/
noncomputable def toPoly (w : ℕ → Zq) : Zq[X] := ∑ i : Fin 256, C (w i) * X ^ (i : ℕ)

theorem toPoly_eval (w : ℕ → Zq) (x : Zq) :
    (toPoly w).eval x = ∑ t ∈ Finset.range 256, w t * x ^ t := by
  unfold toPoly
  rw [eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  exact Fin.sum_univ_eq_sum_range (fun t => w t * x ^ t) 256

theorem toPoly_degree (w : ℕ → Zq) : (toPoly w).degree < ((256 : ℕ) : WithBot ℕ) := by
  unfold toPoly
  exact degree_sum_fin_lt (fun i : Fin 256 => w i)

theorem toPoly_congr {v w : ℕ → Zq} (h : ∀ k < 256, v k = w k) : toPoly v = toPoly w := by
  unfold toPoly
  apply Finset.sum_congr rfl
  intro i _
  rw [h i i.isLt]

/-- `NTT(w)[k]` is the evaluation of `w` at `ω_k`. -/
theorem nttSpec_eq_eval (w : ℕ → Zq) (k : ℕ) (hk : k < 256) :
    nttSpec w k = (toPoly w).eval (ω k) := by
  rw [nttSpec_eval w k hk, toPoly_eval]

theorem monic_X256 : (X ^ 256 + 1 : Zq[X]).Monic := by
  have := monic_X_pow_add_C (R := Zq) (1 : Zq) (n := 256) (by norm_num)
  simpa using this

theorem eval_X256_ω (k : ℕ) : (X ^ 256 + 1 : Zq[X]).eval (ω k) = 0 := by
  simp [ω_pow_256]

set_option maxRecDepth 20000 in
/-- **NTT multiplication theorem (FIPS 204 §7.5)**:
    `NTT⁻¹(NTT(a) ∘ NTT(b)) = a·b` in `ℤ_q[X]/(X^256 + 1)`. -/
theorem invNttSpec_multiply (a b : ℕ → Zq) :
    toPoly (invNttSpec (multiplyNttSpec (nttSpec a) (nttSpec b))) =
      (toPoly a * toPoly b) %ₘ (X ^ 256 + 1) := by
  set c := invNttSpec (multiplyNttSpec (nttSpec a) (nttSpec b)) with hc
  have hnc : nttSpec c = multiplyNttSpec (nttSpec a) (nttSpec b) := by
    rw [hc, nttSpec_invNttSpec]
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq ((Finset.range 256).image ω)
  · have hcard : ((Finset.range 256).image ω).card = 256 := by
      rw [Finset.card_image_of_injOn]
      · exact Finset.card_range 256
      · intro x hx y hy hxy
        simp only [Finset.coe_range, Set.mem_Iio] at hx hy
        exact ω_injOn x y hx hy hxy
    rw [hcard]
    calc (toPoly c - (toPoly a * toPoly b) %ₘ (X ^ 256 + 1)).degree
        ≤ max (toPoly c).degree ((toPoly a * toPoly b) %ₘ (X ^ 256 + 1)).degree :=
          degree_sub_le _ _
      _ < ((256 : ℕ) : WithBot ℕ) := by
          apply max_lt (toPoly_degree c)
          have := degree_modByMonic_lt (toPoly a * toPoly b) monic_X256
          have hdeg : (X ^ 256 + 1 : Zq[X]).degree = ((256 : ℕ) : WithBot ℕ) := by
            have h := degree_X_pow_add_C (R := Zq) (n := 256) (by norm_num) (1 : Zq)
            rw [map_one] at h
            exact h
          rw [hdeg] at this
          exact this
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_range] at hk
    rw [← nttSpec_eq_eval c k hk, hnc]
    unfold multiplyNttSpec
    rw [nttSpec_eq_eval a k hk, nttSpec_eq_eval b k hk, ← eval_mul]
    conv_lhs => rw [← modByMonic_add_div (toPoly a * toPoly b) (X ^ 256 + 1)]
    rw [eval_add, eval_mul, eval_X256_ω, zero_mul, add_zero]

/-- `NTT` only reads the first 256 coefficients. -/
theorem nttSpec_congr {v w : ℕ → Zq} (h : ∀ k < 256, v k = w k) (k : ℕ) (hk : k < 256) :
    nttSpec v k = nttSpec w k := by
  rw [nttSpec_eq_eval v k hk, nttSpec_eq_eval w k hk, toPoly_congr h]

/-! ## The OCaml functions -/

/-- A canonical `int` whose residue is that of `y` is `y mod q`. -/
theorem eq_emod_of_cast {x y : ℤ} (h0 : 0 ≤ x) (h1 : x < q) (h : (x : Zq) = (y : Zq)) :
    x = y % q := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  simp only [q] at *
  push_cast at h
  omega

/-- **`inverse_ntt (ntt a) = a mod q`** for the OCaml functions, on every
    coefficient below 256. -/
theorem inverseNtt_ntt (a : ℕ → ℤ) (k : ℕ) (hk : k < 256) :
    inverseNtt (ntt a) k = a k % q := by
  apply eq_emod_of_cast (inverseNtt_canonical _ k).1 (inverseNtt_canonical _ k).2
  have := inverseNtt_refines (ntt a) k hk
  rw [ntt_refines, invNttSpec_nttSpec] at this
  exact this

/-- **`ntt (inverse_ntt a) = a mod q`** for the OCaml functions, on every
    coefficient below 256. -/
theorem ntt_inverseNtt (a : ℕ → ℤ) (k : ℕ) (hk : k < 256) :
    ntt (inverseNtt a) k = a k % q := by
  apply eq_emod_of_cast (ntt_canonical _ k).1 (ntt_canonical _ k).2
  have h1 := congrFun (ntt_refines (inverseNtt a)) k
  simp only [castArr] at h1
  rw [h1, nttSpec_congr (w := invNttSpec (castArr a)) (fun j hj => inverseNtt_refines a j hj) k hk,
    nttSpec_invNttSpec]
  rfl

/-- **Multiplication via the OCaml NTT**: for any integer arrays `a`, `b`,
    `inverse_ntt (pointwise (ntt a) (ntt b))` is the product `a·b` in
    `ℤ_q[X]/(X^256 + 1)`. -/
theorem inverseNtt_pointwise (a b : ℕ → ℤ) :
    toPoly (castArr (inverseNtt (pointwise (ntt a) (ntt b)))) =
      (toPoly (castArr a) * toPoly (castArr b)) %ₘ (X ^ 256 + 1) := by
  rw [← invNttSpec_multiply]
  apply toPoly_congr
  intro k hk
  rw [inverseNtt_refines _ k hk, pointwise_refines, ntt_refines, ntt_refines]

end OcamlPq.MLDSA
