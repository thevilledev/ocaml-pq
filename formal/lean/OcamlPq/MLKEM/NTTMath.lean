import OcamlPq.MLKEM.NTTLayers

/-!
# The NTT as the Chinese-remainder isomorphism

With `R_q = ℤ_q[X]/(X^256 + 1)` and `γ_i = ζ^(2·BitRev7(i)+1)` (FIPS 203 §4.3):

* `fipsNtt_crt`: output pair `i` of `NTT(f)` is `f mod (X² − γ_i)`, i.e.
  `X² − γ_i ∣ f − (f̂[2i] + f̂[2i+1]·X)`;
* `fipsNtt_unique`: `NTT(f)` is the only array with that property;
* `fipsNtt_add`, `fipsNtt_mulNTT`: `NTT` is additive and turns products in
  `R_q` into `MultiplyNTTs`;
* `fipsNttInv_multiplyNTTs`: `NTT⁻¹(MultiplyNTTs(NTT(f), NTT(g))) = f·g`
  in `R_q`, i.e. `X^256 + 1 ∣ f·g − NTT⁻¹(…)`, and it is the reduced product
  `(f·g) %ₘ (X^256 + 1)`.

Together with `fipsNttInv_fipsNtt` and `fipsNtt_fipsNttInv` this makes `NTT`
a ring isomorphism `R_q ≅ ∏ᵢ ℤ_q[X]/(X² − γ_i)`.
-/

namespace OcamlPq.MLKEM

open Polynomial

/-- `Σ_{j<n} g[s+j]·X^j`. -/
noncomputable def blockPoly (g : Poly) (s n : ℕ) : Zq[X] :=
  ∑ j ∈ Finset.range n, C (g (s + j)) * X ^ j

/-- The polynomial `f = Σ_{k<256} f[k]·X^k` of an array (FIPS 203 §2.4). -/
noncomputable def polyOf (g : Poly) : Zq[X] := blockPoly g 0 256

theorem blockPoly_split (g : Poly) (s m : ℕ) :
    blockPoly g s (2 * m) = blockPoly g s m + X ^ m * blockPoly g (s + m) m := by
  unfold blockPoly
  rw [two_mul, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add, show s + (m + j) = s + m + j by ring]; ring

theorem blockPoly_two (g : Poly) (s : ℕ) : blockPoly g s 2 = C (g s) + C (g (s + 1)) * X := by
  simp [blockPoly, Finset.sum_range_succ]

theorem polyOf_congr {g h : Poly} (hgh : EqOn256 g h) : polyOf g = polyOf h := by
  unfold polyOf blockPoly
  apply Finset.sum_congr rfl
  intro j hj
  rw [hgh _ (by simpa using Finset.mem_range.1 hj)]

theorem polyOf_add (g h : Poly) : polyOf (g + h) = polyOf g + polyOf h := by
  unfold polyOf blockPoly
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply, map_add]; ring

/-! ## The CRT invariant through the layers -/

/-- The modulus of block `b` before layer `k`: `X^(2^(8−k)) − cc k b`. -/
def cc (k b : ℕ) : Zq :=
  if k = 0 then -1
  else if b % 2 = 0 then zeta ^ bitRev7 (2 ^ (k - 1) + b / 2)
  else -zeta ^ bitRev7 (2 ^ (k - 1) + b / 2)

set_option maxRecDepth 100000 in
/-- The zeta of block `b` in layer `k` is a square root of that block's
    modulus constant. -/
theorem zeta_sq_check : ∀ k < 7, ∀ b < 2 ^ k, (zeta ^ bitRev7 (2 ^ k + b)) ^ 2 = cc k b := by
  unfold cc zeta; decide +kernel

set_option maxRecDepth 100000 in
/-- After the last layer, block `i` has modulus `X² − γ_i`. -/
theorem cc_gamma_check : ∀ i < 128, cc 7 i = zeta ^ (2 * bitRev7 i + 1) := by
  unfold cc zeta; decide +kernel

/-- Before layer `k`, block `b` (of size `2^(8−k)`) represents
    `P mod (X^(2^(8−k)) − cc k b)`. -/
def CRTInv (k : ℕ) (P : Zq[X]) (g : Poly) : Prop :=
  ∀ b < 2 ^ k, (X ^ (2 * 2 ^ (7 - k)) - C (cc k b)) ∣
    P - blockPoly g (b * (2 * 2 ^ (7 - k))) (2 * 2 ^ (7 - k))

/-- One Cooley–Tukey butterfly layer splits `X^(2m) − z²` into
    `(X^m − z)(X^m + z)`. -/
theorem layer_crt_block {k : ℕ} (hk : k < 7) (P : Zq[X]) (g : Poly) {b : ℕ} (hb : b < 2 ^ k)
    (c : Zq) (hc : (zeta ^ bitRev7 (2 ^ k + b)) ^ 2 = c)
    (h : (X ^ (2 * 2 ^ (7 - k)) - C c) ∣ P - blockPoly g (b * (2 * 2 ^ (7 - k))) (2 * 2 ^ (7 - k))) :
    (X ^ 2 ^ (7 - k) - C (zeta ^ bitRev7 (2 ^ k + b))) ∣
        P - blockPoly (nttLayer k g) (b * (2 * 2 ^ (7 - k))) (2 ^ (7 - k)) ∧
      (X ^ 2 ^ (7 - k) + C (zeta ^ bitRev7 (2 ^ k + b))) ∣
        P - blockPoly (nttLayer k g) (b * (2 * 2 ^ (7 - k)) + 2 ^ (7 - k)) (2 ^ (7 - k)) := by
  have blk : ∀ r, r < 2 * 2 ^ (7 - k) → nttLayer k g (b * (2 * 2 ^ (7 - k)) + r) =
      if r < 2 ^ (7 - k) then
        g (b * (2 * 2 ^ (7 - k)) + r) +
          zeta ^ bitRev7 (2 ^ k + b) * g (b * (2 * 2 ^ (7 - k)) + r + 2 ^ (7 - k))
      else
        g (b * (2 * 2 ^ (7 - k)) + r - 2 ^ (7 - k)) -
          zeta ^ bitRev7 (2 ^ k + b) * g (b * (2 * 2 ^ (7 - k)) + r) :=
    fun r hr => nttLayer_block hk g hb hr
  generalize zeta ^ bitRev7 (2 ^ k + b) = z at *
  generalize 2 ^ (7 - k) = m at *
  generalize b * (2 * m) = base at *
  have e1 : blockPoly (nttLayer k g) base m =
      blockPoly g base m + C z * blockPoly g (base + m) m := by
    unfold blockPoly
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < m := Finset.mem_range.1 hj
    rw [blk j (by omega), ite_eq_left hj', show base + m + j = base + j + m by ring]
    simp only [map_add, map_mul]; ring
  have e2 : blockPoly (nttLayer k g) (base + m) m =
      blockPoly g base m - C z * blockPoly g (base + m) m := by
    unfold blockPoly
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < m := Finset.mem_range.1 hj
    rw [show base + m + j = base + (m + j) by ring, blk (m + j) (by omega),
      ite_eq_right (by omega), show base + (m + j) - m = base + j by omega]
    simp only [map_sub, map_mul]; ring
  have split := blockPoly_split g base m
  have hz2 : (X ^ m - C z) * (X ^ m + C z) = X ^ (2 * m) - C c := by
    rw [← hc, C_pow, pow_mul']; ring
  obtain ⟨qq, hq⟩ := h
  constructor
  · refine ⟨(X ^ m + C z) * qq + blockPoly g (base + m) m, ?_⟩
    rw [e1]
    linear_combination hq + split - qq * hz2
  · refine ⟨(X ^ m - C z) * qq + blockPoly g (base + m) m, ?_⟩
    rw [e2]
    linear_combination hq + split - qq * hz2

theorem crt_step {k : ℕ} (hk : k < 7) (P : Zq[X]) (g : Poly) (h : CRTInv k P g) :
    CRTInv (k + 1) P (nttLayer k g) := by
  intro b' hb'
  have hsize : 2 * 2 ^ (7 - (k + 1)) = 2 ^ (7 - k) := by
    rw [← pow_succ']; congr 1; omega
  rw [hsize]
  obtain ⟨b, rfl | rfl⟩ := Nat.even_or_odd' b'
  · have hb : b < 2 ^ k := by rw [pow_succ] at hb'; omega
    have := (layer_crt_block hk P g hb (cc k b) (zeta_sq_check k hk b hb) (h b hb)).1
    have hcc : cc (k + 1) (2 * b) = zeta ^ bitRev7 (2 ^ k + b) := by
      simp [cc, Nat.mul_div_cancel_left b (show 0 < 2 by norm_num)]
    rw [hcc, show 2 * b * 2 ^ (7 - k) = b * (2 * 2 ^ (7 - k)) by ring]
    exact this
  · have hb : b < 2 ^ k := by rw [pow_succ] at hb'; omega
    have := (layer_crt_block hk P g hb (cc k b) (zeta_sq_check k hk b hb) (h b hb)).2
    have hcc : cc (k + 1) (2 * b + 1) = -zeta ^ bitRev7 (2 ^ k + b) := by
      have h1 : (2 * b + 1) % 2 = 1 := by omega
      have h2 : (2 * b + 1) / 2 = b := by omega
      simp [cc, h1, h2]
    rw [hcc, show (2 * b + 1) * 2 ^ (7 - k) = b * (2 * 2 ^ (7 - k)) + 2 ^ (7 - k) by ring,
      map_neg, sub_neg_eq_add]
    exact this

theorem crt_layers {n : ℕ} (hn : n ≤ 7) (f : Poly) : CRTInv n (polyOf f) (nttLayers n f) := by
  induction n with
  | zero =>
    intro b hb
    have hb0 : b = 0 := by simpa using hb
    subst hb0
    simp [polyOf, nttLayers]
  | succ n ih =>
    rw [nttLayers_succ]
    exact crt_step (by omega) _ _ (ih (by omega))

/-- `γ_i = ζ^(2·BitRev7(i)+1)`, the roots of the quadratic factors. -/
def gamma (i : ℕ) : Zq := zeta ^ (2 * bitRev7 i + 1)

/-- **CRT characterisation of FIPS 203 Algorithm 9.** Output pair `i` of
    `NTT(f)` is `f mod (X² − γ_i)`. -/
theorem fipsNtt_crt (f : Poly) {i : ℕ} (hi : i < 128) :
    (X ^ 2 - C (gamma i)) ∣
      polyOf f - (C (fipsNtt f (2 * i)) + C (fipsNtt f (2 * i + 1)) * X) := by
  have h := crt_layers le_rfl f i (by norm_num; exact hi)
  rw [cc_gamma_check i hi] at h
  simp only [Nat.sub_self, pow_zero, mul_one] at h
  rw [blockPoly_two, ← fipsNtt_eq_layers, mul_comm i 2] at h
  exact h

/-! ## Uniqueness of remainders modulo `X² − γ` -/

theorem pair_unique (γ a b a' b' : Zq)
    (h : (X ^ 2 - C γ) ∣ (C a + C b * X) - (C a' + C b' * X)) : a = a' ∧ b = b' := by
  have hr : (C a + C b * X) - (C a' + C b' * X) = C (b - b') * X + C (a - a') := by
    simp only [map_sub]; ring
  rw [hr] at h
  by_cases h0 : C (b - b') * X + C (a - a') = 0
  · have c0 := congrArg (fun p => coeff p 0) h0
    have c1 := congrArg (fun p => coeff p 1) h0
    simp at c0 c1
    exact ⟨sub_eq_zero.1 c0, sub_eq_zero.1 c1⟩
  · exfalso
    have hdeg := Polynomial.degree_le_of_dvd h h0
    rw [degree_X_pow_sub_C (by norm_num)] at hdeg
    have := hdeg.trans degree_linear_le
    exact absurd this (by decide)

/-- `NTT(f)` is the unique array whose pair `i` is `f mod (X² − γ_i)`. -/
theorem fipsNtt_unique (f h : Poly)
    (hh : ∀ i < 128, (X ^ 2 - C (gamma i)) ∣ polyOf f - (C (h (2 * i)) + C (h (2 * i + 1)) * X)) :
    EqOn256 (fipsNtt f) h := by
  intro p hp
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' p
  all_goals
    have hi : i < 128 := by omega
    have hd : (X ^ 2 - C (gamma i)) ∣ (C (fipsNtt f (2 * i)) + C (fipsNtt f (2 * i + 1)) * X) -
        (C (h (2 * i)) + C (h (2 * i + 1)) * X) := by
      have := dvd_sub (hh i hi) (fipsNtt_crt f hi)
      rwa [sub_sub_sub_cancel_left] at this
    have := pair_unique _ _ _ _ _ hd
  · exact this.1
  · exact this.2

/-- `NTT` is additive. -/
theorem fipsNtt_add (f g : Poly) : EqOn256 (fipsNtt (f + g)) (fipsNtt f + fipsNtt g) := by
  apply fipsNtt_unique
  intro i hi
  have := dvd_add (fipsNtt_crt f hi) (fipsNtt_crt g hi)
  rw [polyOf_add]
  convert this using 1
  simp only [Pi.add_apply, map_add]; ring

/-! ## Multiplication -/

theorem fipsMultiplyNTTs_fold (f g : Poly) (n : ℕ) :
    let r := (List.range n).foldl (fipsMultiplyStep f g) (fun _ => 0)
    (∀ i < n, r (2 * i) = f (2 * i) * g (2 * i) + f (2 * i + 1) * g (2 * i + 1) * gamma i ∧
        r (2 * i + 1) = f (2 * i) * g (2 * i + 1) + f (2 * i + 1) * g (2 * i)) ∧
      (∀ p, 2 * n ≤ p → r p = 0) := by
  induction n with
  | zero => exact ⟨fun i hi => absurd hi (by omega), fun p _ => rfl⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨fun i hi => ?_, fun p hp => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · obtain ⟨a1, a2⟩ := ih1 i hi
        simp only [fipsMultiplyStep, Function.update_apply, fipsBaseCaseMultiply]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
        exact ⟨a1, a2⟩
      · simp [fipsMultiplyStep, fipsBaseCaseMultiply, gamma]
    · simp only [fipsMultiplyStep, Function.update_apply]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      exact ih2 p (by omega)

/-- FIPS 203 Algorithm 11 computes, for each `i < 128`, the product
    `(a₀ + a₁X)(b₀ + b₁X) mod (X² − γ_i)` (Algorithm 12). -/
theorem fipsMultiplyNTTs_pair (f g : Poly) {i : ℕ} (hi : i < 128) :
    fipsMultiplyNTTs f g (2 * i) =
        f (2 * i) * g (2 * i) + f (2 * i + 1) * g (2 * i + 1) * gamma i ∧
      fipsMultiplyNTTs f g (2 * i + 1) = f (2 * i) * g (2 * i + 1) + f (2 * i + 1) * g (2 * i) :=
  (fipsMultiplyNTTs_fold f g 128).1 i hi

theorem baseCase_crt (γ a0 a1 b0 b1 : Zq) :
    (C a0 + C a1 * X) * (C b0 + C b1 * X) -
        (C (a0 * b0 + a1 * b1 * γ) + C (a0 * b1 + a1 * b0) * X) =
      C (a1 * b1) * (X ^ 2 - C γ) := by
  simp only [map_add, map_mul]; ring

theorem gamma_pow_128 (i : ℕ) : gamma i ^ 128 = -1 := by
  unfold gamma
  rw [← pow_mul, show (2 * bitRev7 i + 1) * 128 = 128 * (2 * bitRev7 i + 1) by ring, pow_mul,
    zeta_pow_128, Odd.neg_one_pow ⟨bitRev7 i, rfl⟩]

/-- `x − y ∣ xⁿ − yⁿ` in `ℤ_q[X]` (stated with a variable exponent so that
    instances unify without unfolding `npow`). -/
theorem sub_dvd_pow_sub_pow_zq (x y : Zq[X]) (n : ℕ) : x - y ∣ x ^ n - y ^ n :=
  sub_dvd_pow_sub_pow _ _ n

/-- Each `X² − γ_i` divides `X^256 + 1`, since `γ_i^128 = −1`. -/
theorem gamma_dvd (i : ℕ) : (X ^ 2 - C (gamma i)) ∣ (X ^ 256 + 1 : Zq[X]) := by
  have e1 : ((X : Zq[X]) ^ 2) ^ 128 = X ^ 256 := (pow_mul X 2 128).symm
  have e2 : (C (gamma i)) ^ 128 = -1 := by rw [← C_pow, gamma_pow_128, map_neg, map_one]
  have e : (X ^ 256 + 1 : Zq[X]) = (X ^ 2) ^ 128 - (C (gamma i)) ^ 128 := by
    rw [e1, e2]; ring
  rw [e]; exact sub_dvd_pow_sub_pow_zq _ _ _

/-- `NTT` is multiplicative: if `h ≡ f·g` in `R_q` then
    `NTT(h) = MultiplyNTTs(NTT(f), NTT(g))`. -/
theorem fipsNtt_mulNTT (f g h : Poly) (hh : (X ^ 256 + 1 : Zq[X]) ∣ polyOf f * polyOf g - polyOf h) :
    EqOn256 (fipsNtt h) (fipsMultiplyNTTs (fipsNtt f) (fipsNtt g)) := by
  apply fipsNtt_unique
  intro i hi
  obtain ⟨m0, m1⟩ := fipsMultiplyNTTs_pair (fipsNtt f) (fipsNtt g) hi
  rw [m0, m1]
  have hf := fipsNtt_crt f hi
  have hg := fipsNtt_crt g hi
  have hΦ := (gamma_dvd i).trans hh
  have hb := baseCase_crt (gamma i) (fipsNtt f (2 * i)) (fipsNtt f (2 * i + 1))
    (fipsNtt g (2 * i)) (fipsNtt g (2 * i + 1))
  obtain ⟨u, hu⟩ := hf
  obtain ⟨v, hv⟩ := hg
  obtain ⟨w, hw⟩ := hΦ
  refine ⟨u * polyOf g + (C (fipsNtt f (2 * i)) + C (fipsNtt f (2 * i + 1)) * X) * v
    + C (fipsNtt f (2 * i + 1) * fipsNtt g (2 * i + 1)) - w, ?_⟩
  linear_combination (polyOf g) * hu +
    (C (fipsNtt f (2 * i)) + C (fipsNtt f (2 * i + 1)) * X) * hv + hb - hw

/-- The reduced product `(f·g) mod (X^256 + 1)` as an array. -/
noncomputable def mulRq (f g : Poly) : Poly :=
  fun k => ((polyOf f * polyOf g) %ₘ (X ^ 256 + 1)).coeff k

theorem monic_X_pow_add_one_zq {n : ℕ} (hn : n ≠ 0) : (X ^ n + 1 : Zq[X]).Monic := by
  have := monic_X_pow_add_C (1 : Zq) hn
  rwa [C_1] at this

theorem monic_Phi : (X ^ 256 + 1 : Zq[X]).Monic := monic_X_pow_add_one_zq (by norm_num)

/-- Degree bound for reduction modulo `Xⁿ + 1` (variable exponent, see
    `sub_dvd_pow_sub_pow_zq`). -/
theorem degree_modByMonic_X_pow_add_one_lt (p : Zq[X]) {n : ℕ} (hn : 0 < n) :
    (p %ₘ (X ^ n + 1)).degree < (n : WithBot ℕ) := by
  have h2 : (X ^ n + 1 : Zq[X]).degree = (n : WithBot ℕ) := by
    rw [← C_1]; exact degree_X_pow_add_C hn 1
  exact lt_of_lt_of_eq (degree_modByMonic_lt p (monic_X_pow_add_one_zq hn.ne')) h2

theorem polyOf_mulRq (f g : Poly) :
    polyOf (mulRq f g) = (polyOf f * polyOf g) %ₘ (X ^ 256 + 1) := by
  set R := (polyOf f * polyOf g) %ₘ (X ^ 256 + 1)
  have hdeg : R.degree < ((256 : ℕ) : WithBot ℕ) :=
    degree_modByMonic_X_pow_add_one_lt _ (by norm_num)
  have hnat : R.natDegree < 256 := by
    by_cases h0 : R = 0
    · rw [h0]; simp
    · exact (natDegree_lt_iff_degree_lt h0).2 hdeg
  conv_rhs => rw [as_sum_range' R 256 hnat]
  unfold polyOf blockPoly mulRq
  apply Finset.sum_congr rfl
  intro j _
  rw [zero_add, C_mul_X_pow_eq_monomial]

theorem dvd_sub_mulRq (f g : Poly) :
    (X ^ 256 + 1 : Zq[X]) ∣ polyOf f * polyOf g - polyOf (mulRq f g) := by
  rw [polyOf_mulRq]
  refine ⟨(polyOf f * polyOf g) /ₘ (X ^ 256 + 1), ?_⟩
  have := modByMonic_add_div (polyOf f * polyOf g) (X ^ 256 + 1 : Zq[X])
  linear_combination -this

/-- **Correctness of NTT-domain multiplication** (FIPS 203 §4.3.1):
    `NTT⁻¹(MultiplyNTTs(NTT(f), NTT(g)))` is the product `f·g` in
    `R_q = ℤ_q[X]/(X^256 + 1)`, reduced to degree `< 256`. -/
theorem fipsNttInv_multiplyNTTs (f g : Poly) :
    polyOf (fipsNttInv (fipsMultiplyNTTs (fipsNtt f) (fipsNtt g))) =
      (polyOf f * polyOf g) %ₘ (X ^ 256 + 1) := by
  rw [← polyOf_mulRq]
  apply polyOf_congr
  intro p hp
  have h1 := fipsNtt_mulNTT f g (mulRq f g) (dvd_sub_mulRq f g)
  rw [fipsNttInv_congr (fun p hp => (h1 p hp).symm) p hp, fipsNttInv_fipsNtt _ p hp]

/-- Multiplication in `R_q = ℤ_q[X]/(X^256 + 1)` on reduced representatives. -/
noncomputable def rqMul (P Q : Zq[X]) : Zq[X] := (P * Q) %ₘ (X ^ 256 + 1)

theorem fipsNttInv_multiplyNTTs_rqMul (f g : Poly) :
    polyOf (fipsNttInv (fipsMultiplyNTTs (fipsNtt f) (fipsNtt g))) =
      rqMul (polyOf f) (polyOf g) :=
  fipsNttInv_multiplyNTTs f g

theorem fipsNttInv_multiplyNTTs_dvd (f g : Poly) :
    (X ^ 256 + 1 : Zq[X]) ∣
      polyOf f * polyOf g - polyOf (fipsNttInv (fipsMultiplyNTTs (fipsNtt f) (fipsNtt g))) := by
  rw [fipsNttInv_multiplyNTTs, ← polyOf_mulRq]; exact dvd_sub_mulRq f g

end OcamlPq.MLKEM
