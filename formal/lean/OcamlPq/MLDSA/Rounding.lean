import OcamlPq.MLDSA.Arith

/-!
# ML-DSA rounding: Power2Round, Decompose, HighBits/LowBits, hints

Models of `power2round`, `decompose`, `use_hint` and `make_hint`
(mldsa/mldsa_engine.ml:426–450) and transcriptions of FIPS 204
Algorithms 35–40, with proofs that they agree.

`Decompose` and the hint functions are proved for the two values of `γ2`
used by the library: `(q-1)/88 = 95232` (ML-DSA-44) and
`(q-1)/32 = 261888` (ML-DSA-65/87).
-/

namespace OcamlPq.MLDSA

/-- The dropped-bits parameter `d = 13` (FIPS 204 Table 1;
    mldsa/mldsa_engine.ml:113). -/
def d : ℕ := 13

/-- The two admissible values of `γ2` (FIPS 204 Table 1). -/
def Gamma2Ok (γ2 : ℤ) : Prop := γ2 = 95232 ∨ γ2 = 261888

theorem gamma2_44 : (8380417 - 1) / 88 = (95232 : ℤ) := by norm_num
theorem gamma2_65 : (8380417 - 1) / 32 = (261888 : ℤ) := by norm_num

/-! ## Specification (FIPS 204 §2.3 and §7.4) -/

/-- `m mod± α` (FIPS 204 §2.3): the representative of `m` modulo `α` in
    `(-α/2, α/2]` for even `α`, and in `[-(α-1)/2, (α-1)/2]` for odd `α`. -/
def modPM (m α : ℤ) : ℤ := if m % α > α / 2 then m % α - α else m % α

/-- `modPM` is the representative required by FIPS 204 §2.3 (even `α`). -/
theorem modPM_spec_even (m α : ℤ) (hα : 0 < α) (he : α % 2 = 0) :
    -(α / 2) < modPM m α ∧ modPM m α ≤ α / 2 ∧ (m - modPM m α) % α = 0 := by
  unfold modPM
  have h0 := Int.emod_nonneg m hα.ne'
  have h1 := Int.emod_lt_of_pos m hα
  have h2 := Int.emod_add_ediv_mul m α
  have h3 : α / 2 * 2 = α := by omega
  split_ifs with h
  · refine ⟨by omega, by omega, ?_⟩
    rw [show m - (m % α - α) = (m / α + 1) * α by rw [add_mul]; linarith]
    exact Int.mul_emod_left _ _
  · refine ⟨by omega, by omega, ?_⟩
    rw [show m - m % α = (m / α) * α by linarith]
    exact Int.mul_emod_left _ _

/-- The infinity norm of one coefficient `w ∈ ℤ_q`: `|w mod± q|`
    (FIPS 204 §2.3). -/
def coeffNorm (w : ℤ) : ℤ := |modPM w q|

/-- FIPS 204 Algorithm 35, `Power2Round(r)`. -/
def power2RoundSpec (r : ℤ) : ℤ × ℤ :=
  let rp := r % q
  let r0 := modPM rp (2 ^ d)
  ((rp - r0) / 2 ^ d, r0)

/-- FIPS 204 Algorithm 36, `Decompose(r)`. -/
def decomposeSpec (γ2 r : ℤ) : ℤ × ℤ :=
  let rp := r % q
  let r0 := modPM rp (2 * γ2)
  if rp - r0 = q - 1 then (0, r0 - 1) else ((rp - r0) / (2 * γ2), r0)

/-- FIPS 204 Algorithm 37, `HighBits(r)`. -/
def highBits (γ2 r : ℤ) : ℤ := (decomposeSpec γ2 r).1

/-- FIPS 204 Algorithm 38, `LowBits(r)`. -/
def lowBits (γ2 r : ℤ) : ℤ := (decomposeSpec γ2 r).2

/-- FIPS 204 Algorithm 39, `MakeHint(z, r)` (as `0`/`1`); `r + z` is taken
    in `ℤ_q`, which `decomposeSpec` does by reducing modulo `q`. -/
def makeHintSpec (γ2 z r : ℤ) : ℤ := if highBits γ2 r ≠ highBits γ2 (r + z) then 1 else 0

/-- FIPS 204 Algorithm 40, `UseHint(h, r)`. -/
def useHintSpec (γ2 h r : ℤ) : ℤ :=
  let m := (q - 1) / (2 * γ2)
  let r1 := (decomposeSpec γ2 r).1
  let r0 := (decomposeSpec γ2 r).2
  if h = 1 ∧ r0 > 0 then (r1 + 1) % m
  else if h = 1 ∧ r0 ≤ 0 then (r1 - 1) % m
  else r1

/-! ## Models -/

/-- Model of `power2round` (mldsa/mldsa_engine.ml:426–429):
    `let value = norm value in
     let high = (value + (1 lsl (d - 1)) - 1) lsr d in
     high, value - (high lsl d)`.
    `lsr d` is applied to a non-negative `int` (see
    `power2round_portable`), where it is floor division by `2^d`; `lsl d` of
    the small non-negative `high` is multiplication by `2^d`. -/
def power2round (value : ℤ) : ℤ × ℤ :=
  let value := norm value
  let high := (value + 2 ^ (d - 1) - 1) / 2 ^ d
  (high, value - high * 2 ^ d)

/-- Model of `decompose` (mldsa/mldsa_engine.ml:431–436). -/
def decompose (γ2 value : ℤ) : ℤ × ℤ :=
  let value := norm value
  let alpha := 2 * γ2
  let modulus := ocamlDiv (q - 1) alpha
  let high := ocamlDiv (value + ocamlDiv alpha 2 - 1) alpha
  if high = modulus then (0, value - q) else (high, value - high * alpha)

/-- Model of `use_hint` (mldsa/mldsa_engine.ml:438–443). -/
def useHint (γ2 value hint : ℤ) : ℤ :=
  let high := (decompose γ2 value).1
  let low := (decompose γ2 value).2
  if hint = 0 then high
  else
    let modulus := ocamlDiv (q - 1) (2 * γ2)
    if low > 0 then ocamlMod (high + 1) modulus
    else ocamlMod (high + modulus - 1) modulus

/-- Model of `make_hint` (mldsa/mldsa_engine.ml:446–450), the
    reference-implementation form of the hint. -/
def makeHint (γ2 low high : ℤ) : ℤ :=
  if low > γ2 ∨ low < -γ2 ∨ (low = -γ2 ∧ high ≠ 0) then 1 else 0

/-! ## Power2Round -/

theorem power2round_eq_spec (r : ℤ) : power2round r = power2RoundSpec r := by
  unfold power2round power2RoundSpec modPM
  rw [norm_eq]
  simp only [d, q]
  norm_num
  split_ifs <;> omega

/-- `Power2Round` outputs: `r1 ∈ [0, 2^10)`, `r0 ∈ (-2^12, 2^12]`, and
    `r ≡ r1·2^13 + r0 (mod q)`. -/
theorem power2round_range (r : ℤ) :
    0 ≤ (power2round r).1 ∧ (power2round r).1 < 2 ^ 10 ∧
    -(2 ^ 12) < (power2round r).2 ∧ (power2round r).2 ≤ 2 ^ 12 ∧
    (power2round r).1 * 2 ^ 13 + (power2round r).2 = r % q := by
  unfold power2round
  rw [norm_eq]
  simp only [d, q]
  norm_num
  omega

/-- Every `int` intermediate of `power2round` is portable, and the operand
    of `lsr` is non-negative (so `lsr` is floor division). -/
theorem power2round_portable (r : ℤ) :
    0 ≤ norm r + 2 ^ (d - 1) - 1 ∧ Portable (norm r + 2 ^ (d - 1) - 1) ∧
    Portable ((power2round r).1 * 2 ^ d) ∧ Portable (power2round r).1 ∧
    Portable (power2round r).2 := by
  have h0 := norm_nonneg r
  have h1 := norm_lt r
  unfold power2round
  simp only [d, q, Portable] at *
  norm_num
  omega

/-! ## Decompose -/

/-- `decompose` with OCaml's truncating `/` replaced by floor division
    (all dividends are non-negative). -/
theorem decompose_eq_floor {γ2 : ℤ} (hγ : 0 < γ2) (r : ℤ) :
    decompose γ2 r =
      if (r % q + γ2 - 1) / (2 * γ2) = (q - 1) / (2 * γ2) then (0, r % q - q)
      else ((r % q + γ2 - 1) / (2 * γ2), r % q - (r % q + γ2 - 1) / (2 * γ2) * (2 * γ2)) := by
  have h0 : 0 ≤ r % q := Int.emod_nonneg _ (by decide)
  have e1 : ocamlDiv (2 * γ2) 2 = γ2 := by rw [ocamlDiv_of_nonneg (by omega)]; omega
  have e2 : ocamlDiv (q - 1) (2 * γ2) = (q - 1) / (2 * γ2) :=
    ocamlDiv_of_nonneg (by simp [q])
  have e3 : ocamlDiv (r % q + γ2 - 1) (2 * γ2) = (r % q + γ2 - 1) / (2 * γ2) :=
    ocamlDiv_of_nonneg (by omega)
  unfold decompose
  simp only [norm_eq, e1, e2, e3]

theorem Gamma2Ok.pos {γ2 : ℤ} (hγ : Gamma2Ok γ2) : 0 < γ2 := by
  rcases hγ with rfl | rfl <;> norm_num

theorem decompose_eq_spec {γ2 : ℤ} (hγ : Gamma2Ok γ2) (r : ℤ) :
    decompose γ2 r = decomposeSpec γ2 r := by
  rw [decompose_eq_floor hγ.pos]
  unfold decomposeSpec modPM
  have h0 : 0 ≤ r % q := Int.emod_nonneg _ (by decide)
  rcases hγ with rfl | rfl <;>
  · simp only [q] at *
    norm_num
    split_ifs <;> (try simp only [Prod.mk.injEq, true_and]) <;> omega

/-- Range and reconstruction facts for `Decompose` (FIPS 204 §7.4):
    `r1 ∈ [0, m)` with `m = (q-1)/(2γ2)`, `r0 ∈ [-γ2, γ2]`, and
    `r ≡ r1·2γ2 + r0 (mod q)`. -/
theorem decomposeSpec_range {γ2 : ℤ} (hγ : Gamma2Ok γ2) (r : ℤ) :
    0 ≤ (decomposeSpec γ2 r).1 ∧ (decomposeSpec γ2 r).1 < (q - 1) / (2 * γ2) ∧
    -γ2 ≤ (decomposeSpec γ2 r).2 ∧ (decomposeSpec γ2 r).2 ≤ γ2 ∧
    ((decomposeSpec γ2 r).1 * (2 * γ2) + (decomposeSpec γ2 r).2 - r) % q = 0 := by
  unfold decomposeSpec modPM
  rcases hγ with rfl | rfl <;>
  · simp only [q]
    norm_num
    split_ifs <;> simp only <;> omega

/-- Every `int` intermediate of `decompose` is portable. -/
theorem decompose_portable {γ2 : ℤ} (hγ : Gamma2Ok γ2) (r : ℤ) :
    Portable (2 * γ2) ∧ Portable (norm r + γ2 - 1) ∧
    Portable (ocamlDiv (norm r + ocamlDiv (2 * γ2) 2 - 1) (2 * γ2)) ∧
    Portable (ocamlDiv (norm r + ocamlDiv (2 * γ2) 2 - 1) (2 * γ2) * (2 * γ2)) ∧
    Portable (norm r - q) ∧ Portable (decompose γ2 r).1 ∧ Portable (decompose γ2 r).2 := by
  have h0 := norm_nonneg r
  have h1 := norm_lt r
  have e1 : ocamlDiv (2 * γ2) 2 = γ2 := by rw [ocamlDiv_of_nonneg (by linarith [hγ.pos])]; omega
  have e3 : ocamlDiv (norm r + γ2 - 1) (2 * γ2) = (norm r + γ2 - 1) / (2 * γ2) :=
    ocamlDiv_of_nonneg (by linarith [hγ.pos])
  rw [decompose_eq_floor hγ.pos, e1, e3, ← norm_eq]
  rcases hγ with rfl | rfl <;>
  · simp only [q, Portable] at *
    norm_num
    split_ifs <;> simp only <;> omega

/-! ## UseHint -/

theorem useHint_eq_spec {γ2 : ℤ} (hγ : Gamma2Ok γ2) (r h : ℤ) (hh : h = 0 ∨ h = 1) :
    useHint γ2 r h = useHintSpec γ2 h r := by
  have hd := decompose_eq_spec hγ r
  have hr := decomposeSpec_range hγ r
  have hm : 0 < (q - 1) / (2 * γ2) := by rcases hγ with rfl | rfl <;> simp [q]
  have e2 : ocamlDiv (q - 1) (2 * γ2) = (q - 1) / (2 * γ2) :=
    ocamlDiv_of_nonneg (by simp [q])
  unfold useHint useHintSpec
  simp only [hd, e2, ocamlMod_pos_eq _ _ hm]
  rcases hγ with rfl | rfl <;>
  · simp only [q] at *
    norm_num at *
    rcases hh with rfl | rfl
    · simp
    · norm_num
      split_ifs <;> omega

/-- `useHint` depends only on its input modulo `q`. -/
theorem decomposeSpec_emod (γ2 r : ℤ) : decomposeSpec γ2 (r % q) = decomposeSpec γ2 r := by
  unfold decomposeSpec; rw [Int.emod_emod_of_dvd _ (dvd_refl q)]

theorem decomposeSpec_congr (γ2 r s : ℤ) (h : r % q = s % q) :
    decomposeSpec γ2 r = decomposeSpec γ2 s := by
  rw [← decomposeSpec_emod, h, decomposeSpec_emod]

/-- Every `int` intermediate of `use_hint` is portable. -/
theorem useHint_portable {γ2 : ℤ} (hγ : Gamma2Ok γ2) (r : ℤ) :
    Portable ((decompose γ2 r).1 + 1) ∧
    Portable ((decompose γ2 r).1 + ocamlDiv (q - 1) (2 * γ2) - 1) := by
  have hd := decompose_eq_spec hγ r
  have hr := decomposeSpec_range hγ r
  rw [hd]
  rcases hγ with rfl | rfl <;>
  · simp only [q, Portable] at *
    rw [ocamlDiv_of_nonneg (by norm_num)]
    norm_num at *
    omega

/-! ## Case analysis of Decompose -/

/-- The two shapes of `Decompose(r)` (FIPS 204 Algorithm 36), with
    `v = r mod q`: the corner case `v ≥ q - γ2` gives `(0, v - q)`;
    otherwise `v = r1·2γ2 + r0` with `r1 ∈ [0, m)` and `r0 ∈ (-γ2, γ2]`. -/
theorem decomposeSpec_cases {γ2 : ℤ} (hγ : Gamma2Ok γ2) (r : ℤ) :
    ∃ r1 r0, decomposeSpec γ2 r = (r1, r0) ∧
      ((q - γ2 ≤ r % q ∧ r1 = 0 ∧ r0 = r % q - q) ∨
       (r % q < q - γ2 ∧ 0 ≤ r1 ∧ r1 < (q - 1) / (2 * γ2) ∧
          r0 = r % q - r1 * (2 * γ2) ∧ -γ2 < r0 ∧ r0 ≤ γ2)) := by
  unfold decomposeSpec modPM
  rcases hγ with rfl | rfl <;>
  · simp only [q]
    norm_num
    split_ifs <;> refine ⟨_, _, rfl, ?_⟩ <;> omega

/-- Reduction modulo `q` of a value in `[-q, 2q)`: at most one correction. -/
theorem emod_q_cases (w : ℤ) (h0 : -q ≤ w) (h1 : w < 2 * q) :
    (w < 0 ∧ w % q = w + q) ∨ (0 ≤ w ∧ w < q ∧ w % q = w) ∨ (q ≤ w ∧ w % q = w - q) := by
  simp only [q] at *
  omega

/-! ## UseHint correctness (FIPS 204 §7.4, Lemma on hints) -/

/-- The hint lemma behind ML-DSA verification: for `‖z‖∞ ≤ γ2` and any
    `r`, `UseHint(MakeHint(z, r), r) = HighBits(r + z)`. -/
theorem useHint_makeHint {γ2 : ℤ} (hγ : Gamma2Ok γ2) (r z : ℤ)
    (hz0 : -γ2 ≤ z) (hz1 : z ≤ γ2) :
    useHintSpec γ2 (makeHintSpec γ2 z r) r = highBits γ2 (r + z) := by
  obtain ⟨a1, a0, ha, hca⟩ := decomposeSpec_cases hγ r
  obtain ⟨b1, b0, hb, hcb⟩ := decomposeSpec_cases hγ (r + z)
  unfold useHintSpec makeHintSpec highBits
  rw [ha, hb]
  simp only
  have hv0 : 0 ≤ r % q := Int.emod_nonneg _ (by decide)
  have hv1 : r % q < q := Int.emod_lt_of_pos _ q_pos
  rw [← Int.emod_add_emod] at hcb
  generalize r % q = v at *
  have hγ' := hγ
  rcases hγ' with rfl | rfl <;>
    rcases emod_q_cases (v + z) (by simp only [q] at *; omega) (by simp only [q] at *; omega) with
      ⟨_, hw⟩ | ⟨_, _, hw⟩ | ⟨_, hw⟩ <;> rw [hw] at hcb
  all_goals
    simp only [q] at *
    norm_num at *
    split_ifs <;> omega

/-! ## MakeHint: reference form versus Algorithm 39 -/

/-- The reference-implementation hint agrees with FIPS 204 MakeHint: for any
    `v` with `(v1, v0) = Decompose(v)` and any `u` with `|v0 + u| ≤ 2γ2`,
    `make_hint (v0 + u) v1 = MakeHint(-u, v + u)`. -/
theorem makeHint_eq_spec {γ2 : ℤ} (hγ : Gamma2Ok γ2) (v u : ℤ)
    (h0 : -(2 * γ2) ≤ lowBits γ2 v + u) (h1 : lowBits γ2 v + u ≤ 2 * γ2) :
    makeHint γ2 (lowBits γ2 v + u) (highBits γ2 v) = makeHintSpec γ2 (-u) (v + u) := by
  have hvu : v + u + -u = v := by ring
  unfold makeHintSpec
  rw [hvu]
  obtain ⟨a1, a0, ha, hca⟩ := decomposeSpec_cases hγ v
  obtain ⟨b1, b0, hb, hcb⟩ := decomposeSpec_cases hγ (v + u)
  unfold makeHint highBits lowBits at *
  rw [ha] at h0 h1 ⊢
  rw [hb]
  simp only at h0 h1 ⊢
  have hv0 : 0 ≤ v % q := Int.emod_nonneg _ (by decide)
  have hv1 : v % q < q := Int.emod_lt_of_pos _ q_pos
  rw [← Int.emod_add_emod] at hcb
  generalize v % q = x at *
  have hγ' := hγ
  rcases hγ' with rfl | rfl <;>
    rcases emod_q_cases (x + u) (by simp only [q] at *; omega) (by simp only [q] at *; omega) with
      ⟨_, hw⟩ | ⟨_, _, hw⟩ | ⟨_, hw⟩ <;> rw [hw] at hcb
  all_goals
    simp only [q] at *
    norm_num at *
    split_ifs <;> omega

end OcamlPq.MLDSA
