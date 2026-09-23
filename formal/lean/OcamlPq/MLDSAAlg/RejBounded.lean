import OcamlPq.MLDSAAlg.RejNTT
import OcamlPq.MLDSAAlg.Restart

/-!
# `eta_polynomial` refines RejBoundedPoly (FIPS 204 Algorithms 15 and 31)

The OCaml sampler squeezes 272 bytes of SHAKE256, feeds each byte's low
nibble and then its high nibble to `accept`, and restarts with twice the
output length if fewer than 256 coefficients were accepted.

For η = 4 (ML-DSA-65) the restart is not rare: 544 nibbles, each accepted
with probability 9/16, fall short of 256 accepted values with probability
about 7.0·10⁻⁶ per polynomial, i.e. about once in 13 000 ML-DSA-65 key
generations (11 polynomials each), so test vectors are unlikely to reach it.
The theorems below prove that the restart path returns the FIPS output
(and this was also confirmed on concrete seeds against an independent
Python implementation; see the report).
-/

namespace OcamlPq.MLDSAAlg

/-! ## Specification -/

/-- FIPS 204 Algorithm 15, `CoeffFromHalfByte(b)`; `none` is `⊥`. -/
def coeffFromHalfByte (eta b : ℕ) : Option ℤ :=
  if eta = 2 ∧ b < 15 then some (2 - ((b % 5 : ℕ) : ℤ))
  else if eta = 4 ∧ b < 9 then some (4 - (b : ℤ))
  else none

/-- The body of the `while j < 256` loop of FIPS 204 Algorithm 31
    (lines 5–13) after squeezing the byte `z`. -/
def rejBoundedBody (eta : ℕ) (st : ℕ × Poly) (z : ℕ) : ℕ × Poly :=
  let z0 := coeffFromHalfByte eta (z % 16)
  let z1 := coeffFromHalfByte eta (z / 16)
  let st := match z0 with
    | some v => (st.1 + 1, Function.update st.2 st.1 v)
    | none => st
  match z1 with
  | some v => if st.1 < 256 then (st.1 + 1, Function.update st.2 st.1 v) else st
  | none => st

/-- FIPS 204 Algorithm 31, `RejBoundedPoly(ρ)`, on the SHAKE256 stream `s` of
    `ρ`, for at most `fuel` iterations; the XOF context is the position
    `pos`. -/
def rejBoundedLoop (eta : ℕ) (s : ℕ → Byte) : ℕ → ℕ → ℕ × Poly → Option Poly
  | 0, _, _ => none
  | fuel + 1, pos, st =>
    if st.1 < 256 then rejBoundedLoop eta s fuel (pos + 1) (rejBoundedBody eta st (s pos).val)
    else some st.2

/-- FIPS 204 Algorithm 31 on the stream `s` terminates with output `a`. -/
def RejBoundedReturns (eta : ℕ) (s : ℕ → Byte) (a : Poly) : Prop :=
  ∃ fuel, rejBoundedLoop eta s fuel 0 (0, fun _ => 0) = some a

/-! ## Model of the OCaml code -/

/-- The `accept` closure of `eta_polynomial` (`mldsa_engine.ml`,
    lines 356–367), acting on `(!count, coefficients)`. -/
def etaAccept (eta : ℕ) (st : ℕ × Poly) (value : ℕ) : ℕ × Poly :=
  let (count, coefficients) := st
  if count < n then
    if eta = 2 then
      if value < 15 then
        let reduced : ℤ := (value : ℤ) - (((205 * value) >>> 10 : ℕ) : ℤ) * 5
        (count + 1, Function.update coefficients count (2 - reduced))
      else (count, coefficients)
    else if value < 9 then
      (count + 1, Function.update coefficients count (4 - (value : ℤ)))
    else (count, coefficients)
  else (count, coefficients)

/-- The `for` loop body of `eta_polynomial` (lines 369–372). -/
def etaByte (eta : ℕ) (st : ℕ × Poly) (byte : ℕ) : ℕ × Poly :=
  etaAccept eta (etaAccept eta st (byte &&& 0x0f)) (byte >>> 4)

/-- The `for position = 0 to String.length stream - 1` loop of
    `eta_polynomial` (lines 369–372). -/
def etaScan (eta : ℕ) (stream : Bytes) : ℕ × Poly :=
  (List.range stream.length).foldl
    (fun st position => etaByte eta st (getU8 stream position)) (0, fun _ => 0)

/-- `eta_polynomial seed nonce output_length` (`mldsa_engine.ml`,
    lines 351–375); `calls` bounds the number of (re)starts. -/
def etaPolynomial (eta : ℕ) (shake256 : XOF) (seed : Bytes) (nonce : ℕ) :
    (calls : ℕ) → (outputLength : ℕ) → Option Poly
  | 0, _ => none
  | calls + 1, outputLength =>
    let stream := shake256.squeeze (seed ++ u16le nonce) outputLength
    let r := etaScan eta stream
    if r.1 = n then some r.2
    else etaPolynomial eta shake256 seed nonce calls (2 * outputLength)

/-- The OCaml call `eta_polynomial seed nonce output_length` returns `p`. -/
def EtaReturns (eta : ℕ) (shake256 : XOF) (seed : Bytes) (nonce outputLength : ℕ)
    (p : Poly) : Prop :=
  ∃ calls, etaPolynomial eta shake256 seed nonce calls outputLength = some p

/-! ## Arithmetic -/

/-- **`value − ((205·value) lsr 10)·5 = value mod 5` for `value < 15`**
    (checked for all 15 values by the kernel). -/
theorem reduced_eq_mod5 : ∀ v : ℕ, v < 15 → v - ((205 * v) >>> 10) * 5 = v % 5 ∧
    ((205 * v) >>> 10) * 5 ≤ v := by
  decide

theorem land_0x0f (x : ℕ) : x &&& 0x0f = x % 16 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 4; norm_num at this; exact this

theorem lsr_4 (x : ℕ) : x >>> 4 = x / 16 := by rw [Nat.shiftRight_eq_div_pow]

/-- `accept` is "store CoeffFromHalfByte(value) if not ⊥ and there is room". -/
theorem etaAccept_eq (eta : ℕ) (heta : eta = 2 ∨ eta = 4) (st : ℕ × Poly) (value : ℕ) :
    etaAccept eta st value =
      if st.1 < 256 then
        match coeffFromHalfByte eta value with
        | some v => (st.1 + 1, Function.update st.2 st.1 v)
        | none => st
      else st := by
  obtain ⟨count, a⟩ := st
  unfold etaAccept coeffFromHalfByte
  simp only [n]
  rcases heta with rfl | rfl
  · by_cases hc : count < 256
    · by_cases hv : value < 15
      · obtain ⟨h1, h2⟩ := reduced_eq_mod5 value hv
        generalize (205 * value) >>> 10 = t at h1 h2 ⊢
        have e : (2 : ℤ) - ((value : ℤ) - (t : ℤ) * 5) = 2 - ((value % 5 : ℕ) : ℤ) := by omega
        simp [hc, hv, e]
      · simp [hc, hv]
    · simp [hc]
  · by_cases hc : count < 256 <;> by_cases hv : value < 9 <;> simp [hc, hv]

/-- One OCaml loop iteration equals one FIPS 204 loop body when `j < 256`. -/
theorem etaByte_eq_body (eta : ℕ) (heta : eta = 2 ∨ eta = 4) (st : ℕ × Poly) (z : ℕ)
    (hj : st.1 < 256) : etaByte eta st z = rejBoundedBody eta st z := by
  unfold etaByte rejBoundedBody
  rw [land_0x0f, lsr_4, etaAccept_eq eta heta, etaAccept_eq eta heta, ite_eq_left hj]
  cases coeffFromHalfByte eta (z % 16) <;> cases coeffFromHalfByte eta (z / 16) <;> simp

/-- Once 256 coefficients have been collected, further bytes change nothing. -/
theorem etaByte_full (eta : ℕ) (heta : eta = 2 ∨ eta = 4) (st : ℕ × Poly) (z : ℕ)
    (hj : 256 ≤ st.1) : etaByte eta st z = st := by
  unfold etaByte
  have h1 : etaAccept eta st (z &&& 0x0f) = st := by
    rw [etaAccept_eq eta heta, ite_eq_right (by omega)]
  rw [h1, etaAccept_eq eta heta, ite_eq_right (by omega)]

theorem etaAccept_le (eta : ℕ) (heta : eta = 2 ∨ eta = 4) (st : ℕ × Poly) (v : ℕ)
    (hj : st.1 ≤ 256) : st.1 ≤ (etaAccept eta st v).1 ∧ (etaAccept eta st v).1 ≤ 256 := by
  rw [etaAccept_eq eta heta]
  split_ifs with h1
  · cases coeffFromHalfByte eta v <;> simp <;> omega
  · simp [hj]

theorem etaByte_le (eta : ℕ) (heta : eta = 2 ∨ eta = 4) (st : ℕ × Poly) (z : ℕ)
    (hj : st.1 ≤ 256) : st.1 ≤ (etaByte eta st z).1 ∧ (etaByte eta st z).1 ≤ 256 := by
  unfold etaByte
  have h1 := etaAccept_le eta heta st (z &&& 0x0f) hj
  have h2 := etaAccept_le eta heta _ (z >>> 4) h1.2
  omega

/-! ## Loop correspondence on the infinite stream -/

/-- The OCaml `for` loop state after the first `m` bytes of the stream `s`. -/
def etaState (eta : ℕ) (s : ℕ → Byte) (m : ℕ) : ℕ × Poly :=
  (List.range m).foldl (fun st position => etaByte eta st (s position).val) (0, fun _ => 0)

@[simp] theorem etaState_zero (eta : ℕ) (s : ℕ → Byte) :
    etaState eta s 0 = (0, fun _ => 0) := rfl

theorem etaState_succ (eta : ℕ) (s : ℕ → Byte) (m : ℕ) :
    etaState eta s (m + 1) = etaByte eta (etaState eta s m) (s m).val := by
  simp [etaState, List.range_succ, List.foldl_append]

theorem etaScan_squeeze (eta : ℕ) (H : XOF) (x : Bytes) (L : ℕ) :
    etaScan eta (H.squeeze x L) = etaState eta (H x) L := by
  unfold etaScan etaState
  rw [XOF.length_squeeze]
  apply List.foldl_ext
  intro st pos hpos
  rw [getU8_squeeze (List.mem_range.mp hpos)]

theorem etaState_le (eta : ℕ) (heta : eta = 2 ∨ eta = 4) (s : ℕ → Byte) (m : ℕ) :
    (etaState eta s m).1 ≤ 256 := by
  induction m with
  | zero => simp [etaState]
  | succ m ih => rw [etaState_succ]; exact (etaByte_le eta heta _ _ ih).2

theorem etaState_stable (eta : ℕ) (heta : eta = 2 ∨ eta = 4) (s : ℕ → Byte) {m m' : ℕ}
    (hm : m ≤ m') (h : (etaState eta s m).1 = 256) : etaState eta s m' = etaState eta s m := by
  induction hm with
  | refl => rfl
  | step _ ih => rw [etaState_succ, ih, etaByte_full eta heta _ _ (by omega)]

theorem rejBoundedLoop_mono {eta : ℕ} {s : ℕ → Byte} {f f' pos : ℕ} {st : ℕ × Poly} {b : Poly}
    (h : rejBoundedLoop eta s f pos st = some b) (hf : f ≤ f') :
    rejBoundedLoop eta s f' pos st = some b := by
  induction f generalizing f' pos st with
  | zero => simp [rejBoundedLoop] at h
  | succ f ih =>
    obtain ⟨f', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    simp only [rejBoundedLoop] at h ⊢
    split_ifs at h ⊢
    · exact ih h (by omega)
    · exact h

theorem RejBoundedReturns.unique {eta : ℕ} {s : ℕ → Byte} {a b : Poly}
    (ha : RejBoundedReturns eta s a) (hb : RejBoundedReturns eta s b) : a = b := by
  obtain ⟨f, hf⟩ := ha
  obtain ⟨g, hg⟩ := hb
  have h1 := rejBoundedLoop_mono hf (le_max_left f g)
  have h2 := rejBoundedLoop_mono hg (le_max_right f g)
  rw [h1] at h2; exact Option.some.inj h2

/-- Soundness: if the OCaml scan of the first `L` bytes collects 256
    coefficients, FIPS 204 Algorithm 31 returns the same array. -/
theorem etaState_sound (eta : ℕ) (heta : eta = 2 ∨ eta = 4) (s : ℕ → Byte) (L : ℕ)
    (hL : (etaState eta s L).1 = 256) :
    ∀ k m, m + k = L →
      rejBoundedLoop eta s (k + 1) m (etaState eta s m) = some (etaState eta s L).2 := by
  intro k
  induction k with
  | zero =>
    intro m hm
    obtain rfl : L = m := by omega
    simp [rejBoundedLoop, hL]
  | succ k ih =>
    intro m hm
    rw [rejBoundedLoop]
    split_ifs with hj
    · rw [← etaByte_eq_body eta heta _ _ hj, ← etaState_succ]
      exact ih (m + 1) (by omega)
    · have h256 : (etaState eta s m).1 = 256 := le_antisymm (etaState_le eta heta s m) (by omega)
      rw [etaState_stable eta heta s (by omega : m ≤ L) h256]

/-- Completeness: if FIPS 204 Algorithm 31 returns within `f` iterations
    from the state reached after `m` bytes, the OCaml scan of any prefix of
    length `L ≥ m + f` collects the same 256 coefficients. -/
theorem etaState_complete (eta : ℕ) (heta : eta = 2 ∨ eta = 4) (s : ℕ → Byte) :
    ∀ f m (b : Poly), rejBoundedLoop eta s f m (etaState eta s m) = some b →
      ∀ L, m + f ≤ L → etaState eta s L = (256, b) := by
  intro f
  induction f with
  | zero => intro m b h; simp [rejBoundedLoop] at h
  | succ f ih =>
    intro m b h L hL
    rw [rejBoundedLoop] at h
    split_ifs at h with hj
    · rw [← etaByte_eq_body eta heta _ _ hj, ← etaState_succ] at h
      exact ih (m + 1) b h L (by omega)
    · cases h
      have h256 : (etaState eta s m).1 = 256 := le_antisymm (etaState_le eta heta s m) (by omega)
      rw [etaState_stable eta heta s (by omega : m ≤ L) h256]
      exact Prod.ext h256 rfl

/-- The OCaml recursion is an instance of `restartLoop`. -/
theorem etaPolynomial_eq_restartLoop (eta : ℕ) (H : XOF) (seed : Bytes) (nonce : ℕ) :
    ∀ calls L, etaPolynomial eta H seed nonce calls L =
      restartLoop (fun L => let r := etaState eta (H (seed ++ u16le nonce)) L
        if r.1 = n then some r.2 else none) calls L := by
  intro calls
  induction calls with
  | zero => intro L; rfl
  | succ c ih =>
    intro L
    rw [etaPolynomial, restartLoop, etaScan_squeeze]
    split_ifs with h <;> simp [h, ih]

/-- **Main theorem (obligation 2).** For η ∈ {2, 4}, every XOF, seed,
    nonce and positive initial output length (the code uses 272), the OCaml
    `eta_polynomial` returns `p` iff FIPS 204
    `RejBoundedPoly(seed ‖ IntegerToBytes(nonce, 2))` (Algorithm 31) returns
    `p`. -/
theorem etaPolynomial_returns_iff {eta : ℕ} (heta : eta = 2 ∨ eta = 4) {H : XOF}
    {seed : Bytes} {nonce L : ℕ} (hL : 0 < L) (p : Poly) :
    EtaReturns eta H seed nonce L p ↔
      RejBoundedReturns eta (H (seed ++ integerToBytes nonce 2)) p := by
  rw [← u16le_eq_integerToBytes]
  unfold EtaReturns
  simp only [etaPolynomial_eq_restartLoop]
  apply restartLoop_returns_iff _ (fun a b ha hb => RejBoundedReturns.unique ha hb) _ hL
  · intro L a h
    split_ifs at h with h256
    cases h
    exact ⟨L + 1, by simpa [n, etaState_zero] using etaState_sound eta heta _ L (by simpa [n] using h256) L 0 (by omega)⟩
  · rintro a ⟨f, hf⟩
    refine ⟨f, fun L hL => ?_⟩
    have := etaState_complete eta heta _ f 0 a (by simpa [etaState] using hf) L (by omega)
    simp [this, n]

/-! ## Safety -/

/-- Every `int` intermediate of `accept` is small: `205 * value ≤ 3075`,
    `reduced ∈ [0, 4]`, and the stored coefficient lies in `[−η, η]`. -/
theorem etaAccept_safe (value : ℕ) (hv : value < 16) :
    205 * value < 2 ^ 12 ∧ Portable ((205 * value : ℕ) : ℤ) ∧
    (value < 15 → (2 : ℤ) - ((value : ℤ) - (((205 * value) >>> 10 : ℕ) : ℤ) * 5) ∈ Set.Icc (-2) 2) ∧
    (value < 9 → (4 : ℤ) - value ∈ Set.Icc (-4) 4) := by
  refine ⟨by omega, Portable.of_nat_lt (by omega), fun h15 => ?_, fun h9 => ?_⟩
  · obtain ⟨h1, h2⟩ := reduced_eq_mod5 value h15
    generalize (205 * value) >>> 10 = t at h1 h2 ⊢
    constructor <;> omega
  · constructor <;> omega

/-- The nibbles passed to `accept` are `< 16`, the array index `!count` is
    `< 256` whenever a coefficient is written (the `!count < n` guard), and
    `get_u8 stream position` is in bounds (`position < String.length`). -/
theorem etaByte_nibbles_lt (byte : ℕ) : byte &&& 0x0f < 16 ∧ (byte < 256 → byte >>> 4 < 16) := by
  rw [land_0x0f, lsr_4]; omega

/-- The output of a completed run has all coefficients in `[−η, η]`
    (at indices `< 256`) and is zero elsewhere. -/
theorem etaState_coeff_bound (eta : ℕ) (heta : eta = 2 ∨ eta = 4) (s : ℕ → Byte) (m : ℕ) :
    ∀ i, (i < (etaState eta s m).1 → -(eta : ℤ) ≤ (etaState eta s m).2 i ∧
      (etaState eta s m).2 i ≤ eta) ∧ ((etaState eta s m).1 ≤ i → (etaState eta s m).2 i = 0) := by
  induction m with
  | zero => intro i; simp [etaState]
  | succ m ih =>
    intro i
    rw [etaState_succ]
    generalize etaState eta s m = st at ih ⊢
    have hbound : ∀ b, b < 16 → ∀ v, coeffFromHalfByte eta b = some v →
        -(eta : ℤ) ≤ v ∧ v ≤ eta := by
      intro b hb v hv
      unfold coeffFromHalfByte at hv
      rcases heta with rfl | rfl <;> split_ifs at hv <;> cases hv <;> push_cast <;> omega
    have hacc : ∀ (st : ℕ × Poly) (b : ℕ), b < 16 →
        (∀ i, (i < st.1 → -(eta : ℤ) ≤ st.2 i ∧ st.2 i ≤ eta) ∧ (st.1 ≤ i → st.2 i = 0)) →
        ∀ i, (i < (etaAccept eta st b).1 → -(eta : ℤ) ≤ (etaAccept eta st b).2 i ∧
          (etaAccept eta st b).2 i ≤ eta) ∧
          ((etaAccept eta st b).1 ≤ i → (etaAccept eta st b).2 i = 0) := by
      intro st b hb hst i
      rw [etaAccept_eq eta heta]
      split_ifs with hc
      · cases hv : coeffFromHalfByte eta b with
        | none => exact hst i
        | some v =>
          have := hbound b hb v hv
          simp only
          by_cases hi : i = st.1
          · subst hi; simp [this]
          · rw [Function.update_of_ne hi]
            have := hst i
            constructor
            · intro h; exact this.1 (by omega)
            · intro h; exact this.2 (by omega)
      · exact hst i
    unfold etaByte
    exact hacc _ _ (by rw [lsr_4]; have := (s m).isLt; omega)
      (hacc _ _ (by rw [land_0x0f]; omega) ih) i

/-- Output lengths `272 · 2^r` and their doubles are `Portable` for the first
    21 calls; all positions and the `for` bound `String.length stream - 1` are
    below the output length. -/
theorem eta_outputLength_portable {r : ℕ} (hr : r < 21) :
    Portable ((272 * 2 ^ r : ℕ) : ℤ) ∧ Portable ((2 * (272 * 2 ^ r) : ℕ) : ℤ) := by
  constructor <;> apply Portable.of_nat_lt <;>
    · have : 2 ^ r ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

end OcamlPq.MLDSAAlg
