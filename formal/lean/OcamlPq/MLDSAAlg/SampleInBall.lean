import OcamlPq.MLDSAAlg.RejNTT
import OcamlPq.MLDSAAlg.Restart

/-!
# `challenge_polynomial` refines SampleInBall (FIPS 204 Algorithm 29)

The OCaml code reads the first 8 bytes of SHAKE256(c̃) little-endian into
an `Int64` (`signs`), then for `index = 256 − τ … 255` scans forward for a
byte `candidate ≤ index`, swaps, and stores `+1`/`−1` according to the
least significant bit of `signs`, which it then shifts right. When the
finite prefix runs out (`complete := false`) it restarts with twice the
output length.

Results:
* `challengePolynomial_returns_iff`: the OCaml function returns `c` iff
  FIPS 204 Algorithm 29 returns `c` on the same stream.
* `sampleInBall_output`: every output has exactly `τ` nonzero coefficients
  among indices `< 256`, each `±1`, and is zero at indices `≥ 256`.
* `challengeBody_coeffs`: in every intermediate state of the OCaml loop (also
  in incomplete passes) every coefficient is in `{−1, 0, 1}`.
-/

namespace OcamlPq.MLDSAAlg

/-! ## Specification -/

/-- Lines 7–10 of FIPS 204 Algorithm 29: `j` has just been squeezed (the
    stream position is now `pos`); `while j > i do (ctx, j) ←
    H.Squeeze(ctx, 1)`. At most `fuel` tests of the loop condition. Returns
    the final `j` and stream position. -/
def sibSelect (s : ℕ → Byte) (i : ℕ) : ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _, _ => none
  | fuel + 1, j, pos => if j > i then sibSelect s i fuel (s pos).val (pos + 1) else some (j, pos)

/-- One iteration (lines 7–12) of the `for` loop of FIPS 204 Algorithm 29 on
    the state `(stream position, c)`; `h` is `BytesToBits(s)` of line 5. -/
def sibStep (tau : ℕ) (s : ℕ → Byte) (h : ℕ → ℕ) (fuel : ℕ)
    (st : Option (ℕ × Poly)) (i : ℕ) : Option (ℕ × Poly) :=
  match st with
  | none => none
  | some (pos, c) =>
    match sibSelect s i fuel (s pos).val (pos + 1) with
    | none => none
    | some (j, pos') =>
      let c := Function.update c i (c j)
      some (pos', Function.update c j ((-1 : ℤ) ^ h (i + tau - 256)))

/-- FIPS 204 Algorithm 29, `SampleInBall(ρ)`, on the SHAKE256 stream `s` of
    `ρ`, with every `while` loop bounded by `fuel` tests: `c ← 0`;
    `(ctx, s) ← H.Squeeze(ctx, 8)`; `h ← BytesToBits(s)`; `for i from 256 − τ
    to 255 …`. -/
def sampleInBallFuel (tau : ℕ) (s : ℕ → Byte) (fuel : ℕ) : Option Poly :=
  ((List.range' (256 - tau) tau).foldl
    (sibStep tau s (bytesToBits ((List.range 8).map s)) fuel) (some (8, fun _ => 0))).map
    Prod.snd

/-- FIPS 204 Algorithm 29 on the stream `s` terminates with output `c`. -/
def SampleInBallReturns (tau : ℕ) (s : ℕ → Byte) (c : Poly) : Prop :=
  ∃ fuel, sampleInBallFuel tau s fuel = some c

/-! ## Model of the OCaml code -/

/-- `signs` after the loop of `mldsa_engine.ml`, lines 378–382:
    `signs := Int64.logor !signs (Int64.shift_left (Int64.of_int (get_u8 stream
    index)) (8 * index))` for `index = 0 … 7`. `Int64.t` is `BitVec 64`. -/
def challengeSigns (stream : Bytes) : BitVec 64 :=
  (List.range 8).foldl
    (fun signs index => signs ||| (BitVec.ofNat 64 (getU8 stream index) <<< (8 * index))) 0

/-- The inner `while !selected < 0 && !complete` loop (lines 388–395), on
    `(!selected, !complete, !position)`. -/
def challengeSelect (stream : Bytes) (index : ℕ) (selected : ℤ) (complete : Bool)
    (position : ℕ) : ℤ × Bool × ℕ :=
  if selected < 0 ∧ complete = true then
    if position ≥ stream.length then challengeSelect stream index selected false position
    else
      let candidate := getU8 stream position
      if candidate ≤ index then
        challengeSelect stream index (candidate : ℤ) complete (position + 1)
      else challengeSelect stream index selected complete (position + 1)
  else (selected, complete, position)
termination_by (stream.length - position) + (if complete then 1 else 0)
decreasing_by all_goals (simp_all <;> omega)

/-- The mutable state of `challenge_polynomial`. -/
structure ChallengeState where
  complete : Bool
  position : ℕ
  coefficients : Poly
  signs : BitVec 64

/-- The `for index = n - P.tau to n - 1` loop body (lines 386–403). -/
def challengeBody (stream : Bytes) (st : ChallengeState) (index : ℕ) : ChallengeState :=
  if st.complete then
    let (selected, complete, position) := challengeSelect stream index (-1) st.complete st.position
    if complete then
      let c := Function.update st.coefficients index (st.coefficients selected.toNat)
      let c := Function.update c selected.toNat
        (if st.signs &&& 1#64 = 0#64 then 1 else -1)
      { complete := complete, position := position, coefficients := c, signs := st.signs >>> 1 }
    else { st with complete := complete, position := position }
  else st

/-- One pass of `challenge_polynomial` over `stream` (lines 377–403). -/
def challengeScan (tau : ℕ) (stream : Bytes) : ChallengeState :=
  (List.range' (n - tau) tau).foldl (challengeBody stream)
    { complete := true, position := 8, coefficients := fun _ => 0,
      signs := challengeSigns stream }

/-- `challenge_polynomial seed output_length` (`mldsa_engine.ml`,
    lines 376–406); `calls` bounds the number of (re)starts. -/
def challengePolynomial (tau : ℕ) (shake256 : XOF) (seed : Bytes) :
    (calls : ℕ) → (outputLength : ℕ) → Option Poly
  | 0, _ => none
  | calls + 1, outputLength =>
    let stream := shake256.squeeze seed outputLength
    let st := challengeScan tau stream
    if st.complete then some st.coefficients
    else challengePolynomial tau shake256 seed calls (2 * outputLength)

/-- The OCaml call `challenge_polynomial seed output_length` returns `c`. -/
def ChallengeReturns (tau : ℕ) (shake256 : XOF) (seed : Bytes) (outputLength : ℕ)
    (c : Poly) : Prop :=
  ∃ calls, challengePolynomial tau shake256 seed calls outputLength = some c

/-! ## Searching the stream -/

/-- The first position `p' ∈ [p, p + fuel)` with `s p' ≤ i`. -/
def findLE (s : ℕ → Byte) (i : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, p => if (s p).val ≤ i then some p else findLE s i fuel (p + 1)

theorem findLE_spec (s : ℕ → Byte) (i : ℕ) :
    ∀ f p p', findLE s i f p = some p' ↔
      p ≤ p' ∧ p' < p + f ∧ (s p').val ≤ i ∧ ∀ q, p ≤ q → q < p' → i < (s q).val := by
  intro f
  induction f with
  | zero => intro p p'; simp [findLE]; omega
  | succ f ih =>
    intro p p'
    rw [findLE]
    split_ifs with h
    · constructor
      · rintro ⟨⟩; exact ⟨le_rfl, by omega, h, fun q h1 h2 => by omega⟩
      · rintro ⟨h1, h2, h3, h4⟩
        have : p = p' := by
          by_contra hne
          have := h4 p le_rfl (by omega)
          omega
        rw [this]
    · rw [ih]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨by omega, by omega, h3, fun q hq1 hq2 => ?_⟩
        rcases Nat.eq_or_lt_of_le hq1 with rfl | hq1
        · omega
        · exact h4 q (by omega) hq2
      · rintro ⟨h1, h2, h3, h4⟩
        have hne : p ≠ p' := by rintro rfl; exact h h3
        exact ⟨by omega, by omega, h3, fun q hq1 hq2 => h4 q (by omega) hq2⟩

theorem findLE_ge {s : ℕ → Byte} {i f p p' : ℕ} (h : findLE s i f p = some p') : p ≤ p' :=
  ((findLE_spec s i f p p').mp h).1

theorem findLE_le {s : ℕ → Byte} {i f p p' : ℕ} (h : findLE s i f p = some p') :
    (s p').val ≤ i :=
  ((findLE_spec s i f p p').mp h).2.2.1

theorem findLE_fuel {s : ℕ → Byte} {i f f' p p' : ℕ} (h : findLE s i f p = some p')
    (hf : p' < p + f') : findLE s i f' p = some p' := by
  obtain ⟨h1, _, h3, h4⟩ := (findLE_spec s i f p p').mp h
  exact (findLE_spec s i f' p p').mpr ⟨h1, hf, h3, h4⟩

/-- The FIPS `while` loop is a bounded search. -/
theorem sibSelect_eq (s : ℕ → Byte) (i : ℕ) :
    ∀ f p, sibSelect s i f (s p).val (p + 1) =
      (findLE s i f p).map fun p' => ((s p').val, p' + 1) := by
  intro f
  induction f with
  | zero => intro p; rfl
  | succ f ih =>
    intro p
    rw [sibSelect, findLE]
    split_ifs with h1 h2 h2
    · omega
    · rw [ih]
    · rfl
    · omega

/-- The OCaml `while` loop is a search bounded by the end of the prefix. -/
theorem challengeSelect_eq {H : XOF} {x : Bytes} {L : ℕ} (i : ℕ) :
    ∀ k p, p + k = L →
      challengeSelect (H.squeeze x L) i (-1) true p =
        match findLE (H x) i k p with
        | some p' => (((H x p').val : ℤ), true, p' + 1)
        | none => (-1, false, L) := by
  intro k
  induction k with
  | zero =>
    intro p hp
    rw [challengeSelect]
    simp only [XOF.length_squeeze]
    rw [ite_eq_left (by simp), ite_eq_left (by omega), challengeSelect]
    simp [findLE]; omega
  | succ k ih =>
    intro p hp
    rw [challengeSelect]
    simp only [XOF.length_squeeze]
    rw [ite_eq_left (by simp), ite_eq_right (by omega), getU8_squeeze (by omega), findLE]
    split_ifs with h
    · rw [challengeSelect, ite_eq_right (by simp)]
    · exact ih (p + 1) (by omega)

/-! ## A common abstraction of both loops -/

/-- One loop iteration, parametrised by the search used to find `j`. -/
def absStep (tau : ℕ) (s : ℕ → Byte) (h : ℕ → ℕ) (srch : ℕ → ℕ → Option ℕ)
    (st : Option (ℕ × Poly)) (i : ℕ) : Option (ℕ × Poly) :=
  st.bind fun pc => (srch i pc.1).map fun p' =>
    let j := (s p').val
    (p' + 1, Function.update (Function.update pc.2 i (pc.2 j)) j ((-1 : ℤ) ^ h (i + tau - 256)))

theorem sibStep_eq (tau : ℕ) (s : ℕ → Byte) (h : ℕ → ℕ) (fuel : ℕ) :
    sibStep tau s h fuel = absStep tau s h (fun i p => findLE s i fuel p) := by
  funext st i
  cases st with
  | none => rfl
  | some pc =>
    obtain ⟨p, c⟩ := pc
    simp only [sibStep, absStep, sibSelect_eq, Option.bind_some]
    cases findLE s i fuel p <;> rfl

theorem absFold_none (tau : ℕ) (s : ℕ → Byte) (h : ℕ → ℕ) (srch : ℕ → ℕ → Option ℕ)
    (l : List ℕ) : l.foldl (absStep tau s h srch) none = none := by
  induction l with
  | nil => rfl
  | cons i l ih => simpa [List.foldl, absStep] using ih

theorem absFold_pos_le (tau : ℕ) (s : ℕ → Byte) (h : ℕ → ℕ) (srch : ℕ → ℕ → Option ℕ)
    (hmono : ∀ i p p', srch i p = some p' → p ≤ p') :
    ∀ (l : List ℕ) (pc qc : ℕ × Poly), l.foldl (absStep tau s h srch) (some pc) = some qc →
      pc.1 ≤ qc.1 := by
  intro l
  induction l with
  | nil => intro pc qc hq; cases hq; exact le_rfl
  | cons i l ih =>
    intro pc qc hq
    simp only [List.foldl] at hq
    cases hs : srch i pc.1 with
    | none =>
      simp [absStep, hs, absFold_none] at hq
    | some p' =>
      simp only [absStep, Option.bind_some, hs, Option.map_some] at hq
      have := ih _ _ hq
      have := hmono _ _ _ hs
      simp only at *
      omega

/-- Transfer a completed fold from one search to another that agrees on
    every search result below the final position. -/
theorem absFold_transfer (tau : ℕ) (s : ℕ → Byte) (h : ℕ → ℕ) (srch1 srch2 : ℕ → ℕ → Option ℕ)
    (hmono : ∀ i p p', srch1 i p = some p' → p ≤ p') :
    ∀ (l : List ℕ) (pc qc : ℕ × Poly), l.foldl (absStep tau s h srch1) (some pc) = some qc →
      (∀ i p p', srch1 i p = some p' → p' < qc.1 → srch2 i p = some p') →
      l.foldl (absStep tau s h srch2) (some pc) = some qc := by
  intro l
  induction l with
  | nil => intro pc qc hq _; exact hq
  | cons i l ih =>
    intro pc qc hq htr
    simp only [List.foldl] at hq ⊢
    cases hs : srch1 i pc.1 with
    | none => simp [absStep, hs, absFold_none] at hq
    | some p' =>
      simp only [absStep, Option.bind_some, hs, Option.map_some] at hq ⊢
      have hle := absFold_pos_le tau s h srch1 hmono l _ _ hq
      rw [htr _ _ _ hs (by simp only at hle; omega), Option.map_some]
      exact ih _ _ hq htr

/-! ## Signs -/

theorem challengeSigns_getLsbD_aux (stream : Bytes) :
    ∀ m, m ≤ 8 → ∀ t, t < 64 →
      ((List.range m).foldl
        (fun signs index => signs ||| (BitVec.ofNat 64 (getU8 stream index) <<< (8 * index)))
        0).getLsbD t = (decide (t < 8 * m) && (getU8 stream (t / 8)).testBit (t % 8)) := by
  intro m
  induction m with
  | zero => intro _ t _; simp
  | succ m ih =>
    intro hm t ht
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      BitVec.getLsbD_or, ih (by omega) t ht, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
    by_cases h1 : t < 8 * m
    · have : t < 8 * (m + 1) := by omega
      simp [h1, this]
    · by_cases h2 : t < 8 * (m + 1)
      · have e1 : t / 8 = m := by omega
        have e2 : t % 8 = t - 8 * m := by omega
        simp [h1, h2, ht, e1, e2]
        omega
      · have hb : (getU8 stream m).testBit (t - 8 * m) = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (getU8_lt stream m)
            (by
              calc 256 = 2 ^ 8 := by norm_num
                _ ≤ 2 ^ (t - 8 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, hb]

/-- Bit `t` of `signs` is bit `t mod 8` of byte `⌊t/8⌋` (little-endian). -/
theorem challengeSigns_getLsbD (stream : Bytes) {t : ℕ} (ht : t < 64) :
    (challengeSigns stream).getLsbD t = (getU8 stream (t / 8)).testBit (t % 8) := by
  have := challengeSigns_getLsbD_aux stream 8 le_rfl t ht
  simp only [show t < 8 * 8 from ht, decide_true, Bool.true_and] at this
  exact this

/-- After `t` right shifts, the tested bit is bit `t` of the original. -/
theorem signs_bit (x : BitVec 64) (t : ℕ) :
    ((x >>> t) &&& 1#64 = 0#64) ↔ x.getLsbD t = false := by
  rw [BitVec.toNat_eq, BitVec.toNat_and, BitVec.toNat_ushiftRight]
  simp only [BitVec.toNat_ofNat, Nat.one_mod, Nat.zero_mod, Nat.and_one_is_mod]
  rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  constructor
  · intro h; simp; omega
  · intro h; simp at h; have := Nat.mod_lt (x.toNat / 2 ^ t) (by norm_num : 2 > 0); omega

theorem ushiftRight_succ (x : BitVec 64) (t : ℕ) : (x >>> t) >>> 1 = x >>> (t + 1) := by
  rw [BitVec.toNat_eq, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
    BitVec.toNat_ushiftRight, Nat.shiftRight_add]

/-- The OCaml sign choice equals `(−1)^{h[t]}` of FIPS 204 (line 12). -/
theorem sign_eq {stream : Bytes} {H : XOF} {x : Bytes} {L t : ℕ} (hL : 8 ≤ L) (ht : t < 64)
    (hs : stream = H.squeeze x L) :
    (if (challengeSigns stream >>> t) &&& 1#64 = 0#64 then (1 : ℤ) else -1) =
      (-1 : ℤ) ^ bytesToBits ((List.range 8).map (H x)) t := by
  subst hs
  have hbit : (challengeSigns (H.squeeze x L)).getLsbD t =
      decide ((H x (t / 8)).val / 2 ^ (t % 8) % 2 = 1) := by
    rw [challengeSigns_getLsbD _ ht, getU8_squeeze (by omega), Nat.testBit_eq_decide_div_mod_eq]
  have hbits : bytesToBits ((List.range 8).map (H x)) t = (H x (t / 8)).val / 2 ^ (t % 8) % 2 := by
    unfold bytesToBits
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp
  rw [hbits]
  by_cases hb : (challengeSigns (H.squeeze x L) >>> t) &&& 1#64 = 0#64
  · rw [ite_eq_left hb]
    rw [signs_bit, hbit] at hb
    have : (H x (t / 8)).val / 2 ^ (t % 8) % 2 = 0 := by simp at hb; omega
    rw [this]; simp
  · rw [ite_eq_right hb]
    rw [signs_bit, hbit] at hb
    have : (H x (t / 8)).val / 2 ^ (t % 8) % 2 = 1 := by simpa using hb
    rw [this]; simp

/-! ## The OCaml pass as an abstract fold -/

/-- Relation between the OCaml state after `t` iterations and the abstract
    state. -/
def ChallengeRel (signs0 : BitVec 64) (t : ℕ) (st : ChallengeState)
    (a : Option (ℕ × Poly)) : Prop :=
  (st.complete = true ∧ a = some (st.position, st.coefficients) ∧ st.signs = signs0 >>> t) ∨
  (st.complete = false ∧ a = none)

theorem challengeFold_rel {H : XOF} {x : Bytes} {L tau : ℕ} (hL : 8 ≤ L) (htau : tau ≤ 64) :
    ∀ (k t : ℕ) (st : ChallengeState) (a : Option (ℕ × Poly)), t + k = tau →
      st.position ≤ L →
      ChallengeRel (challengeSigns (H.squeeze x L)) t st a →
      ChallengeRel (challengeSigns (H.squeeze x L)) (t + k)
        ((List.range' (256 - tau + t) k).foldl (challengeBody (H.squeeze x L)) st)
        ((List.range' (256 - tau + t) k).foldl
          (absStep tau (H x) (bytesToBits ((List.range 8).map (H x)))
            (fun i p => findLE (H x) i (L - p) p)) a) := by
  intro k
  induction k with
  | zero => intro t st a _ _ hr; simpa using hr
  | succ k ih =>
    intro t st a hk hpos hr
    rw [List.range'_succ, List.foldl_cons, List.foldl_cons]
    have ih' := ih (t + 1)
    rw [show 256 - tau + t + 1 = 256 - tau + (t + 1) by omega,
      show t + (k + 1) = t + 1 + k by omega]
    rcases hr with ⟨hc, rfl, hsg⟩ | ⟨hc, rfl⟩
    · -- complete state
      have hsel := challengeSelect_eq (H := H) (x := x) (L := L) (256 - tau + t) (L - st.position)
        st.position (by omega)
      cases hf : findLE (H x) (256 - tau + t) (L - st.position) st.position with
      | none =>
        rw [hf] at hsel
        apply ih' _ _ (by omega) (by simp [challengeBody, hc, hsel]) _
        right
        simp [challengeBody, hc, hsel, absStep, hf]
      | some p' =>
        rw [hf] at hsel
        have hp' := (findLE_spec _ _ _ _ _).mp hf
        apply ih' _ _ (by omega) (by simp [challengeBody, hc, hsel]; omega) _
        left
        refine ⟨by simp [challengeBody, hc, hsel], ?_, ?_⟩
        · have hsign : (if st.signs &&& 1#64 = 0#64 then (1 : ℤ) else -1) =
              (-1 : ℤ) ^ bytesToBits ((List.range 8).map (H x)) (256 - tau + t + tau - 256) := by
            rw [show 256 - tau + t + tau - 256 = t by omega, hsg]
            exact sign_eq hL (by omega) rfl
          simp [challengeBody, hc, hsel, absStep, hf, hsign]
        · simp [challengeBody, hc, hsel, hsg, ushiftRight_succ]
    · -- incomplete state stays incomplete
      apply ih' _ _ (by omega) (by simp [challengeBody, hc]; omega) _
      right
      simp [challengeBody, hc, absStep]

/-- One OCaml pass over an `L`-byte prefix (`L ≥ 8`), expressed through the
    abstract fold. -/
theorem challengeScan_rel {H : XOF} {x : Bytes} {L tau : ℕ} (hL : 8 ≤ L) (htau : tau ≤ 64) :
    ChallengeRel (challengeSigns (H.squeeze x L)) tau (challengeScan tau (H.squeeze x L))
      ((List.range' (256 - tau) tau).foldl
          (absStep tau (H x) (bytesToBits ((List.range 8).map (H x)))
            (fun i p => findLE (H x) i (L - p) p)) (some (8, fun _ => 0))) := by
  have := challengeFold_rel (H := H) (x := x) (L := L) hL htau tau 0
    { complete := true, position := 8, coefficients := fun _ => 0,
      signs := challengeSigns (H.squeeze x L) } (some (8, fun _ => 0)) (by omega) (by simpa)
    (Or.inl ⟨rfl, rfl, by simp⟩)
  simpa [challengeScan, n] using this

/-! ## Refinement -/

theorem sampleInBallFuel_mono {tau : ℕ} {s : ℕ → Byte} {f f' : ℕ} {c : Poly}
    (h : sampleInBallFuel tau s f = some c) (hf : f ≤ f') : sampleInBallFuel tau s f' = some c := by
  unfold sampleInBallFuel at h ⊢
  rw [sibStep_eq] at h ⊢
  obtain ⟨qc, hq, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [absFold_transfer tau s _ _ _ (fun i p p' h => findLE_ge h) _ _ qc hq
    (fun i p p' h1 _ => findLE_fuel h1 (by have := ((findLE_spec _ _ _ _ _).mp h1).2.1; omega))]
  rfl

theorem SampleInBallReturns.unique {tau : ℕ} {s : ℕ → Byte} {a b : Poly}
    (ha : SampleInBallReturns tau s a) (hb : SampleInBallReturns tau s b) : a = b := by
  obtain ⟨f, hf⟩ := ha
  obtain ⟨g, hg⟩ := hb
  have h1 := sampleInBallFuel_mono hf (le_max_left f g)
  have h2 := sampleInBallFuel_mono hg (le_max_right f g)
  rw [h1] at h2; exact Option.some.inj h2

/-- The OCaml recursion is an instance of `restartLoop`. -/
theorem challengePolynomial_eq_restartLoop (tau : ℕ) (H : XOF) (seed : Bytes) :
    ∀ calls L, challengePolynomial tau H seed calls L =
      restartLoop (fun L => let st := challengeScan tau (H.squeeze seed L)
        if st.complete then some st.coefficients else none) calls L := by
  intro calls
  induction calls with
  | zero => intro L; rfl
  | succ c ih =>
    intro L
    rw [challengePolynomial, restartLoop]
    split_ifs with h <;> simp [h, ih]

/-- **Main theorem (obligation 3, refinement).** For `τ ≤ 64` (the code uses
    39, 49, 60), every XOF, seed and initial output length `≥ 8` (the code
    uses 136), the OCaml `challenge_polynomial` returns `c` iff FIPS 204
    `SampleInBall(seed)` (Algorithm 29) returns `c`. -/
theorem challengePolynomial_returns_iff {tau : ℕ} (htau : tau ≤ 64) {H : XOF} {seed : Bytes}
    {L0 : ℕ} (hL0 : 8 ≤ L0) (c : Poly) :
    ChallengeReturns tau H seed L0 c ↔ SampleInBallReturns tau (H seed) c := by
  unfold ChallengeReturns
  simp only [challengePolynomial_eq_restartLoop]
  apply restartLoop_returns_iff' (L0 := L0) _ (fun a b ha hb => SampleInBallReturns.unique ha hb)
    _ (by omega)
  · -- soundness
    intro L a hL h
    split_ifs at h with hc
    cases h
    have hrel := challengeScan_rel (H := H) (x := seed) (L := L) (by omega) htau
    rcases hrel with ⟨_, hfold, _⟩ | ⟨hc', _⟩
    · refine ⟨L, ?_⟩
      unfold sampleInBallFuel
      rw [sibStep_eq, absFold_transfer tau (H seed) _ _ _ (fun i p p' h => findLE_ge h) _ _ _
        hfold (fun i p p' h1 _ => findLE_fuel h1
          (by have := ((findLE_spec _ _ _ _ _).mp h1).2.1; omega))]
      rfl
    · rw [hc] at hc'; cases hc'
  · -- completeness
    rintro a ⟨f, hf⟩
    unfold sampleInBallFuel at hf
    rw [sibStep_eq] at hf
    obtain ⟨qc, hq, rfl⟩ := Option.map_eq_some_iff.mp hf
    refine ⟨qc.1 + 8, fun L hL => ?_⟩
    have hq' := absFold_transfer tau (H seed) _ _ (fun i p => findLE (H seed) i (L - p) p)
      (fun i p p' h => findLE_ge h) _ _ qc hq
      (fun i p p' h1 h2 => findLE_fuel h1 (by have := findLE_ge h1; omega))
    have hrel := challengeScan_rel (H := H) (x := seed) (L := L) (by omega) htau
    rcases hrel with ⟨hc, hfold, _⟩ | ⟨_, hfold⟩
    · rw [hq'] at hfold
      simp only [hc, ite_true]
      rw [Option.some.inj hfold]
    · rw [hq'] at hfold; cases hfold

/-! ## Shape of the challenge -/

/-- Number of nonzero coefficients among indices `< 256`. -/
def nonzeroCount (c : Poly) : ℕ := ((Finset.range 256).filter fun k => c k ≠ 0).card

theorem sum_update_add (s : Finset ℕ) (f : ℕ → ℕ) {k : ℕ} (hk : k ∈ s) (b : ℕ) :
    (∑ x ∈ s, Function.update f k b x) + f k = (∑ x ∈ s, f x) + b := by
  rw [Finset.sum_update_of_mem hk, ← Finset.add_sum_erase s f hk, Finset.sdiff_singleton_eq_erase]
  ring

theorem nonzeroCount_update (c : Poly) {k : ℕ} (hk : k < 256) (v : ℤ) :
    nonzeroCount (Function.update c k v) + (if c k = 0 then 0 else 1) =
      nonzeroCount c + (if v = 0 then 0 else 1) := by
  unfold nonzeroCount
  rw [Finset.card_filter, Finset.card_filter]
  have := sum_update_add (Finset.range 256) (fun x => if c x ≠ 0 then 1 else 0)
    (Finset.mem_range.mpr hk) (if v ≠ 0 then 1 else 0)
  have e : ∀ x, (if Function.update c k v x ≠ 0 then 1 else 0) =
      Function.update (fun x => if c x ≠ 0 then 1 else 0) k (if v ≠ 0 then 1 else 0) x := by
    intro x
    by_cases hx : x = k
    · subst hx; simp
    · simp [Function.update_of_ne hx]
  simp only [e]
  by_cases h1 : c k = 0 <;> by_cases h2 : v = 0 <;> simp_all

/-- The invariant of the abstract fold after `t` iterations. -/
def BallInv (tau t : ℕ) (c : Poly) : Prop :=
  (∀ k, c k = 0 ∨ c k = 1 ∨ c k = -1) ∧ (∀ k, 256 - tau + t ≤ k → c k = 0) ∧
    nonzeroCount c = t

theorem sign_pm (b : ℕ) (hb : b ≤ 1) : (-1 : ℤ) ^ b = 1 ∨ (-1 : ℤ) ^ b = -1 := by
  interval_cases b <;> simp

theorem ballInv_step {tau t : ℕ} (htau : tau ≤ 256) (ht : t < tau) {c : Poly} (hc : BallInv tau t c)
    {j : ℕ} (hj : j ≤ 256 - tau + t) {e : ℕ} (he : e ≤ 1) :
    BallInv tau (t + 1)
      (Function.update (Function.update c (256 - tau + t) (c j)) j ((-1 : ℤ) ^ e)) := by
  obtain ⟨hv, hz, hn⟩ := hc
  set i := 256 - tau + t with hi
  have hci : c i = 0 := hz i le_rfl
  have hsgn := sign_pm e he
  refine ⟨?_, ?_, ?_⟩
  · intro k
    by_cases hkj : k = j
    · subst hkj; simp; tauto
    · rw [Function.update_of_ne hkj]
      by_cases hki : k = i
      · subst hki; simp; exact hv j
      · rw [Function.update_of_ne hki]; exact hv k
  · intro k hk
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hz k (by omega)
  · have h1 := nonzeroCount_update (Function.update c i (c j)) (k := j) (by omega) ((-1 : ℤ) ^ e)
    have h2 := nonzeroCount_update c (k := i) (by omega) (c j)
    have hju : Function.update c i (c j) j = c j := by
      by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji]
    rw [hju] at h1
    rw [hci] at h2
    have hne : (-1 : ℤ) ^ e ≠ 0 := by rcases hsgn with h | h <;> rw [h] <;> norm_num
    simp only [hne, ite_false, ite_true] at h1 h2
    simp only [hn] at h2
    split_ifs at h1 h2 <;> omega

theorem absFold_ballInv {tau : ℕ} (htau : tau ≤ 256) (s : ℕ → Byte) (h : ℕ → ℕ)
    (hh : ∀ k, h k ≤ 1) (srch : ℕ → ℕ → Option ℕ)
    (hsrch : ∀ i p p', srch i p = some p' → (s p').val ≤ i) :
    ∀ k t (pc qc : ℕ × Poly), t + k = tau → BallInv tau t pc.2 →
      (List.range' (256 - tau + t) k).foldl (absStep tau s h srch) (some pc) = some qc →
      BallInv tau tau qc.2 := by
  intro k
  induction k with
  | zero => intro t pc qc hk hinv hq; cases hq; simpa [show t = tau by omega] using hinv
  | succ k ih =>
    intro t pc qc hk hinv hq
    rw [List.range'_succ, List.foldl_cons] at hq
    cases hs : srch (256 - tau + t) pc.1 with
    | none => simp [absStep, hs, absFold_none] at hq
    | some p' =>
      simp only [absStep, Option.bind_some, hs, Option.map_some] at hq
      rw [show 256 - tau + t + 1 = 256 - tau + (t + 1) by omega] at hq
      refine ih (t + 1) _ qc (by omega) ?_ hq
      simp only
      rw [show 256 - tau + t + tau - 256 = t by omega]
      exact ballInv_step htau (by omega) hinv (hsrch _ _ _ hs) (hh t)

/-- **Obligation 3 (shape).** Every output of FIPS 204 Algorithm 29 (hence,
    by `challengePolynomial_returns_iff`, every value returned by the OCaml
    `challenge_polynomial`) has exactly `τ` nonzero coefficients among
    indices `< 256`, every coefficient is `−1`, `0` or `1`, and the array is
    zero beyond index 255. Precondition: `τ ≤ 256`. -/
theorem sampleInBall_output {tau : ℕ} (htau : tau ≤ 256) {s : ℕ → Byte} {c : Poly}
    (hc : SampleInBallReturns tau s c) :
    ((Finset.range 256).filter fun k => c k ≠ 0).card = tau ∧
    (∀ k, c k = 0 ∨ c k = 1 ∨ c k = -1) ∧ (∀ k, 256 ≤ k → c k = 0) := by
  obtain ⟨f, hf⟩ := hc
  unfold sampleInBallFuel at hf
  rw [sibStep_eq] at hf
  obtain ⟨qc, hq, rfl⟩ := Option.map_eq_some_iff.mp hf
  have := absFold_ballInv htau s _ (bytesToBits_le_one _) _ (fun i p p' h => findLE_le h)
    tau 0 (8, fun _ => 0) qc (by omega)
    ⟨fun _ => Or.inl rfl, fun _ _ => rfl, by simp [nonzeroCount]⟩ (by simpa using hq)
  obtain ⟨h1, h2, h3⟩ := this
  exact ⟨h3, h1, fun k hk => h2 k (by omega)⟩

/-- **Obligation 3 (intermediate states).** Every loop iteration of the
    OCaml code, complete or not, keeps all coefficients in `{−1, 0, 1}`. -/
theorem challengeBody_coeffs (stream : Bytes) (st : ChallengeState) (index : ℕ)
    (h : ∀ k, st.coefficients k = 0 ∨ st.coefficients k = 1 ∨ st.coefficients k = -1) :
    ∀ k, (challengeBody stream st index).coefficients k = 0 ∨
      (challengeBody stream st index).coefficients k = 1 ∨
      (challengeBody stream st index).coefficients k = -1 := by
  intro k
  unfold challengeBody
  by_cases hc : st.complete = true
  · rw [ite_eq_left hc]
    generalize challengeSelect stream index (-1) st.complete st.position = r
    obtain ⟨sel, comp, pos⟩ := r
    dsimp only
    by_cases hcomp : comp = true
    · rw [ite_eq_left hcomp]
      dsimp only
      by_cases hk : k = sel.toNat
      · subst hk; rw [Function.update_self]; split_ifs <;> simp
      · rw [Function.update_of_ne hk]
        by_cases hk' : k = index
        · subst hk'; rw [Function.update_self]; exact h _
        · rw [Function.update_of_ne hk']; exact h k
    · rw [ite_eq_right hcomp]; exact h k
  · rw [ite_eq_right hc]; exact h k

/-- Along the OCaml loop: whenever a swap happens, `selected ∈ [0, index]`
    (so `coefficients.(!selected)` is in bounds), and the stream position
    never exceeds the prefix length. -/
theorem challengeSelect_bounds {H : XOF} {x : Bytes} {L : ℕ} (i p : ℕ) (hp : p ≤ L) :
    let r := challengeSelect (H.squeeze x L) i (-1) true p
    r.2.2 ≤ L ∧ (r.2.1 = true → 0 ≤ r.1 ∧ r.1 ≤ i ∧ p < r.2.2) := by
  have := challengeSelect_eq (H := H) (x := x) (L := L) i (L - p) p (by omega)
  simp only [this]
  cases hf : findLE (H x) i (L - p) p with
  | none => simp
  | some p' =>
    have := (findLE_spec _ _ _ _ _).mp hf
    simp only [true_implies]
    refine ⟨by omega, by positivity, by exact_mod_cast this.2.2.1, by omega⟩

/-- Output lengths `136 · 2^r` (and doubles) are `Portable` for the first 22
    calls; `8 * index ≤ 56`; `candidate < 256`; `selected ∈ [−1, 255]`. (A
    restart needs more than 128 draws after the sign bytes; for uniformly
    random SHAKE256 output that has probability about `2^-203`, `2^-140`,
    `2^-88` for `τ = 39, 49, 60`.) -/
theorem challenge_outputLength_portable {r : ℕ} (hr : r < 22) :
    Portable ((136 * 2 ^ r : ℕ) : ℤ) ∧ Portable ((2 * (136 * 2 ^ r) : ℕ) : ℤ) := by
  constructor <;> apply Portable.of_nat_lt <;>
    · have : 2 ^ r ≤ 2 ^ 21 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

end OcamlPq.MLDSAAlg
