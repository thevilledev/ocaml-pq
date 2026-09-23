import OcamlPq.MLDSAAlg.Bytes
import OcamlPq.MLDSAAlg.Params

/-!
# `uniform_polynomial` refines RejNTTPoly (FIPS 204 Algorithms 14 and 30)

The OCaml sampler squeezes a finite prefix of SHAKE128 (840 bytes at first),
scans it three bytes at a time, and if the prefix yields fewer than 256
coefficients restarts from scratch with twice the output length. FIPS 204
instead squeezes three bytes at a time from an unbounded stream.

Because the stream of a restarted call extends the previous one (prefix
consistency), every run of the OCaml function that returns produces exactly
the FIPS output, and the OCaml function returns exactly when FIPS 204 does,
i.e. when the stream eventually contains 256 accepted triples
(`uniformPolynomial_returns_iff`, `rejNTTPoly_terminates_iff`).
-/

namespace OcamlPq.MLDSAAlg

/-- An OCaml `int array` of length 256 holding a polynomial: index ↦
    coefficient. Arrays are created by `Array.make n 0` (the constant `0`
    function) and written by `a.(i) <- v` (`Function.update a i v`). -/
abbrev Poly := ℕ → ℤ

/-! ## Specification -/

/-- FIPS 204 Algorithm 14, `CoeffFromThreeBytes(b0, b1, b2)`; `none` is `⊥`. -/
def coeffFromThreeBytes (b0 b1 b2 : ℕ) : Option ℕ :=
  let b2' := if b2 > 127 then b2 - 128 else b2
  let z := 2 ^ 16 * b2' + 2 ^ 8 * b1 + b0
  if z < q then some z else none

/-- The `while j < 256` loop of FIPS 204 Algorithm 30, `RejNTTPoly(ρ)`, run
    for at most `fuel` iterations on the SHAKE128 stream `s` of `ρ`. The XOF
    context is the stream position `pos`; `G.Squeeze(ctx, 3)` reads
    `s pos, s (pos+1), s (pos+2)`. (Algorithm 30 stores `⊥` in `â[j]` and
    then does not advance `j`, so the slot is overwritten later; storing only
    non-`⊥` values yields the same final array.) Returns `none` when the fuel
    runs out. -/
def rejNTTPolyLoop (s : ℕ → Byte) : ℕ → ℕ → ℕ → Poly → Option Poly
  | 0, _, _, _ => none
  | fuel + 1, pos, j, a =>
    if j < 256 then
      match coeffFromThreeBytes (s pos).val (s (pos + 1)).val (s (pos + 2)).val with
      | some z => rejNTTPolyLoop s fuel (pos + 3) (j + 1) (Function.update a j (z : ℤ))
      | none => rejNTTPolyLoop s fuel (pos + 3) j a
    else some a

/-- FIPS 204 Algorithm 30 on the stream `s` terminates with output `a`. -/
def RejNTTPolyReturns (s : ℕ → Byte) (a : Poly) : Prop :=
  ∃ fuel, rejNTTPolyLoop s fuel 0 0 (fun _ => 0) = some a

/-! ## Model of the OCaml code -/

/-- `value` in `uniform_polynomial` (`mldsa_engine.ml`, lines 339–342). -/
def uniformValue (stream : Bytes) (position : ℕ) : ℕ :=
  getU8 stream position ||| (getU8 stream (position + 1) <<< 8) |||
    ((getU8 stream (position + 2) &&& 0x7f) <<< 16)

/-- The `while` loop of `uniform_polynomial` (`mldsa_engine.ml`,
    lines 335–348); returns the final `(!count, coefficients)`. -/
def uniformLoop (stream : Bytes) (count position : ℕ) (coefficients : Poly) : ℕ × Poly :=
  if count < n ∧ position + 2 < stream.length then
    let value := uniformValue stream position
    if value < q then
      uniformLoop stream (count + 1) (position + 3) (Function.update coefficients count (value : ℤ))
    else uniformLoop stream count (position + 3) coefficients
  else (count, coefficients)
termination_by stream.length - position

/-- `uniform_polynomial seed nonce output_length` (`mldsa_engine.ml`,
    lines 330–349). The OCaml function is recursive without a bound; `calls`
    bounds the number of (re)starts, and `none` means "has not returned within
    `calls` calls". -/
def uniformPolynomial (shake128 : XOF) (seed : Bytes) (nonce : ℕ) :
    (calls : ℕ) → (outputLength : ℕ) → Option Poly
  | 0, _ => none
  | calls + 1, outputLength =>
    let stream := shake128.squeeze (seed ++ u16le nonce) outputLength
    let r := uniformLoop stream 0 0 (fun _ => 0)
    if r.1 = n then some r.2
    else uniformPolynomial shake128 seed nonce calls (2 * outputLength)

/-- The OCaml call `uniform_polynomial seed nonce output_length` returns `p`. -/
def UniformReturns (shake128 : XOF) (seed : Bytes) (nonce outputLength : ℕ) (p : Poly) : Prop :=
  ∃ calls, uniformPolynomial shake128 seed nonce calls outputLength = some p

/-! ## Byte-level lemma -/

/-- The OCaml bit manipulation computes CoeffFromThreeBytes' `z`:
    `b0 lor (b1 lsl 8) lor ((b2 land 0x7f) lsl 16) = 2^16·b2' + 2^8·b1 + b0`
    with `b2' = b2 − 128` if `b2 > 127`. -/
theorem value_bits_eq {b0 b1 b2 : ℕ} (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) :
    (b0 ||| (b1 <<< 8) ||| ((b2 &&& 0x7f) <<< 16)) =
      2 ^ 16 * (if b2 > 127 then b2 - 128 else b2) + 2 ^ 8 * b1 + b0 := by
  have hm : b2 &&& 0x7f = b2 % 128 := by
    have := Nat.and_two_pow_sub_one_eq_mod b2 7; norm_num at this; exact this
  have e1 : b0 ||| (b1 <<< 8) = b1 <<< 8 + b0 := by
    rw [Nat.lor_comm]; exact (Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega) b1).symm
  have hlt : b1 <<< 8 + b0 < 2 ^ 16 := by rw [Nat.shiftLeft_eq]; omega
  have e2 : (b1 <<< 8 + b0) ||| ((b2 % 128) <<< 16) = (b2 % 128) <<< 16 + (b1 <<< 8 + b0) := by
    rw [Nat.lor_comm]; exact (Nat.shiftLeft_add_eq_or_of_lt hlt _).symm
  rw [hm, e1, e2, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  split_ifs <;> omega

theorem uniformValue_lt (stream : Bytes) (position : ℕ) :
    uniformValue stream position < 2 ^ 23 := by
  have h0 := getU8_lt stream position
  have h1 := getU8_lt stream (position + 1)
  have h2 := getU8_lt stream (position + 2)
  unfold uniformValue
  rw [value_bits_eq h0 h1 h2]
  split_ifs <;> omega

/-- On a squeezed prefix, one iteration of the OCaml loop computes the
    FIPS 204 CoeffFromThreeBytes of the same three stream bytes. -/
theorem uniformValue_squeeze {H : XOF} {x : Bytes} {L pos : ℕ} (h : pos + 2 < L) :
    coeffFromThreeBytes (H x pos).val (H x (pos + 1)).val (H x (pos + 2)).val =
      if uniformValue (H.squeeze x L) pos < q then
        some (uniformValue (H.squeeze x L) pos) else none := by
  unfold uniformValue
  rw [getU8_squeeze (by omega), getU8_squeeze (by omega), getU8_squeeze h,
    value_bits_eq (H x pos).isLt (H x (pos + 1)).isLt (H x (pos + 2)).isLt]
  rfl

/-! ## Loop correspondence -/

theorem rejNTTPolyLoop_mono {s : ℕ → Byte} {f f' pos j : ℕ} {a b : Poly}
    (h : rejNTTPolyLoop s f pos j a = some b) (hf : f ≤ f') :
    rejNTTPolyLoop s f' pos j a = some b := by
  induction f generalizing f' pos j a with
  | zero => simp [rejNTTPolyLoop] at h
  | succ f ih =>
    obtain ⟨f', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    simp only [rejNTTPolyLoop] at h ⊢
    split_ifs at h ⊢ with hj
    · cases hz : coeffFromThreeBytes (s pos).val (s (pos + 1)).val (s (pos + 2)).val <;>
        rw [hz] at h <;> exact ih h (by omega)
    · exact h

/-- FIPS 204 Algorithm 30 is deterministic: it has at most one output. -/
theorem RejNTTPolyReturns.unique {s : ℕ → Byte} {a b : Poly}
    (ha : RejNTTPolyReturns s a) (hb : RejNTTPolyReturns s b) : a = b := by
  obtain ⟨f, hf⟩ := ha
  obtain ⟨g, hg⟩ := hb
  have h1 := rejNTTPolyLoop_mono hf (le_max_left f g)
  have h2 := rejNTTPolyLoop_mono hg (le_max_right f g)
  rw [h1] at h2; exact Option.some.inj h2

/-- Soundness of one pass: if the OCaml loop over an `L`-byte prefix
    collects 256 coefficients, FIPS 204 Algorithm 30 (from the same state)
    returns the same array. -/
theorem uniformLoop_sound {H : XOF} {x : Bytes} {L : ℕ} :
    ∀ (count position : ℕ) (a b : Poly), count ≤ 256 →
      uniformLoop (H.squeeze x L) count position a = (256, b) →
      ∃ f, rejNTTPolyLoop (H x) f position count a = some b := by
  intro count position a b hc h
  induction count, position, a using uniformLoop.induct (stream := H.squeeze x L) with
  | case1 count position a hcond value hv ih =>
    rw [uniformLoop, ite_eq_left hcond] at h
    simp only at h
    rw [ite_eq_left hv] at h
    obtain ⟨f, hf⟩ := ih (by simp [n] at hcond; omega) h
    refine ⟨f + 1, ?_⟩
    have hcond' := hcond; simp only [XOF.length_squeeze, n] at hcond'
    rw [rejNTTPolyLoop, ite_eq_left hcond'.1, uniformValue_squeeze (L := L) hcond'.2, ite_eq_left hv]
    exact hf
  | case2 count position a hcond value hv ih =>
    rw [uniformLoop, ite_eq_left hcond] at h
    simp only at h
    rw [ite_eq_right hv] at h
    obtain ⟨f, hf⟩ := ih hc h
    refine ⟨f + 1, ?_⟩
    have hcond' := hcond; simp only [XOF.length_squeeze, n] at hcond'
    rw [rejNTTPolyLoop, ite_eq_left hcond'.1, uniformValue_squeeze (L := L) hcond'.2, ite_eq_right hv]
    exact hf
  | case3 count position a hcond =>
    rw [uniformLoop, ite_eq_right hcond] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨1, by simp [rejNTTPolyLoop]⟩

/-- Completeness of one pass: if FIPS 204 Algorithm 30 returns after at most
    `f` iterations, the OCaml loop over any prefix of at least `pos + 3f`
    bytes collects the same 256 coefficients. -/
theorem uniformLoop_complete {H : XOF} {x : Bytes} :
    ∀ (f position count : ℕ) (a b : Poly) (L : ℕ), count ≤ 256 →
      rejNTTPolyLoop (H x) f position count a = some b → position + 3 * f ≤ L →
      uniformLoop (H.squeeze x L) count position a = (256, b) := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _ _ h; simp [rejNTTPolyLoop] at h
  | succ f ih =>
    intro position count a b L hc h hL
    rw [rejNTTPolyLoop] at h
    split_ifs at h with hj
    · have hcond : count < n ∧ position + 2 < (H.squeeze x L).length := by
        simp [n]; omega
      rw [uniformLoop, ite_eq_left hcond]
      rw [uniformValue_squeeze (L := L) (by omega)] at h
      split_ifs at h with hv
      · simp only [hv, ite_true]
        exact ih _ _ _ _ _ (by omega) h (by omega)
      · simp only [hv, ite_false]
        exact ih _ _ _ _ _ hc h (by omega)
    · have hcount : count = 256 := by omega
      subst hcount
      cases h
      rw [uniformLoop, ite_eq_right (by simp [n])]

/-- `uniformPolynomial` only ever returns FIPS 204 outputs. -/
theorem uniformPolynomial_sound {H : XOF} {seed : Bytes} {nonce : ℕ} :
    ∀ (calls L : ℕ) (p : Poly), uniformPolynomial H seed nonce calls L = some p →
      RejNTTPolyReturns (H (seed ++ u16le nonce)) p := by
  intro calls
  induction calls with
  | zero => intro L p h; simp [uniformPolynomial] at h
  | succ calls ih =>
    intro L p h
    rw [uniformPolynomial] at h
    split_ifs at h with h256
    · cases h
      obtain ⟨f, hf⟩ := uniformLoop_sound (H := H) (x := seed ++ u16le nonce) (L := L) 0 0
        (fun _ => 0) _ (by omega) (by
          simp only [n] at h256; rw [← h256])
      exact ⟨f, hf⟩
    · exact ih _ _ h

/-- Completeness: if FIPS 204 Algorithm 30 terminates (within `f`
    iterations), the OCaml function returns within `3f + 1` calls, for any
    positive initial output length. -/
theorem uniformPolynomial_complete {H : XOF} {seed : Bytes} {nonce : ℕ} {p : Poly} {f : ℕ}
    (hf : rejNTTPolyLoop (H (seed ++ u16le nonce)) f 0 0 (fun _ => 0) = some p) :
    ∀ (calls L : ℕ), 0 < L → 3 * f ≤ L * 2 ^ calls →
      ∃ p', uniformPolynomial H seed nonce (calls + 1) L = some p' := by
  intro calls
  induction calls with
  | zero =>
    intro L hL hfL
    have := uniformLoop_complete (H := H) (x := seed ++ u16le nonce) f 0 0 _ _ L (by omega) hf
      (by simpa using hfL)
    exact ⟨p, by simp [uniformPolynomial, this, n]⟩
  | succ calls ih =>
    intro L hL hfL
    rw [uniformPolynomial]
    split_ifs
    · exact ⟨_, rfl⟩
    · exact ih (2 * L) (by omega) (by rw [pow_succ] at hfL; linarith)

/-- **Main theorem (obligation 1).** For every XOF `H`, seed, nonce and
    positive initial output length (the code uses 840), the OCaml
    `uniform_polynomial` returns `p` iff FIPS 204 `RejNTTPoly(seed ‖
    IntegerToBytes(nonce, 2))` (Algorithm 30) returns `p` on the stream
    `H(seed ‖ u16_le nonce)`. -/
theorem uniformPolynomial_returns_iff {H : XOF} {seed : Bytes} {nonce L : ℕ} (hL : 0 < L)
    (p : Poly) :
    UniformReturns H seed nonce L p ↔ RejNTTPolyReturns (H (seed ++ integerToBytes nonce 2)) p := by
  rw [← u16le_eq_integerToBytes]
  constructor
  · rintro ⟨calls, h⟩; exact uniformPolynomial_sound calls L p h
  · rintro ⟨f, hf⟩
    have hbig : 3 * f ≤ L * 2 ^ (3 * f) := by
      have : 3 * f < 2 ^ (3 * f) := Nat.lt_two_pow_self
      nlinarith
    obtain ⟨p', hp'⟩ := uniformPolynomial_complete hf (3 * f) L hL hbig
    have := uniformPolynomial_sound _ _ _ hp'
    rw [RejNTTPolyReturns.unique this ⟨f, hf⟩] at hp'
    exact ⟨_, hp'⟩

/-- The OCaml function is deterministic (at most one result). -/
theorem UniformReturns.unique {H : XOF} {seed : Bytes} {nonce L : ℕ} {p p' : Poly}
    (h : UniformReturns H seed nonce L p) (h' : UniformReturns H seed nonce L p') : p = p' := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  exact RejNTTPolyReturns.unique (uniformPolynomial_sound _ _ _ hc)
    (uniformPolynomial_sound _ _ _ hc')

/-! ## When does sampling terminate? -/

/-- The number of accepted triples among the first `m` triples of `s`. -/
def acceptedTriples (s : ℕ → Byte) (m : ℕ) : ℕ :=
  ((List.range m).filter fun i =>
    (coeffFromThreeBytes (s (3 * i)).val (s (3 * i + 1)).val (s (3 * i + 2)).val).isSome).length

theorem acceptedTriples_succ (s : ℕ → Byte) (m : ℕ) :
    acceptedTriples s (m + 1) = acceptedTriples s m +
      if (coeffFromThreeBytes (s (3 * m)).val (s (3 * m + 1)).val (s (3 * m + 2)).val).isSome
      then 1 else 0 := by
  unfold acceptedTriples
  rw [List.range_succ, List.filter_append]
  simp only [List.length_append]
  split_ifs with h <;> simp [h]

theorem acceptedTriples_mono (s : ℕ → Byte) {m m' : ℕ} (h : m ≤ m') :
    acceptedTriples s m ≤ acceptedTriples s m' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [acceptedTriples_succ]; omega

/-- FIPS 204 Algorithm 30 (and hence the OCaml sampler) terminates on the
    stream `s` exactly when some finite prefix of the stream contains 256
    accepted triples. -/
theorem rejNTTPoly_terminates_iff (s : ℕ → Byte) :
    (∃ a, RejNTTPolyReturns s a) ↔ ∃ m, 256 ≤ acceptedTriples s m := by
  constructor
  · rintro ⟨a, f, hf⟩
    -- generalize over the state reached after `i` triples
    suffices ∀ f i (a b : Poly), acceptedTriples s i ≤ 256 →
        rejNTTPolyLoop s f (3 * i) (acceptedTriples s i) a = some b →
        ∃ m, 256 ≤ acceptedTriples s m from
      this f 0 _ a (by simp [acceptedTriples]) (by simpa [acceptedTriples] using hf)
    intro f
    induction f with
    | zero => intro _ _ _ _ h; simp [rejNTTPolyLoop] at h
    | succ f ih =>
      intro i a b hi h
      rw [rejNTTPolyLoop] at h
      split_ifs at h with hj
      · have hs := acceptedTriples_succ s i
        split at h
        · rename_i z hz
          simp only [hz, Option.isSome_some, ite_true] at hs
          exact ih (i + 1) _ b (by omega) (by rw [hs]; simpa [mul_add] using h)
        · rename_i hz
          simp only [hz, Option.isSome_none, Bool.false_eq_true, ite_false] at hs
          exact ih (i + 1) _ b (by omega) (by rw [hs]; simpa [mul_add] using h)
      · exact ⟨i, by omega⟩
  · rintro ⟨m, hm⟩
    suffices ∀ k i (a : Poly), i + k = m → acceptedTriples s i ≤ 256 →
        ∃ b, rejNTTPolyLoop s (k + 1) (3 * i) (acceptedTriples s i) a = some b by
      obtain ⟨b, hb⟩ := this m 0 (fun _ => 0) (by omega) (by simp [acceptedTriples])
      exact ⟨b, m + 1, by simpa [acceptedTriples] using hb⟩
    intro k
    induction k with
    | zero =>
      intro i a hi _
      subst hi
      refine ⟨a, ?_⟩
      rw [rejNTTPolyLoop, ite_eq_right (by simp at hm ⊢; omega)]
    | succ k ih =>
      intro i a hi hle
      rw [rejNTTPolyLoop]
      split_ifs with hj
      · have hs := acceptedTriples_succ s i
        split
        · rename_i z hz
          simp only [hz, Option.isSome_some, ite_true] at hs
          have := ih (i + 1) (Function.update a (acceptedTriples s i) (z : ℤ)) (by omega)
            (by omega)
          rw [hs] at this; simpa [mul_add] using this
        · rename_i hz
          simp only [hz, Option.isSome_none, Bool.false_eq_true, ite_false] at hs
          have := ih (i + 1) a (by omega) (by omega)
          rw [hs] at this; simpa [mul_add] using this
      · exact ⟨a, rfl⟩

/-! ## Safety: bounds and portability -/

/-- Loop invariant of `uniformLoop` for a stream of length `L`. -/
def UniformInv (L count position : ℕ) : Prop := count ≤ n ∧ position ≤ L

/-- Every iteration from a state satisfying the invariant: string indices
    `position`, `position + 1`, `position + 2` are in bounds, the array
    index `!count` is in bounds, every `int` intermediate
    (`!position + 2`, `value`, `!position + 3`, `!count + 1`) is `Portable`
    when the output length `L` satisfies `L + 3 < 2^30`, and the invariant is
    re-established. -/
theorem uniformLoop_step_safe {stream : Bytes} {count position : ℕ}
    (hinv : UniformInv stream.length count position) (hL : stream.length + 3 < 2 ^ 30) :
    Portable ((position : ℤ) + 2) ∧
    (count < n ∧ position + 2 < stream.length →
      position + 2 < stream.length ∧ count < n ∧
      Portable (uniformValue stream position : ℤ) ∧ Portable ((position : ℤ) + 3) ∧
      Portable ((count : ℤ) + 1) ∧
      UniformInv stream.length (count + 1) (position + 3) ∧
      UniformInv stream.length count (position + 3)) := by
  obtain ⟨hc, hp⟩ := hinv
  refine ⟨by have := Portable.of_nat_lt (n := position + 2) (by omega); push_cast at this; exact this, ?_⟩
  rintro ⟨hc', hp'⟩
  have hv := uniformValue_lt stream position
  refine ⟨hp', hc', Portable.of_nat_lt (by omega), ?_, ?_, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  · have := Portable.of_nat_lt (n := position + 3) (by omega); push_cast at this; exact this
  · have := Portable.of_nat_lt (n := count + 1) (by simp [n] at hc'; omega)
    push_cast at this; exact this

/-- The loop starts in the invariant. -/
theorem uniformInv_init (L : ℕ) : UniformInv L 0 0 := ⟨by simp [n], by omega⟩

/-- The output lengths requested by successive restarts are
    `840 · 2^r`; they (and the doubled value computed before restart `r+1`)
    are `Portable` for the first 20 calls. Reaching the 2nd call already
    requires 25 rejected triples among the first 280, which for uniformly
    random SHAKE128 output has probability about `2^-132`. -/
theorem uniform_outputLength_portable {r : ℕ} (hr : r < 20) :
    Portable ((840 * 2 ^ r : ℕ) : ℤ) ∧ Portable ((2 * (840 * 2 ^ r) : ℕ) : ℤ) := by
  constructor <;> apply Portable.of_nat_lt <;>
    · have : 2 ^ r ≤ 2 ^ 19 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

end OcamlPq.MLDSAAlg
