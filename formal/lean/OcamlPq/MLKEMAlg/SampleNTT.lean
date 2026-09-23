import OcamlPq.MLKEMAlg.Params

/-!
# `sample_ntt` refines FIPS 203 Algorithm 7

`sample_ntt rho i j` (lib/mlkem_engine.ml:309-334) does not squeeze the XOF
three bytes at a time as FIPS 203 Algorithm 7 does. It asks SHAKE128 for an
840-byte prefix, runs the rejection loop over that prefix, and if fewer than
256 coefficients were accepted it starts again with twice as many bytes.

Specification: Algorithm 7 run on the SHAKE128 output stream `X` of
`ρ ‖ j ‖ i`. The spec is partial: it has no result if the stream never yields
256 accepted candidates. `Spec.sampleNTT` returns `none` in that case.

Main results:

* `sampleNtt_spec`: for byte-sized `i, j`, `sample_ntt` returns exactly when
  Algorithm 7 terminates, and then returns Algorithm 7's result with canonical
  coefficients.
* `sampleNtt_portable`: if Algorithm 7 terminates after `T` iterations, the
  largest `output_length` the recursion reaches is at most `max 840 (6T)`.
  Every `int` in `draw` is therefore portable when `12 T < 2^30`.
* `extract_d1`, `extract_d2`: the 12-bit candidate extraction.
-/

namespace OcamlPq.MLKEMAlg

/-! ## Specification: FIPS 203 Algorithm 7 over the XOF stream -/

namespace Spec

/-- The loop state of Algorithm 7: the counter `j` and the array `â`. FIPS 203
    leaves `â` uninitialised; it starts at `0` here. Every entry is written
    before the algorithm returns, so the choice does not matter. -/
structure SNState where
  j : ℕ
  a : Poly

/-- The body of the `while j < 256` loop of Algorithm 7, given the three bytes
    `C = XOF.Squeeze(ctx, 3)` and the loop guard `j < 256`. -/
def sampleNTTBody (st : SNState) (hj : st.j < 256) (C0 C1 C2 : ℕ) : SNState :=
  let d1 := C0 + 256 * (C1 % 16)
  let d2 := C1 / 16 + 16 * C2
  let st' : SNState :=
    if d1 < q then ⟨st.j + 1, Function.update st.a ⟨st.j, hj⟩ (d1 : ZMod q)⟩ else st
  if h : d2 < q ∧ st'.j < 256 then
    ⟨st'.j + 1, Function.update st'.a ⟨st'.j, h.2⟩ (d2 : ZMod q)⟩
  else st'

/-- The loop of Algorithm 7 run for at most `fuel` iterations on the stream `X`
    starting at stream position `pos`: `some â` if the loop exits, `none` if
    the fuel ran out first. -/
def sampleNTTLoop (X : ℕ → Byte) : ℕ → SNState → ℕ → Option Poly
  | 0, st, _ => if st.j < 256 then none else some st.a
  | fuel + 1, st, pos =>
    if hj : st.j < 256 then
      sampleNTTLoop X fuel (sampleNTTBody st hj (X pos).val (X (pos + 1)).val (X (pos + 2)).val)
        (pos + 3)
    else some st.a

/-- The initial state `j = 0`. -/
def snInit : SNState := ⟨0, 0⟩

open Classical in
/-- FIPS 203 Algorithm 7, `SampleNTT(B)`, with XOF = SHAKE128: the value the
    loop exits with, or `none` if it never exits. -/
noncomputable def sampleNTT (K : Keccak) (B : Bytes) : Option Poly :=
  if h : ∃ fuel a, sampleNTTLoop (K.shake128 B) fuel snInit 0 = some a then
    sampleNTTLoop (K.shake128 B) (Nat.find h) snInit 0
  else none

/-- The loop state after `t` iterations. Once `j = 256` the loop has exited,
    and the state no longer changes. -/
def stateAfter (X : ℕ → Byte) : ℕ → SNState
  | 0 => snInit
  | t + 1 =>
    let st := stateAfter X t
    if hj : st.j < 256 then
      sampleNTTBody st hj (X (3 * t)).val (X (3 * t + 1)).val (X (3 * t + 2)).val
    else st

end Spec

/-! ## Model -/

/-- The loop state of `draw` (lib/mlkem_engine.ml:317-331): `out`, `!count`
    and `!off`. -/
structure DrawState where
  out : IPoly
  count : ℕ
  off : ℕ

/-- One `if d < q && !count < n then begin Array.unsafe_set out !count d;
    incr count end` block of `draw` (lib/mlkem_engine.ml:324-331), acting on
    `(out, !count)`. The loop body contains two copies, for `d1` and `d2`. -/
def acceptCandidate (d : ℕ) (oc : IPoly × ℕ) : IPoly × ℕ :=
  if h : d < q ∧ oc.2 < n then (Function.update oc.1 ⟨oc.2, h.2⟩ (d : ℤ), oc.2 + 1) else oc

/-- One iteration of the `while` loop in `draw` (lib/mlkem_engine.ml:321-330).
    `get` is `get_u8 stream`. All values are non-negative and at most 16 bits
    wide (`draw_portable`), so they are modelled in `ℕ`. -/
def drawBody (get : ℕ → ℕ) (st : DrawState) : DrawState :=
  let d1 := (get st.off ||| (get (st.off + 1) <<< 8)) &&& 0xfff
  let d2 := (get (st.off + 1) ||| (get (st.off + 2) <<< 8)) >>> 4
  let off := st.off + 3
  let oc := acceptCandidate d2 (acceptCandidate d1 (st.out, st.count))
  ⟨oc.1, oc.2, off⟩

@[simp] theorem drawBody_off (get : ℕ → ℕ) (st : DrawState) : (drawBody get st).off = st.off + 3 :=
  rfl

/-- `while !count < n && !off + 2 < output_length do ... done`
    (lib/mlkem_engine.ml:321-331). -/
def drawLoop (get : ℕ → ℕ) (L : ℕ) (st : DrawState) : DrawState :=
  if _h : st.count < n ∧ st.off + 2 < L then drawLoop get L (drawBody get st) else st
termination_by L - st.off
decreasing_by simp only [drawBody_off]; omega

/-- One call `draw output_length` up to the recursive call
    (lib/mlkem_engine.ml:316-332): `some out` if `!count = n`, `none` if `draw`
    recurses. -/
def drawOnce (K : Keccak) (input : Bytes) (L : ℕ) : Option IPoly :=
  let stream := K.shake128Out L input
  let st := drawLoop (getU8 stream) L ⟨polyZero, 0, 0⟩
  if st.count = n then some st.out else none

/-- Big-step semantics of the recursive `draw` (lib/mlkem_engine.ml:316-333):
    `DrawReturns K input L p` holds iff `draw L` returns `p`. -/
inductive DrawReturns (K : Keccak) (input : Bytes) : ℕ → IPoly → Prop
  | done {L : ℕ} {p : IPoly} : drawOnce K input L = some p → DrawReturns K input L p
  | retry {L : ℕ} {p : IPoly} : drawOnce K input L = none → DrawReturns K input (L * 2) p →
      DrawReturns K input L p

/-- The input `rho ^ String.make 1 (Char.unsafe_chr i) ^ String.make 1 (Char.unsafe_chr j)`
    (lib/mlkem_engine.ml:310). -/
def sampleNttInput (rho : Bytes) (i j : ℕ) : Bytes := rho ++ byteString i ++ byteString j

open Classical in
/-- `sample_ntt rho i j` (lib/mlkem_engine.ml:309-334): the value `draw 840`
    returns, or `none` if the recursion does not return. -/
noncomputable def sampleNtt (K : Keccak) (rho : Bytes) (i j : ℕ) : Option IPoly :=
  if h : ∃ p, DrawReturns K (sampleNttInput rho i j) 840 p then some (Classical.choose h) else none

/-! ## Candidate extraction -/

theorem or_shift8 (a b : ℕ) (ha : a < 256) : a ||| (b <<< 8) = a + 256 * b := by
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : a < 2 ^ 8), Nat.shiftLeft_eq]
  ring

/-- `d1 = C[0] + 256 · (C[1] mod 16)`. -/
theorem extract_d1 (b0 b1 : ℕ) (h0 : b0 < 256) :
    (b0 ||| (b1 <<< 8)) &&& 0xfff = b0 + 256 * (b1 % 16) := by
  rw [or_shift8 _ _ h0, show (0xfff : ℕ) = 2 ^ 12 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `d2 = ⌊C[1] / 16⌋ + 16 · C[2]`. -/
theorem extract_d2 (b1 b2 : ℕ) (h1 : b1 < 256) :
    (b1 ||| (b2 <<< 8)) >>> 4 = b1 / 16 + 16 * b2 := by
  rw [or_shift8 _ _ h1, Nat.shiftRight_eq_div_pow]
  omega

/-! ## The implementation as an iteration over the stream -/

section Iteration

variable (X : ℕ → Byte)

/-- Reading the SHAKE128 stream. -/
def getX : ℕ → ℕ := fun p => (X p).val

/-- `t` iterations of the loop body of `draw`, reading from the unbounded stream. -/
def implAfter : ℕ → DrawState
  | 0 => ⟨polyZero, 0, 0⟩
  | t + 1 => drawBody (getX X) (implAfter t)

theorem implAfter_off (t : ℕ) : (implAfter X t).off = 3 * t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [implAfter, ih]; ring

theorem acceptCandidate_count_le (d : ℕ) (oc : IPoly × ℕ) (h : oc.2 ≤ n) :
    (acceptCandidate d oc).2 ≤ n := by
  unfold acceptCandidate
  split_ifs with h'
  · exact h'.2
  · exact h

theorem acceptCandidate_full (d : ℕ) (oc : IPoly × ℕ) (h : oc.2 = n) : acceptCandidate d oc = oc := by
  unfold acceptCandidate; rw [dite_eq_right (by omega)]

theorem drawBody_count_le (get : ℕ → ℕ) (st : DrawState) (h : st.count ≤ n) :
    (drawBody get st).count ≤ n :=
  acceptCandidate_count_le _ _ (acceptCandidate_count_le _ _ h)

theorem implAfter_count_le (t : ℕ) : (implAfter X t).count ≤ n := by
  induction t with
  | zero => simp [implAfter]
  | succ t ih => exact drawBody_count_le _ _ ih

/-- Once 256 coefficients are accepted, the body only advances `off`. -/
theorem drawBody_full (get : ℕ → ℕ) (st : DrawState) (h : st.count = n) :
    (drawBody get st).count = n ∧ (drawBody get st).out = st.out := by
  simp only [drawBody]
  rw [acceptCandidate_full _ (st.out, st.count) h, acceptCandidate_full _ (st.out, st.count) h]
  exact ⟨h, rfl⟩

theorem implAfter_stable (t : ℕ) (h : (implAfter X t).count = n) (s : ℕ) :
    (implAfter X (t + s)).count = n ∧ (implAfter X (t + s)).out = (implAfter X t).out := by
  induction s with
  | zero => exact ⟨h, rfl⟩
  | succ s ih =>
    obtain ⟨h1, h2⟩ := drawBody_full (getX X) (implAfter X (t + s)) ih.1
    exact ⟨h1, h2.trans ih.2⟩

/-- `drawLoop` only reads positions below `L`. -/
theorem drawLoop_congr (get get' : ℕ → ℕ) (L : ℕ) (hg : ∀ p < L, get p = get' p) (st : DrawState) :
    drawLoop get L st = drawLoop get' L st := by
  induction st using drawLoop.induct get L with
  | case1 st h ih =>
    rw [drawLoop.eq_1 get L st, drawLoop.eq_1 get' L st, dite_eq_left h, dite_eq_left h]
    have : drawBody get st = drawBody get' st := by
      unfold drawBody
      rw [hg st.off (by omega), hg (st.off + 1) (by omega), hg (st.off + 2) (by omega)]
    rw [← this]; exact ih
  | case2 st h =>
    rw [drawLoop.eq_1 get L st, drawLoop.eq_1 get' L st, dite_eq_right h, dite_eq_right h]

/-- Running the `while` loop on a prefix of `3m` bytes ends in the state that
    `m` iterations over the unbounded stream reach. -/
theorem drawLoop_implAfter (m t : ℕ) (ht : t ≤ m) :
    (drawLoop (getX X) (3 * m) (implAfter X t)).count = (implAfter X m).count ∧
    (drawLoop (getX X) (3 * m) (implAfter X t)).out = (implAfter X m).out := by
  induction h : m - t generalizing t with
  | zero =>
    have : t = m := by omega
    subst this
    rw [drawLoop.eq_1, dite_eq_right (by rw [implAfter_off]; omega)]
    exact ⟨rfl, rfl⟩
  | succ d ih =>
    rw [drawLoop.eq_1]
    by_cases hc : (implAfter X t).count < n
    · rw [dite_eq_left ⟨hc, by rw [implAfter_off]; omega⟩]
      exact ih (t + 1) (by omega) (by omega)
    · rw [dite_eq_right (by tauto)]
      have hn : (implAfter X t).count = n := le_antisymm (implAfter_count_le X t) (by omega)
      obtain ⟨h1, h2⟩ := implAfter_stable X t hn (m - t)
      rw [show t + (m - t) = m by omega] at h1 h2
      exact ⟨by rw [h1, hn], h2.symm⟩

theorem getU8_shake128Out (K : Keccak) (L : ℕ) (input : Bytes) (p : ℕ) (hp : p < L) :
    getU8 (K.shake128Out L input) p = getX (K.shake128 input) p := by
  rw [getU8_of_lt (by simpa using hp)]
  simp [Keccak.shake128Out, getX]

/-- `draw` on an output length that is a multiple of 3 returns the state after
    `m` iterations over the unbounded stream, provided it has 256 coefficients. -/
theorem drawOnce_eq (K : Keccak) (input : Bytes) (m : ℕ) :
    drawOnce K input (3 * m) =
      if (implAfter (K.shake128 input) m).count = n then some (implAfter (K.shake128 input) m).out
      else none := by
  unfold drawOnce
  dsimp only
  rw [drawLoop_congr _ (getX (K.shake128 input)) _ (getU8_shake128Out K _ input)]
  have := drawLoop_implAfter (K.shake128 input) m 0 (Nat.zero_le _)
  simp only [implAfter] at this
  rw [this.1, this.2]

end Iteration

/-! ## Relating the implementation's iteration to Algorithm 7 -/

/-- The representation relation between loop states. -/
def DrawRel (st : DrawState) (sst : Spec.SNState) : Prop :=
  st.count = sst.j ∧ Canonical st.out ∧ toSpec st.out = sst.a

theorem toSpec_update (p : IPoly) (i : Fin 256) (v : ℤ) :
    toSpec (Function.update p i v) = Function.update (toSpec p) i (v : ZMod q) := by
  funext x
  by_cases hx : x = i
  · subst hx; simp [toSpec]
  · simp [toSpec, Function.update_of_ne hx]

theorem canonical_update {p : IPoly} (hp : Canonical p) (i : Fin 256) {v : ℤ} (h0 : 0 ≤ v)
    (h1 : v < q) : Canonical (Function.update p i v) := by
  intro x
  by_cases hx : x = i
  · subst hx; simp only [Function.update_self]; exact ⟨h0, h1⟩
  · simp only [Function.update_of_ne hx]; exact hp x

/-- The representation relation on `(out, !count)`. -/
def OCRel (oc : IPoly × ℕ) (sst : Spec.SNState) : Prop :=
  oc.2 = sst.j ∧ Canonical oc.1 ∧ toSpec oc.1 = sst.a

/-- The `d1` block refines `if d1 < q then â[j] ← d1; j ← j + 1`. -/
theorem OCRel.accept_d1 {oc : IPoly × ℕ} {sst : Spec.SNState} (hR : OCRel oc sst)
    (hj : sst.j < 256) (d : ℕ) :
    OCRel (acceptCandidate d oc)
      (if d < q then ⟨sst.j + 1, Function.update sst.a ⟨sst.j, hj⟩ (d : ZMod q)⟩ else sst) := by
  obtain ⟨hc, hcan, hspec⟩ := hR
  unfold acceptCandidate
  by_cases hd : d < q
  · rw [dite_eq_left ⟨hd, by rw [hc]; exact hj⟩, ite_eq_left hd]
    refine ⟨by simp [hc], canonical_update hcan _ (by omega) (by exact_mod_cast hd), ?_⟩
    simp only [toSpec_update, hspec, Int.cast_natCast]
    congr 2
  · rw [dite_eq_right (by tauto), ite_eq_right hd]
    exact ⟨hc, hcan, hspec⟩

/-- The `d2` block refines `if d2 < q and j < 256 then â[j] ← d2; j ← j + 1`. -/
theorem OCRel.accept_d2 {oc : IPoly × ℕ} {sst : Spec.SNState} (hR : OCRel oc sst) (d : ℕ) :
    OCRel (acceptCandidate d oc)
      (if h : d < q ∧ sst.j < 256 then ⟨sst.j + 1, Function.update sst.a ⟨sst.j, h.2⟩ (d : ZMod q)⟩
        else sst) := by
  obtain ⟨hc, hcan, hspec⟩ := hR
  unfold acceptCandidate
  by_cases hd : d < q ∧ sst.j < 256
  · rw [dite_eq_left ⟨hd.1, by rw [hc]; exact hd.2⟩, dite_eq_left hd]
    refine ⟨by simp [hc], canonical_update hcan _ (by omega) (by exact_mod_cast hd.1), ?_⟩
    simp only [toSpec_update, hspec, Int.cast_natCast]
    congr 2
  · rw [dite_eq_right (by rw [hc]; exact hd), dite_eq_right hd]
    exact ⟨hc, hcan, hspec⟩

theorem drawRel_step (get : ℕ → ℕ) (st : DrawState) (sst : Spec.SNState) (hR : DrawRel st sst)
    (hj : sst.j < 256) (h0 : get st.off < 256) (h1 : get (st.off + 1) < 256) :
    DrawRel (drawBody get st)
      (Spec.sampleNTTBody sst hj (get st.off) (get (st.off + 1)) (get (st.off + 2))) := by
  have hR' : OCRel (st.out, st.count) sst := ⟨hR.1, hR.2.1, hR.2.2⟩
  have := (hR'.accept_d1 hj (get st.off + 256 * (get (st.off + 1) % 16))).accept_d2
    (get (st.off + 1) / 16 + 16 * get (st.off + 2))
  simp only [drawBody, extract_d1 _ _ h0, extract_d2 _ _ h1]
  exact this

theorem drawRel_implAfter (X : ℕ → Byte) (t : ℕ) : DrawRel (implAfter X t) (Spec.stateAfter X t) := by
  induction t with
  | zero => exact ⟨rfl, polyZero_canonical, by simp [implAfter, Spec.stateAfter, Spec.snInit]⟩
  | succ t ih =>
    simp only [implAfter, Spec.stateAfter]
    by_cases hj : (Spec.stateAfter X t).j < 256
    · rw [dite_eq_left hj]
      have h := drawRel_step (getX X) _ _ ih hj (X _).isLt (X _).isLt
      rw [implAfter_off] at h
      exact h
    · rw [dite_eq_right hj]
      have hn : (implAfter X t).count = n := by
        have h1 := implAfter_count_le X t; have h2 := ih.1; have := n_eq; omega
      obtain ⟨h1, h2⟩ := drawBody_full (getX X) _ hn
      exact ⟨by rw [h1, ← hn, ih.1], by rw [h2]; exact ih.2.1, by rw [h2]; exact ih.2.2⟩

/-! ## Algorithm 7 in terms of `stateAfter` -/

theorem stateAfter_stable (X : ℕ → Byte) (t : ℕ) (h : 256 ≤ (Spec.stateAfter X t).j) (s : ℕ) :
    Spec.stateAfter X (t + s) = Spec.stateAfter X t := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [← Nat.add_assoc, Spec.stateAfter]
    rw [ih, dite_eq_right (by omega)]

theorem sampleNTTLoop_stateAfter (X : ℕ → Byte) (fuel t : ℕ) :
    Spec.sampleNTTLoop X fuel (Spec.stateAfter X t) (3 * t) =
      if (Spec.stateAfter X (t + fuel)).j < 256 then none
      else some (Spec.stateAfter X (t + fuel)).a := by
  induction fuel generalizing t with
  | zero => rfl
  | succ fuel ih =>
    rw [Spec.sampleNTTLoop]
    by_cases hj : (Spec.stateAfter X t).j < 256
    · rw [dite_eq_left hj]
      have : Spec.sampleNTTBody (Spec.stateAfter X t) hj (X (3 * t)).val (X (3 * t + 1)).val
          (X (3 * t + 2)).val = Spec.stateAfter X (t + 1) := by
        rw [Spec.stateAfter, dite_eq_left hj]
      rw [this, show 3 * t + 3 = 3 * (t + 1) by ring, ih, show t + 1 + fuel = t + (fuel + 1) by ring]
    · rw [dite_eq_right hj, stateAfter_stable X t (by omega), ite_eq_right hj]

/-- Algorithm 7 has a result iff some iteration count reaches `j = 256`, and
    then the result is the array at any such iteration count. -/
theorem sampleNTT_eq_some_iff (K : Keccak) (B : Bytes) (a : Poly) :
    Spec.sampleNTT K B = some a ↔
      ∃ T, 256 ≤ (Spec.stateAfter (K.shake128 B) T).j ∧ (Spec.stateAfter (K.shake128 B) T).a = a := by
  have hloop : ∀ fuel, Spec.sampleNTTLoop (K.shake128 B) fuel Spec.snInit 0 =
      if (Spec.stateAfter (K.shake128 B) fuel).j < 256 then none
      else some (Spec.stateAfter (K.shake128 B) fuel).a := by
    intro fuel
    have := sampleNTTLoop_stateAfter (K.shake128 B) fuel 0
    simpa [Spec.stateAfter] using this
  -- any two terminating iteration counts give the same array
  have huniq : ∀ T T', 256 ≤ (Spec.stateAfter (K.shake128 B) T).j →
      256 ≤ (Spec.stateAfter (K.shake128 B) T').j →
      (Spec.stateAfter (K.shake128 B) T).a = (Spec.stateAfter (K.shake128 B) T').a := by
    intro T T' h h'
    rcases le_total T T' with hle | hle
    · rw [← stateAfter_stable _ T h (T' - T), Nat.add_sub_cancel' hle]
    · rw [← stateAfter_stable _ T' h' (T - T'), Nat.add_sub_cancel' hle]
  unfold Spec.sampleNTT
  constructor
  · intro hs
    split_ifs at hs with h
    have hfind := hloop (Nat.find h)
    rw [hs] at hfind
    split_ifs at hfind with hlt
    exact ⟨Nat.find h, by omega, (Option.some.inj hfind).symm⟩
  · rintro ⟨T, hT, rfl⟩
    have hex : ∃ fuel a, Spec.sampleNTTLoop (K.shake128 B) fuel Spec.snInit 0 = some a :=
      ⟨T, _, by rw [hloop, ite_eq_right (by omega)]⟩
    rw [dite_eq_left hex, hloop]
    have hspec := Nat.find_spec hex
    obtain ⟨a', ha'⟩ := hspec
    rw [hloop] at ha'
    split_ifs at ha' with hlt
    rw [ite_eq_right hlt, huniq _ _ (by omega) hT]

/-! ## Main theorem -/

section Main

variable (K : Keccak) (input : Bytes)

local notation "X" => K.shake128 input

theorem drawOnce_840 (e : ℕ) :
    drawOnce K input (840 * 2 ^ e) =
      if (implAfter X (280 * 2 ^ e)).count = n then some (implAfter X (280 * 2 ^ e)).out else none := by
  rw [show 840 * 2 ^ e = 3 * (280 * 2 ^ e) by ring, drawOnce_eq]

/-- Every value `draw 840` can return is the stream result. -/
theorem drawReturns_sound {L : ℕ} {p : IPoly} (h : DrawReturns K input L p) :
    ∀ e, L = 840 * 2 ^ e → ∃ T, (implAfter X T).count = n ∧ (implAfter X T).out = p := by
  induction h with
  | done hd =>
    intro e hL
    subst hL
    rw [drawOnce_840] at hd
    split_ifs at hd with hc
    exact ⟨_, hc, Option.some.inj hd⟩
  | retry _ _ ih =>
    intro e hL
    exact ih (e + 1) (by rw [hL, pow_succ]; ring)

/-- If the stream reaches 256 coefficients after `T` iterations, then `draw`
    started at `840 · 2^e` returns, for every `e`. -/
theorem drawReturns_complete (T : ℕ) (hT : (implAfter X T).count = n) :
    ∀ d e, T ≤ 280 * 2 ^ (e + d) → DrawReturns K input (840 * 2 ^ e) (implAfter X T).out := by
  intro d
  induction d with
  | zero =>
    intro e he
    apply DrawReturns.done
    rw [drawOnce_840]
    obtain ⟨h1, h2⟩ := implAfter_stable X T hT (280 * 2 ^ e - T)
    rw [Nat.add_sub_cancel' (by simpa using he)] at h1 h2
    rw [ite_eq_left h1, h2]
  | succ d ih =>
    intro e he
    by_cases hc : (implAfter X (280 * 2 ^ e)).count = n
    · apply DrawReturns.done
      rw [drawOnce_840, ite_eq_left hc]
      congr 1
      rcases le_total T (280 * 2 ^ e) with hle | hle
      · obtain ⟨-, h2⟩ := implAfter_stable X T hT (280 * 2 ^ e - T)
        rw [Nat.add_sub_cancel' hle] at h2; exact h2
      · obtain ⟨-, h2⟩ := implAfter_stable X _ hc (T - 280 * 2 ^ e)
        rw [Nat.add_sub_cancel' hle] at h2; exact h2.symm
    · apply DrawReturns.retry
      · rw [drawOnce_840, ite_eq_right hc]
      · rw [show 840 * 2 ^ e * 2 = 840 * 2 ^ (e + 1) by ring]
        exact ih (e + 1) (by rw [show e + 1 + d = e + (d + 1) by ring]; exact he)

/-- `draw 840` can return at most one value. -/
theorem drawReturns_unique {p p' : IPoly} (h : DrawReturns K input 840 p)
    (h' : DrawReturns K input 840 p') : p = p' := by
  obtain ⟨T, hT, rfl⟩ := drawReturns_sound K input h 0 (by simp)
  obtain ⟨T', hT', rfl⟩ := drawReturns_sound K input h' 0 (by simp)
  rcases le_total T T' with hle | hle
  · obtain ⟨-, h2⟩ := implAfter_stable _ T hT (T' - T)
    rw [Nat.add_sub_cancel' hle] at h2; exact h2.symm
  · obtain ⟨-, h2⟩ := implAfter_stable _ T' hT' (T - T')
    rw [Nat.add_sub_cancel' hle] at h2; exact h2

theorem exists_pow_ge (T : ℕ) : ∃ d, T ≤ 280 * 2 ^ d :=
  ⟨T, by have := Nat.lt_two_pow_self (n := T); omega⟩

end Main

/-- The model `sampleNtt` is the big-step semantics of `draw 840`. -/
theorem sampleNtt_eq_some_iff (K : Keccak) (rho : Bytes) (i j : ℕ) (p : IPoly) :
    sampleNtt K rho i j = some p ↔ DrawReturns K (sampleNttInput rho i j) 840 p := by
  unfold sampleNtt
  split_ifs with h
  · constructor
    · rintro hp; rw [← Option.some.inj hp]; exact Classical.choose_spec h
    · intro hp; rw [drawReturns_unique K _ (Classical.choose_spec h) hp]
  · simp only [false_iff]
    exact fun hp => h ⟨p, hp⟩

/-- **Obligation 2.** For byte-sized `i` and `j`, `sample_ntt rho i j` returns
    iff FIPS 203 Algorithm 7 on `ρ ‖ i ‖ j` terminates, and then it returns
    Algorithm 7's result, with canonical coefficients. -/
theorem sampleNtt_spec (K : Keccak) (rho : Bytes) (i j : ℕ) (hi : i < 256) (hj : j < 256) :
    (sampleNtt K rho i j).map toSpec = Spec.sampleNTT K (rho ++ [⟨i, hi⟩, ⟨j, hj⟩]) ∧
      ∀ p, sampleNtt K rho i j = some p → Canonical p := by
  have hin : sampleNttInput rho i j = rho ++ [⟨i, hi⟩, ⟨j, hj⟩] := by
    simp only [sampleNttInput, byteString, List.append_assoc, List.singleton_append]
    rw [show unsafeChr (i : ℤ) = ⟨i, hi⟩ from Fin.ext (unsafeChr_val_nat hi),
      show unsafeChr (j : ℤ) = ⟨j, hj⟩ from Fin.ext (unsafeChr_val_nat hj)]
  set input := sampleNttInput rho i j
  rw [← hin]
  -- every returned value is the stream result
  have hsound : ∀ p, DrawReturns K input 840 p →
      Canonical p ∧ Spec.sampleNTT K input = some (toSpec p) := by
    intro p hp
    obtain ⟨T, hT, rfl⟩ := drawReturns_sound K input hp 0 (by simp)
    obtain ⟨hc, hcan, hspec⟩ := drawRel_implAfter (K.shake128 input) T
    have := n_eq
    refine ⟨hcan, (sampleNTT_eq_some_iff K input _).2 ⟨T, by omega, hspec.symm⟩⟩
  unfold sampleNtt
  split_ifs with h
  · have hs := hsound _ (Classical.choose_spec h)
    refine ⟨by rw [Option.map_some, hs.2], ?_⟩
    rintro p hp
    rw [← Option.some.inj hp]; exact hs.1
  · refine ⟨?_, by simp⟩
    rw [Option.map_none]
    symm
    by_contra hne
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hne
    obtain ⟨T, hT, -⟩ := (sampleNTT_eq_some_iff K input a).1 ha
    have hc : (implAfter (K.shake128 input) T).count = n := by
      have h1 := (drawRel_implAfter (K.shake128 input) T).1
      have h2 := implAfter_count_le (K.shake128 input) T
      have := n_eq
      omega
    obtain ⟨d, hd⟩ := exists_pow_ge T
    exact h ⟨_, by simpa using drawReturns_complete K input T hc d 0 (by simpa using hd)⟩

/-- **Termination and portability of the restart.** If Algorithm 7 terminates
    after `T` iterations on the stream, then `draw` never recurses past an
    `output_length` of `max 840 (6T)`. If `12 T < 2^30`, every
    `output_length` the recursion computes (including the doubled value) is
    therefore a portable `int`. For `T ≤ 280` (the initial 840-byte prefix
    suffices), no recursion happens at all. -/
theorem sampleNtt_portable (K : Keccak) (input : Bytes) (T : ℕ)
    (hT : 256 ≤ (Spec.stateAfter (K.shake128 input) T).j) (e : ℕ)
    (hprev : ∀ e' < e, drawOnce K input (840 * 2 ^ e') = none) :
    840 * 2 ^ e ≤ max 840 (6 * T) := by
  have hc : (implAfter (K.shake128 input) T).count = n := by
    have h1 := (drawRel_implAfter (K.shake128 input) T).1
    have h2 := implAfter_count_le (K.shake128 input) T
    have := n_eq
    omega
  cases e with
  | zero => simp
  | succ e =>
    have hnone := hprev e (by omega)
    rw [drawOnce_840, ite_eq_right_iff] at hnone
    -- the prefix of 280 · 2^e triples was too short, so T > 280 · 2^e
    have hlt : 280 * 2 ^ e < T := by
      by_contra hge
      obtain ⟨h1, -⟩ := implAfter_stable (K.shake128 input) T hc (280 * 2 ^ e - T)
      rw [Nat.add_sub_cancel' (by omega)] at h1
      exact absurd (hnone h1) (by simp)
    rw [pow_succ]
    omega

/-- The `int` intermediates of one iteration of `draw` are portable: bytes are
    below 256, `d1` and `d2` below `2^16`, and `off + 2 < output_length`
    bounds the reads, so they stay in range of the SHAKE128 output. -/
theorem draw_portable (b0 b1 b2 : ℕ) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) :
    Portable (((b0 ||| (b1 <<< 8)) &&& 0xfff : ℕ) : ℤ) ∧
    Portable (((b1 ||| (b2 <<< 8)) >>> 4 : ℕ) : ℤ) ∧
    Portable (((b0 ||| (b1 <<< 8)) : ℕ) : ℤ) ∧ Portable (((b1 ||| (b2 <<< 8)) : ℕ) : ℤ) := by
  rw [extract_d1 _ _ h0, extract_d2 _ _ h1, or_shift8 _ _ h0, or_shift8 _ _ h1]
  refine ⟨Portable.of_nat_lt ?_, Portable.of_nat_lt ?_, Portable.of_nat_lt ?_,
    Portable.of_nat_lt ?_⟩ <;> omega

/-! ## Total extension, used by the composition -/

/-- `sample_ntt` as a total function: its result, or the zero polynomial if
    it does not return. The composition theorems use this. `sampleNtt_spec`
    shows that `sample_ntt` diverges on exactly the inputs where Algorithm 7
    diverges, so on every terminating run this is what `sample_ntt` returns. -/
noncomputable def sampleNttTotal (K : Keccak) (rho : Bytes) (i j : ℕ) : IPoly :=
  (sampleNtt K rho i j).getD polyZero

/-- Algorithm 7 as a total function (0 if the loop does not terminate). -/
noncomputable def Spec.sampleNTTTotal (K : Keccak) (B : Bytes) : Poly := (Spec.sampleNTT K B).getD 0

theorem sampleNttTotal_spec (K : Keccak) (rho : Bytes) (i j : ℕ) (hi : i < 256) (hj : j < 256) :
    Canonical (sampleNttTotal K rho i j) ∧
      toSpec (sampleNttTotal K rho i j) = Spec.sampleNTTTotal K (rho ++ [⟨i, hi⟩, ⟨j, hj⟩]) := by
  obtain ⟨h1, h2⟩ := sampleNtt_spec K rho i j hi hj
  unfold sampleNttTotal Spec.sampleNTTTotal
  rw [← h1]
  cases hs : sampleNtt K rho i j with
  | none => exact ⟨polyZero_canonical, by simp⟩
  | some p => exact ⟨h2 p hs, rfl⟩

end OcamlPq.MLKEMAlg
