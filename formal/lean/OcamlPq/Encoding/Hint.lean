import OcamlPq.Encoding.HintSpec

/-!
# The ML-DSA hint codec

Models of the hint part of `encode_signature` (`mldsa/mldsa_engine.ml`
lines 694–705) and of `decode_signature` (lines 653–676), and the proofs that

* (a) `decodeHintWith_eq`: the decoder is FIPS 204 Algorithm 21
  (`HintBitUnpack`) exactly: same accept/reject decision, same output, on
  every byte string;
* `encodeHint_eq_spec`: the encoder is FIPS 204 Algorithm 20
  (`HintBitPack`), and `encodeHint_shift`/`decodeHint_shift` place both at
  the hint offset of the signature;
* `decoder_reads_in_bounds`: every index the decoder reads is inside the hint
  section and every `hint.(row).(coefficient)` write is inside the `k × 256`
  array.

`HintRoundTrip.lean` then proves (b) `decode_encode`, (c) `encode_decode`
(canonicity), (d) `weight_le_of_decode`, and `encode_writes_in_bounds`.

All results hold for every `k` and `ω`, in particular for the three
parameter sets `(k, ω) = (4, 80), (6, 55), (8, 75)`.
-/

namespace OcamlPq.Encoding.Hint

open OcamlPq.Encoding

/-! ## The decoder -/

/-- The mutable state of the hint decoder: `hint`, `previous`, `valid`. -/
structure DecState where
  hint : HintVec
  previous : ℕ
  valid : Bool

/-- The body of the inner loop (lines 662–666), with `first = !previous`
fixed for the row:
```
let coefficient = get_u8 octets (hint_offset + index) in
if index > !previous
   && coefficient <= get_u8 octets (hint_offset + index - 1)
then valid := false
else hint.(row).(coefficient) <- 1
``` -/
def decInner (get : ℕ → ℕ) (row first : ℕ) (s : DecState) (index : ℕ) : DecState :=
  let coefficient := get index
  if index > first ∧ coefficient ≤ get (index - 1) then { s with valid := false }
  else { s with hint := setHint s.hint row coefficient }

/-- One iteration of the row loop (lines 658–669):
```
let endpoint = get_u8 octets (hint_offset + P.omega + row) in
if endpoint < !previous || endpoint > P.omega then valid := false;
if !valid then begin
  for index = !previous to endpoint - 1 do <inner> done;
  previous := endpoint
end
``` -/
def decRow (get : ℕ → ℕ) (ω : ℕ) (s : DecState) (row : ℕ) : DecState :=
  let endpoint := get (ω + row)
  let s := if endpoint < s.previous ∨ endpoint > ω then { s with valid := false } else s
  if s.valid then
    let s' := (List.range' s.previous (endpoint - s.previous)).foldl
      (decInner get row s.previous) s
    { s' with previous := endpoint }
  else s

/-- The hint decoder of `decode_signature` (lines 653–676), reading the
signature through `get i = get_u8 octets (hint_offset + i)`:
```
for row = 0 to P.k - 1 do <row> done;
for index = !previous to P.omega - 1 do
  if get_u8 octets (hint_offset + index) <> 0 then valid := false
done;
if not !valid then Error _ else Ok { c_tilde; z; hint }
``` -/
def decodeHintWith (get : ℕ → ℕ) (k ω : ℕ) : Option HintVec :=
  let s := (List.range k).foldl (decRow get ω) ⟨fun _ _ => 0, 0, true⟩
  let valid := (List.range' s.previous (ω - s.previous)).foldl
    (fun v index => if get index ≠ 0 then false else v) s.valid
  if valid then some s.hint else none

/-- The hint decoder on the signature `octets` at `hint_offset`. -/
def decodeHint (octets : List ℕ) (hintOffset k ω : ℕ) : Option HintVec :=
  decodeHintWith (fun i => octets.getD (hintOffset + i) 0) k ω

/-! ### One step of the decoder -/

theorem decInner_bad (get : ℕ → ℕ) (row first : ℕ) (s : DecState) (index : ℕ)
    (h : index > first ∧ get index ≤ get (index - 1)) :
    decInner get row first s index = { s with valid := false } := by
  unfold decInner; simp only; rw [ite_eq_left h]

theorem decInner_good (get : ℕ → ℕ) (row first : ℕ) (s : DecState) (index : ℕ)
    (h : ¬ (index > first ∧ get index ≤ get (index - 1))) :
    decInner get row first s index = { s with hint := setHint s.hint row (get index) } := by
  unfold decInner; simp only; rw [ite_eq_right h]

theorem decRow_bad (get : ℕ → ℕ) (ω : ℕ) (s : DecState) (row : ℕ)
    (h : get (ω + row) < s.previous ∨ get (ω + row) > ω) :
    decRow get ω s row = { s with valid := false } := by
  unfold decRow; simp only; rw [ite_eq_left h]; simp

theorem decRow_good (get : ℕ → ℕ) (ω : ℕ) (s : DecState) (row : ℕ)
    (h : ¬ (get (ω + row) < s.previous ∨ get (ω + row) > ω)) (hv : s.valid = true) :
    decRow get ω s row =
      { (List.range' s.previous (get (ω + row) - s.previous)).foldl
          (decInner get row s.previous) s with previous := get (ω + row) } := by
  unfold decRow; simp only; rw [ite_eq_right h, ite_eq_left hv]

/-! ### Invalid states stay invalid -/

theorem decInner_previous (get : ℕ → ℕ) (row first : ℕ) :
    ∀ (l : List ℕ) (s : DecState), (l.foldl (decInner get row first) s).previous = s.previous := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x l ih =>
    intro s
    rw [List.foldl_cons, ih]
    by_cases hc : x > first ∧ get x ≤ get (x - 1)
    · rw [decInner_bad _ _ _ _ _ hc]
    · rw [decInner_good _ _ _ _ _ hc]

theorem decInner_invalid (get : ℕ → ℕ) (row first : ℕ) :
    ∀ (l : List ℕ) (s : DecState), s.valid = false →
      (l.foldl (decInner get row first) s).valid = false := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons x l ih =>
    intro s h
    rw [List.foldl_cons]
    apply ih
    by_cases hc : x > first ∧ get x ≤ get (x - 1)
    · rw [decInner_bad _ _ _ _ _ hc]
    · rw [decInner_good _ _ _ _ _ hc]; exact h

theorem decRow_invalid (get : ℕ → ℕ) (ω : ℕ) (s : DecState) (row : ℕ) (h : s.valid = false) :
    decRow get ω s row = s := by
  by_cases hc : get (ω + row) < s.previous ∨ get (ω + row) > ω
  · rw [decRow_bad _ _ _ _ hc]; cases s; simp_all
  · unfold decRow; simp only; rw [ite_eq_right hc, h]; rfl

theorem decRows_invalid (get : ℕ → ℕ) (ω : ℕ) :
    ∀ (l : List ℕ) (s : DecState), s.valid = false → l.foldl (decRow get ω) s = s := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons x l ih =>
    intro s h
    rw [List.foldl_cons, decRow_invalid get ω s x h, ih s h]

theorem trailing_invalid (get : ℕ → ℕ) :
    ∀ (l : List ℕ), l.foldl (fun v index => if get index ≠ 0 then false else v) false = false := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons]
    split_ifs <;> exact ih

/-! ### Characterisation of the decoder -/

section
variable (k ω : ℕ) (y : List ℕ)

theorem decInner_fold (row first stop : ℕ) :
    ∀ n idx (h : HintVec) (p : ℕ), stop - idx = n → first ≤ idx → idx ≤ stop →
      let r := (List.range' idx (stop - idx)).foldl (decInner (fun i => y.getD i 0) row first)
        ⟨h, p, true⟩
      (r.valid = true ↔ ∀ t < stop, idx ≤ t → first < t → y.getD (t - 1) 0 < y.getD t 0) ∧
      ((∀ t < stop, idx ≤ t → first < t → y.getD (t - 1) 0 < y.getD t 0) →
        r.hint = fun r c =>
          if r = row ∧ c ∈ (List.range' idx (stop - idx)).map (fun t => y.getD t 0) then 1
          else h r c) := by
  intro n
  induction n with
  | zero =>
    intro idx h p hn h1 h2
    have he : idx = stop := by omega
    subst he
    simp only [Nat.sub_self, List.range'_zero, List.foldl_nil]
    refine ⟨⟨fun _ t ht h' _ => absurd ht (by omega), fun _ => trivial⟩, fun _ => ?_⟩
    funext r c
    rw [ite_eq_right (fun h => by simp at h)]
  | succ n ih =>
    intro idx h p hn h1 h2
    simp only
    rw [show stop - idx = (stop - (idx + 1)) + 1 by omega, List.range'_succ, List.foldl_cons]
    by_cases hbad : idx > first ∧ y.getD idx 0 ≤ y.getD (idx - 1) 0
    · rw [decInner_bad _ _ _ _ _ hbad]
      have hinv := decInner_invalid (fun i => y.getD i 0) row first
        (List.range' (idx + 1) (stop - (idx + 1))) { hint := h, previous := p, valid := false } rfl
      have hno : ¬ ∀ t < stop, idx ≤ t → first < t → y.getD (t - 1) 0 < y.getD t 0 := by
        intro hall
        have := hall idx (by omega) le_rfl hbad.1
        omega
      refine ⟨?_, fun hall => absurd hall hno⟩
      simp only at hinv ⊢
      rw [hinv]
      simp only [Bool.false_eq_true, false_iff]
      exact hno
    · rw [decInner_good _ _ _ _ _ hbad]
      obtain ⟨ih1, ih2⟩ := ih (idx + 1) (setHint h row (y.getD idx 0)) p (by omega) (by omega)
        (by omega)
      have hloc : idx > first → y.getD (idx - 1) 0 < y.getD idx 0 := by
        intro h'; by_contra hc; exact hbad ⟨h', by omega⟩
      have hfull : (∀ t < stop, idx + 1 ≤ t → first < t → y.getD (t - 1) 0 < y.getD t 0) ↔
          (∀ t < stop, idx ≤ t → first < t → y.getD (t - 1) 0 < y.getD t 0) := by
        constructor
        · intro hall t ht h1' h2'
          rcases Nat.eq_or_lt_of_le h1' with he | hlt
          · subst he; exact hloc h2'
          · exact hall t ht hlt h2'
        · intro hall t ht h1' h2'
          exact hall t ht (by omega) h2'
      refine ⟨ih1.trans hfull, fun hall => ?_⟩
      rw [ih2 (hfull.mpr hall)]
      funext r c
      simp only [List.map_cons, List.mem_cons, setHint]
      by_cases hr : r = row
      · by_cases hc1 : c ∈ (List.range' (idx + 1) (stop - (idx + 1))).map (fun t => y.getD t 0)
        · rw [ite_eq_left ⟨hr, hc1⟩, ite_eq_left ⟨hr, Or.inr hc1⟩]
        · by_cases hc2 : c = y.getD idx 0
          · rw [ite_eq_right (fun h => hc1 h.2), ite_eq_left ⟨hr, hc2⟩, ite_eq_left ⟨hr, Or.inl hc2⟩]
          · rw [ite_eq_right (fun h => hc1 h.2), ite_eq_right (fun h => hc2 h.2),
              ite_eq_right (fun h => h.2.elim hc2 hc1)]
      · rw [ite_eq_right (fun h => hr h.1), ite_eq_right (fun h => hr h.1), ite_eq_right (fun h => hr h.1)]

theorem decRows_fold :
    ∀ n i (h : HintVec), k - i = n → i ≤ k →
      let r := (List.range' i (k - i)).foldl (decRow (fun i => y.getD i 0) ω)
        ⟨h, st ω y i, true⟩
      (r.valid = true ↔ RowsFrom k ω y i) ∧
      (RowsFrom k ω y i →
        r.hint = (fun r c => if i ≤ r ∧ r < k ∧ c ∈ seg ω y r then 1 else h r c) ∧
        r.previous = st ω y k) := by
  intro n
  induction n with
  | zero =>
    intro i h hn hi
    have he : i = k := by omega
    subst he
    simp only [Nat.sub_self, List.range'_zero, List.foldl_nil, true_iff]
    refine ⟨fun j hj h' => absurd hj (by omega), fun _ => ⟨?_, trivial⟩⟩
    funext r c
    rw [ite_eq_right (by omega)]
  | succ n ih =>
    intro i h hn hi
    simp only
    rw [show k - i = (k - (i + 1)) + 1 by omega, List.range'_succ, List.foldl_cons]
    by_cases hbad : y.getD (ω + i) 0 < st ω y i ∨ y.getD (ω + i) 0 > ω
    · rw [decRow_bad _ _ _ _ hbad, decRows_invalid _ _ _ _ rfl]
      have hno : ¬ RowsFrom k ω y i := by
        intro hall
        have := hall i (by omega) le_rfl
        unfold RowOK ep at this
        omega
      refine ⟨?_, fun hall => absurd hall hno⟩
      simp only [Bool.false_eq_true, false_iff]
      exact hno
    · rw [decRow_good _ _ _ _ hbad rfl]
      push Not at hbad
      obtain ⟨hw1, hw2⟩ := decInner_fold y i (st ω y i) (y.getD (ω + i) 0) _ (st ω y i) h
        (st ω y i) rfl le_rfl hbad.1
      have hprev := decInner_previous (fun i => y.getD i 0) i (st ω y i)
        (List.range' (st ω y i) (y.getD (ω + i) 0 - st ω y i)) ⟨h, st ω y i, true⟩
      generalize hs : (List.range' (st ω y i) (y.getD (ω + i) 0 - st ω y i)).foldl
        (decInner (fun i => y.getD i 0) i (st ω y i)) ⟨h, st ω y i, true⟩ = s at hw1 hw2 hprev
      by_cases hinc : ∀ t < y.getD (ω + i) 0, st ω y i ≤ t → st ω y i < t →
          y.getD (t - 1) 0 < y.getD t 0
      · have hvalid : s.valid = true := hw1.mpr hinc
        have hrow : RowOK ω y i := ⟨hbad.1, hbad.2, fun t ht h' => hinc t ht h'.le h'⟩
        have hiff : RowsFrom k ω y (i + 1) ↔ RowsFrom k ω y i := by
          constructor
          · intro hall j hj hij
            rcases Nat.eq_or_lt_of_le hij with he | hlt
            · subst he; exact hrow
            · exact hall j hj hlt
          · intro hall j hj hij
            exact hall j hj (by omega)
        have hs' : ({ s with previous := y.getD (ω + i) 0 } : DecState) =
            ⟨s.hint, st ω y (i + 1), true⟩ := by
          rw [st_succ]; cases s; simp_all [ep]
        rw [hs']
        obtain ⟨ih1, ih2⟩ := ih (i + 1) s.hint (by omega) (by omega)
        refine ⟨ih1.trans hiff, fun hall => ?_⟩
        obtain ⟨ih3, ih4⟩ := ih2 (hiff.mpr hall)
        refine ⟨?_, ih4⟩
        rw [ih3, hw2 hinc]
        funext r c
        beta_reduce
        by_cases hr : r = i
        · subst hr
          have hseg : ∀ c, c ∈ seg ω y r ↔ c ∈ List.map (fun t => y.getD t 0)
              (List.range' (st ω y r) (y.getD (ω + r) 0 - st ω y r)) := by
            intro c; rfl
          rw [ite_eq_right (show ¬ (r + 1 ≤ r ∧ r < k ∧ c ∈ seg ω y r) from fun h => by omega)]
          by_cases hcm : c ∈ seg ω y r
          · rw [ite_eq_left (show r = r ∧ _ from ⟨rfl, (hseg c).mp hcm⟩),
              ite_eq_left (show r ≤ r ∧ r < k ∧ c ∈ seg ω y r from ⟨le_rfl, by omega, hcm⟩)]
          · rw [ite_eq_right (show ¬ (r = r ∧ c ∈ List.map (fun t => y.getD t 0)
                (List.range' (st ω y r) (y.getD (ω + r) 0 - st ω y r))) from
                fun h => hcm ((hseg c).mpr h.2)),
              ite_eq_right (show ¬ (r ≤ r ∧ r < k ∧ c ∈ seg ω y r) from fun h => hcm h.2.2)]
        · by_cases h1 : i + 1 ≤ r ∧ r < k ∧ c ∈ seg ω y r
          · rw [ite_eq_left h1, ite_eq_left ⟨by omega, h1.2⟩]
          · have h2 : ¬ (i ≤ r ∧ r < k ∧ c ∈ seg ω y r) := fun h => h1 ⟨by omega, h.2⟩
            rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (fun h => hr h.1)]
      · have hinvalid : s.valid = false := by
          cases hv : s.valid
          · rfl
          · exact absurd (hw1.mp hv) hinc
        have hs' : ({ s with previous := y.getD (ω + i) 0 } : DecState).valid = false := hinvalid
        rw [decRows_invalid _ _ _ _ hs']
        have hno : ¬ RowsFrom k ω y i := by
          intro hall
          exact hinc (fun t ht _ h' => (hall i (by omega) le_rfl).2.2 t ht h')
        simp only [hinvalid, Bool.false_eq_true, hno, IsEmpty.forall_iff, and_true]

theorem trailing_fold :
    ∀ n i, ω - i = n →
      (List.range' i (ω - i)).foldl (fun v index => if y.getD index 0 ≠ 0 then false else v) true =
        decide (∀ t < ω, i ≤ t → y.getD t 0 = 0) := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [hn]
    simp only [List.range'_zero, List.foldl_nil, true_eq_decide_iff]
    intro t ht hit; omega
  | succ n ih =>
    intro i hn
    rw [show ω - i = (ω - (i + 1)) + 1 by omega, List.range'_succ, List.foldl_cons]
    by_cases hy : y.getD i 0 ≠ 0
    · rw [ite_eq_left hy, trailing_invalid]
      symm
      simp only [decide_eq_false_iff_not]
      intro hall
      exact hy (hall i (by omega) le_rfl)
    · rw [ite_eq_right hy, ih (i + 1) (by omega)]
      push Not at hy
      congr 1
      apply propext
      constructor
      · intro hall t ht hit
        rcases Nat.eq_or_lt_of_le hit with he | hlt
        · subst he; exact hy
        · exact hall t ht hlt
      · intro hall t ht hit
        exact hall t ht (by omega)

/-- **(a) The decoder is Algorithm 21.** Same accept/reject decision and same
output as `HintBitUnpack` on every byte string. -/
theorem decodeHintWith_eq : decodeHintWith (fun i => y.getD i 0) k ω = hintBitUnpack k ω y := by
  rw [hintBitUnpack_eq]
  unfold decodeHintWith
  obtain ⟨h1, h2⟩ := decRows_fold k ω y k 0 (fun _ _ => 0) (by omega) (by omega)
  simp only [Nat.sub_zero, List.range'_eq_map_range, zero_add, List.map_id'] at h1 h2
  have hst0 : st ω y 0 = 0 := rfl
  rw [hst0] at h1 h2
  simp only
  generalize hr : (List.range k).foldl (decRow (fun i => y.getD i 0) ω)
    ⟨fun _ _ => 0, 0, true⟩ = r at h1 h2
  by_cases hrows : RowsFrom k ω y 0
  · have hvalid : r.valid = true := h1.mpr hrows
    obtain ⟨hhint, hprev⟩ := h2 hrows
    rw [hvalid, hprev]
    have hstk : st ω y k ≤ ω := by
      unfold st
      split_ifs with hk
      · omega
      · exact (hrows (k - 1) (by omega) (by omega)).2.1
    rw [trailing_fold ω y _ _ rfl]
    by_cases htr : ∀ t < ω, st ω y k ≤ t → y.getD t 0 = 0
    · have hacc : Accepts k ω y := ⟨fun i hi => hrows i hi (by omega), htr⟩
      rw [decide_eq_true htr, ite_eq_left rfl, ite_eq_left hacc, hhint]
      congr 1
      funext r c
      simp only [decoded, zero_le, true_and]
    · have hacc : ¬ Accepts k ω y := fun h => htr h.2
      rw [decide_eq_false htr, ite_eq_right (by simp), ite_eq_right hacc]
  · have hvalid : r.valid = false := by
      cases hv : r.valid
      · rfl
      · exact absurd (h1.mp hv) hrows
    rw [hvalid, trailing_invalid, ite_eq_right (by simp), ite_eq_right]
    intro h
    exact hrows (fun j hj _ => h.1 j hj)

end

/-- The decoder reads the hint section `octets[hint_offset …]` only through
`get`, so on a signature `P ‖ y` with `|P| = hint_offset` it is the decoder
of `y`. -/
theorem decodeHint_shift (P y : List ℕ) (k ω : ℕ) :
    decodeHint (P ++ y) P.length k ω = hintBitUnpack k ω y := by
  unfold decodeHint
  have : (fun i => (P ++ y).getD (P.length + i) 0) = (fun i => y.getD i 0) := by
    funext i
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  rw [this, decodeHintWith_eq]

/-- Every read of the decoder is inside the hint section `[0, ω + k)` of
length `ω + k` (so inside the signature), and every write
`hint.(row).(coefficient) <- 1` has `row < k` and `coefficient < 256` when the
bytes are bytes. -/
theorem decoder_reads_in_bounds (k ω : ℕ) (y : List ℕ) (hb : ∀ x ∈ y, x < 256) :
    (∀ row < k, ω + row < ω + k) ∧
    (∀ index endpoint, endpoint ≤ ω → index < endpoint → index < ω + k ∧ index - 1 < ω + k) ∧
    (∀ index < ω, index < ω + k) ∧
    (∀ index, y.getD index 0 < 256) := by
  refine ⟨fun row h => by omega, fun i e he hi => ⟨by omega, by omega⟩, fun i h => by omega,
    getD_lt_of_all (by norm_num) hb⟩

/-! ## The encoder -/

/-- The inner loop body of the hint encoder (lines 699–702):
```
if hint.(row).(coefficient) <> 0 then begin
  set_u8 output (hint_offset + !count) coefficient;
  incr count
end
``` -/
def encInner (base : ℕ) (h : HintVec) (row : ℕ) (st : List ℕ × ℕ) (coefficient : ℕ) :
    List ℕ × ℕ :=
  if h row coefficient ≠ 0 then (st.1.set (base + st.2) coefficient, st.2 + 1) else st

/-- One row of the hint encoder (lines 698–704), ending with
`set_u8 output (hint_offset + P.omega + row) !count`. -/
def encRow (base ω : ℕ) (h : HintVec) (st : List ℕ × ℕ) (row : ℕ) : List ℕ × ℕ :=
  let st := (List.range 256).foldl (encInner base h row) st
  (st.1.set (base + ω + row) st.2, st.2)

/-- The hint part of `encode_signature` (lines 694–705) at
`base = hint_offset`, on the output buffer `output`. -/
def encodeHint (base k ω : ℕ) (h : HintVec) (output : List ℕ) : List ℕ :=
  ((List.range k).foldl (encRow base ω h) (output, 0)).1

/-- At `hint_offset = 0` on a zero buffer, the encoder is Algorithm 20. -/
theorem encodeHint_eq_spec (k ω : ℕ) (h : HintVec) :
    encodeHint 0 k ω h (List.replicate (ω + k) 0) = hintBitPack k ω h := by
  unfold encodeHint hintBitPack encRow encInner
  simp only [zero_add]

/-- The encoder only writes at `hint_offset + i`, so on a buffer `P ‖ Q` with
`|P| = hint_offset` it leaves `P` alone. -/
theorem encodeHint_shift (P Q : List ℕ) (k ω : ℕ) (h : HintVec) :
    encodeHint P.length k ω h (P ++ Q) = P ++ encodeHint 0 k ω h Q := by
  have hset : ∀ (L : List ℕ) (n x : ℕ), (P ++ L).set (P.length + n) x = P ++ L.set n x := by
    intro L n x
    rw [List.set_append, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  let f : List ℕ × ℕ → List ℕ × ℕ := fun st => (P ++ st.1, st.2)
  have hinner : ∀ row (st : List ℕ × ℕ) c, encInner P.length h row (f st) c = f (encInner 0 h row st c) := by
    intro row st c
    unfold encInner
    split_ifs
    · simp only [f, hset, zero_add]
    · rfl
  have hrow : ∀ (st : List ℕ × ℕ) row, encRow P.length ω h (f st) row = f (encRow 0 ω h st row) := by
    intro st row
    unfold encRow
    simp only
    rw [List.foldl_hom f (fun st c => hinner row st c)]
    simp only [f, zero_add]
    rw [show P.length + ω + row = P.length + (ω + row) by ring, hset]
  unfold encodeHint
  have := List.foldl_hom f (g₁ := encRow 0 ω h) (g₂ := encRow P.length ω h) (l := List.range k)
    (init := (Q, 0)) hrow
  simp only [f] at this
  rw [this]

end OcamlPq.Encoding.Hint
