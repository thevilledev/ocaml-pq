import OcamlPq.Encoding.Bytes

/-!
# FIPS 204 hint encoding: Algorithms 20 and 21

Transcriptions of `HintBitPack` (Algorithm 20) and `HintBitUnpack`
(Algorithm 21), and a closed-form characterisation of `HintBitUnpack`
(`hintBitUnpack_eq`): it accepts exactly the strings satisfying `Accepts`
and then returns `decoded`.

A hint vector `h ∈ R_2^k` is a function `row ↦ coefficient ↦ value`
(the OCaml `int array array` read with `h.(row).(coefficient)`); rows are
`0 … k−1`, coefficients `0 … 255`. The hint section of a signature is the byte
string `y` of length `ω + k`; `y[ω + i]` is the end of row `i`'s index list.
-/

namespace OcamlPq.Encoding.Hint

/-- A hint vector, indexed by row and coefficient. -/
abbrev HintVec := ℕ → ℕ → ℕ

/-- `h[row]_c ← 1`. -/
def setHint (h : HintVec) (row c : ℕ) : HintVec := fun r c' => if r = row ∧ c' = c then 1 else h r c'

/-! ## Algorithm 20 -/

/-- FIPS 204 Algorithm 20, `HintBitPack(h)`:
```
y ← 0^{ω+k}; Index ← 0
for i from 0 to k − 1
  for j from 0 to 255
    if h[i]_j ≠ 0 then y[Index] ← j; Index ← Index + 1
  y[ω + i] ← Index
return y
``` -/
def hintBitPack (k ω : ℕ) (h : HintVec) : List ℕ :=
  ((List.range k).foldl (fun (st : List ℕ × ℕ) i =>
    let st := (List.range 256).foldl (fun (st : List ℕ × ℕ) j =>
      if h i j ≠ 0 then (st.1.set st.2 j, st.2 + 1) else st) st
    (st.1.set (ω + i) st.2, st.2)) (List.replicate (ω + k) 0, 0)).1

/-! ## Algorithm 21 -/

/-- Lines 6–11 of Algorithm 21, the `while Index < y[ω + i]` loop of row `i`
with `First` fixed. Returns the hint and the final `Index`, or `⊥`. -/
def unpackWhile (y : List ℕ) (i first stop : ℕ) (index : ℕ) (h : HintVec) : Option (HintVec × ℕ) :=
  if index < stop then
    if index > first ∧ y.getD (index - 1) 0 ≥ y.getD index 0 then none
    else unpackWhile y i first stop (index + 1) (setHint h i (y.getD index 0))
  else some (h, index)
termination_by stop - index

/-- Lines 3–12 of Algorithm 21, the `for i` loop from row `i` on. -/
def unpackRows (k ω : ℕ) (y : List ℕ) (i : ℕ) (h : HintVec) (index : ℕ) : Option (HintVec × ℕ) :=
  if i < k then
    if y.getD (ω + i) 0 < index ∨ y.getD (ω + i) 0 > ω then none
    else match unpackWhile y i index (y.getD (ω + i) 0) index h with
      | none => none
      | some (h', index') => unpackRows k ω y (i + 1) h' index'
  else some (h, index)
termination_by k - i

/-- Lines 13–15 of Algorithm 21: `for i from Index to ω − 1: if y[i] ≠ 0
then return ⊥`. -/
def unpackTrailing (ω : ℕ) (y : List ℕ) (i : ℕ) : Bool :=
  if i < ω then (if y.getD i 0 ≠ 0 then false else unpackTrailing ω y (i + 1)) else true
termination_by ω - i

/-- FIPS 204 Algorithm 21, `HintBitUnpack(y)`; `none` is `⊥`. -/
def hintBitUnpack (k ω : ℕ) (y : List ℕ) : Option HintVec :=
  match unpackRows k ω y 0 (fun _ _ => 0) 0 with
  | none => none
  | some (h, index) => if unpackTrailing ω y index then some h else none

/-! ## Characterisation -/

/-- The end of row `i`'s index list, `y[ω + i]`. -/
def ep (ω : ℕ) (y : List ℕ) (i : ℕ) : ℕ := y.getD (ω + i) 0

/-- The start of row `i`'s index list: `0` for row 0, else `y[ω + i − 1]`. -/
def st (ω : ℕ) (y : List ℕ) (i : ℕ) : ℕ := if i = 0 then 0 else ep ω y (i - 1)

theorem st_succ (ω : ℕ) (y : List ℕ) (i : ℕ) : st ω y (i + 1) = ep ω y i := by
  simp [st]

/-- The coefficients listed for row `i`: `y[st i], …, y[ep i − 1]`. -/
def seg (ω : ℕ) (y : List ℕ) (i : ℕ) : List ℕ :=
  (List.range' (st ω y i) (ep ω y i - st ω y i)).map (fun t => y.getD t 0)

/-- Row `i` passes the checks of Algorithm 21: its end lies in
`[start, ω]` and its coefficients are strictly increasing. -/
def RowOK (ω : ℕ) (y : List ℕ) (i : ℕ) : Prop :=
  st ω y i ≤ ep ω y i ∧ ep ω y i ≤ ω ∧
    ∀ t < ep ω y i, st ω y i < t → y.getD (t - 1) 0 < y.getD t 0

instance (ω : ℕ) (y : List ℕ) (i : ℕ) : Decidable (RowOK ω y i) := by
  unfold RowOK; infer_instance

/-- The strings `HintBitUnpack` accepts. -/
def Accepts (k ω : ℕ) (y : List ℕ) : Prop :=
  (∀ i < k, RowOK ω y i) ∧ ∀ t < ω, st ω y k ≤ t → y.getD t 0 = 0

instance (k ω : ℕ) (y : List ℕ) : Decidable (Accepts k ω y) := by
  unfold Accepts; infer_instance

/-- The hint vector an accepted string decodes to. -/
def decoded (k ω : ℕ) (y : List ℕ) : HintVec :=
  fun r c => if r < k ∧ c ∈ seg ω y r then 1 else 0

theorem unpackWhile_eq (y : List ℕ) (i first stop : ℕ) :
    ∀ n idx (h : HintVec), stop - idx = n → first ≤ idx → idx ≤ stop →
      unpackWhile y i first stop idx h =
        if ∀ t < stop, idx ≤ t → first < t → y.getD (t - 1) 0 < y.getD t 0
        then some (fun r c =>
          if r = i ∧ c ∈ (List.range' idx (stop - idx)).map (fun t => y.getD t 0) then 1
          else h r c, stop)
        else none := by
  intro n
  induction n with
  | zero =>
    intro idx h hn h1 h2
    have he : idx = stop := by omega
    subst he
    rw [unpackWhile, ite_eq_right (lt_irrefl _), ite_eq_left (fun t ht h' _ => absurd ht (by omega))]
    simp
  | succ n ih =>
    intro idx h hn h1 h2
    rw [unpackWhile, ite_eq_left (by omega)]
    by_cases hbad : idx > first ∧ y.getD (idx - 1) 0 ≥ y.getD idx 0
    · rw [ite_eq_left hbad, ite_eq_right]
      intro hall
      have := hall idx (by omega) le_rfl hbad.1
      omega
    · rw [ite_eq_right hbad, ih (idx + 1) _ (by omega) (by omega) (by omega)]
      have hiff : (∀ t < stop, idx + 1 ≤ t → first < t → y.getD (t - 1) 0 < y.getD t 0) ↔
          (∀ t < stop, idx ≤ t → first < t → y.getD (t - 1) 0 < y.getD t 0) := by
        constructor
        · intro hall t ht h1' h2'
          rcases Nat.eq_or_lt_of_le h1' with he | hlt
          · subst he
            push Not at hbad
            exact hbad h2'
          · exact hall t ht hlt h2'
        · intro hall t ht h1' h2'
          exact hall t ht (by omega) h2'
      by_cases hc : ∀ t < stop, idx ≤ t → first < t → y.getD (t - 1) 0 < y.getD t 0
      · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc]
        congr 2
        funext r c
        rw [show stop - idx = (stop - (idx + 1)) + 1 by omega, List.range'_succ]
        simp only [List.map_cons, List.mem_cons, setHint]
        by_cases hr : r = i
        · by_cases hc1 : c ∈ (List.range' (idx + 1) (stop - (idx + 1))).map (fun t => y.getD t 0)
          · rw [ite_eq_left ⟨hr, hc1⟩, ite_eq_left ⟨hr, Or.inr hc1⟩]
          · by_cases hc2 : c = y.getD idx 0
            · rw [ite_eq_right (fun h => hc1 h.2), ite_eq_left ⟨hr, hc2⟩, ite_eq_left ⟨hr, Or.inl hc2⟩]
            · rw [ite_eq_right (fun h => hc1 h.2), ite_eq_right (fun h => hc2 h.2),
                ite_eq_right (fun h => h.2.elim hc2 hc1)]
        · rw [ite_eq_right (fun h => hr h.1), ite_eq_right (fun h => hr h.1), ite_eq_right (fun h => hr h.1)]
      · rw [ite_eq_right (fun h' => hc (hiff.mp h')), ite_eq_right hc]

/-- The row conditions for rows `i … k − 1`. -/
def RowsFrom (k ω : ℕ) (y : List ℕ) (i : ℕ) : Prop := ∀ j < k, i ≤ j → RowOK ω y j

instance (k ω : ℕ) (y : List ℕ) (i : ℕ) : Decidable (RowsFrom k ω y i) := by
  unfold RowsFrom; infer_instance

theorem unpackRows_eq (k ω : ℕ) (y : List ℕ) :
    ∀ n i (h : HintVec), k - i = n → i ≤ k →
      unpackRows k ω y i h (st ω y i) =
        if RowsFrom k ω y i
        then some (fun r c => if i ≤ r ∧ r < k ∧ c ∈ seg ω y r then 1 else h r c, st ω y k)
        else none := by
  intro n
  induction n with
  | zero =>
    intro i h hn hi
    have he : i = k := by omega
    subst he
    rw [unpackRows, ite_eq_right (lt_irrefl _),
      ite_eq_left (show RowsFrom i ω y i from fun j hj h' => absurd hj (by omega))]
    congr 2
    funext r c
    simp only [show ¬ (i ≤ r ∧ r < i ∧ c ∈ seg ω y r) by omega, ite_false]
  | succ n ih =>
    intro i h hn hi
    rw [unpackRows, ite_eq_left (by omega)]
    by_cases hbad : y.getD (ω + i) 0 < st ω y i ∨ y.getD (ω + i) 0 > ω
    · rw [ite_eq_left hbad, ite_eq_right]
      intro hall
      have := hall i (by omega) le_rfl
      unfold RowOK ep at this
      omega
    · rw [ite_eq_right hbad]
      push Not at hbad
      have hw := unpackWhile_eq y i (st ω y i) (y.getD (ω + i) 0) _ (st ω y i) h rfl le_rfl hbad.1
      rw [hw]
      by_cases hinc : ∀ t < y.getD (ω + i) 0, st ω y i ≤ t → st ω y i < t →
          y.getD (t - 1) 0 < y.getD t 0
      · rw [ite_eq_left hinc]
        simp only
        rw [show y.getD (ω + i) 0 = st ω y (i + 1) by rw [st_succ]; rfl,
          ih (i + 1) _ (by omega) (by omega)]
        have hrow : RowOK ω y i := ⟨hbad.1, hbad.2, fun t ht h' => hinc t ht h'.le h'⟩
        have hiff : RowsFrom k ω y (i + 1) ↔ RowsFrom k ω y i := by
          constructor
          · intro hall j hj hij
            rcases Nat.eq_or_lt_of_le hij with he | hlt
            · subst he; exact hrow
            · exact hall j hj hlt
          · intro hall j hj hij
            exact hall j hj (by omega)
        by_cases hrows : RowsFrom k ω y i
        · rw [ite_eq_left (hiff.mpr hrows), ite_eq_left hrows]
          congr 2
          funext r c
          by_cases hr : r = i
          · subst hr
            have hseg : ∀ c, c ∈ seg ω y r ↔ c ∈ List.map (fun t => y.getD t 0)
                (List.range' (st ω y r) (st ω y (r + 1) - st ω y r)) := by
              intro c; rw [st_succ]; rfl
            rw [ite_eq_right (show ¬ (r + 1 ≤ r ∧ r < k ∧ c ∈ seg ω y r) from fun h => by omega)]
            by_cases hcm : c ∈ seg ω y r
            · rw [ite_eq_left (show r = r ∧ _ from ⟨rfl, (hseg c).mp hcm⟩),
                ite_eq_left (show r ≤ r ∧ r < k ∧ c ∈ seg ω y r from ⟨le_rfl, by omega, hcm⟩)]
            · rw [ite_eq_right (show ¬ (r = r ∧ c ∈ List.map (fun t => y.getD t 0)
                  (List.range' (st ω y r) (st ω y (r + 1) - st ω y r))) from
                  fun h => hcm ((hseg c).mpr h.2)),
                ite_eq_right (show ¬ (r ≤ r ∧ r < k ∧ c ∈ seg ω y r) from fun h => hcm h.2.2)]
          · by_cases h1 : i + 1 ≤ r ∧ r < k ∧ c ∈ seg ω y r
            · rw [ite_eq_left h1, ite_eq_left ⟨by omega, h1.2⟩]
            · have h2 : ¬ (i ≤ r ∧ r < k ∧ c ∈ seg ω y r) := fun h => h1 ⟨by omega, h.2⟩
              rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (fun h => hr h.1)]
        · rw [ite_eq_right (fun h' => hrows (hiff.mp h')), ite_eq_right hrows]
      · rw [ite_eq_right hinc, ite_eq_right]
        intro hall
        have := (hall i (by omega) le_rfl).2.2
        exact hinc (fun t ht _ h' => this t ht h')

theorem unpackTrailing_eq (ω : ℕ) (y : List ℕ) :
    ∀ n i, ω - i = n → unpackTrailing ω y i = decide (∀ t < ω, i ≤ t → y.getD t 0 = 0) := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [unpackTrailing, ite_eq_right (by omega)]
    simp only [true_eq_decide_iff]
    intro t ht hit; omega
  | succ n ih =>
    intro i hn
    rw [unpackTrailing, ite_eq_left (by omega)]
    by_cases hy : y.getD i 0 ≠ 0
    · rw [ite_eq_left hy]
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

/-- **Characterisation of Algorithm 21.** `HintBitUnpack(y)` accepts exactly
the strings satisfying `Accepts` and returns `decoded`. -/
theorem hintBitUnpack_eq (k ω : ℕ) (y : List ℕ) :
    hintBitUnpack k ω y = if Accepts k ω y then some (decoded k ω y) else none := by
  unfold hintBitUnpack
  have h0 : st ω y 0 = 0 := rfl
  have hr := unpackRows_eq k ω y k 0 (fun _ _ => 0) (by omega) (by omega)
  rw [h0] at hr
  rw [hr]
  by_cases hrows : RowsFrom k ω y 0
  · rw [ite_eq_left hrows]
    simp only
    rw [unpackTrailing_eq ω y _ _ rfl]
    by_cases htr : ∀ t < ω, st ω y k ≤ t → y.getD t 0 = 0
    · have hacc : Accepts k ω y := ⟨fun i hi => hrows i hi (by omega), htr⟩
      rw [decide_eq_true htr, ite_eq_left rfl, ite_eq_left hacc]
      congr 1
      funext r c
      simp only [decoded, zero_le, true_and]
    · have hacc : ¬ Accepts k ω y := fun h => htr h.2
      rw [decide_eq_false htr, ite_eq_right (by simp), ite_eq_right hacc]
  · rw [ite_eq_right hrows, ite_eq_right]
    intro h
    exact hrows (fun j hj _ => h.1 j hj)

end OcamlPq.Encoding.Hint
