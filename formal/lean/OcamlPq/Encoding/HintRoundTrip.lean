import OcamlPq.Encoding.Hint
import OcamlPq.Encoding.Packer

/-!
# Round trips and canonicity of the hint encoding

For every `k` and `ω`:

* `hintBitPack_eq`: closed form of Algorithm 20 — the rows' index lists,
  zero padding to `ω` bytes, then the `k` cumulative counts;
* (b) `decode_encode`: `HintBitUnpack(HintBitPack(h)) = h` for every
  `h ∈ {0,1}^{k×256}` with at most `ω` ones;
* (c) `encode_decode`: **canonicity** — `HintBitUnpack(y) = h` implies
  `HintBitPack(h) = y`, for every byte string `y` of length `ω + k`;
* (d) `weight_le_of_decode`: every decoded `h` has at most `ω` ones.

With `decodeHintWith_eq` (Algorithm 21 = the OCaml decoder) and
`encodeHint_eq_spec` (Algorithm 20 = the OCaml encoder) these are statements
about `encode_signature` and `decode_signature`; see `MldsaLayout.lean` for
the whole signature.
-/

namespace OcamlPq.Encoding.Hint

open OcamlPq.Encoding

/-! ## Weights -/

/-- The coefficients `c < 256` with `h[i]_c ≠ 0`, in increasing order. -/
def rowList (h : HintVec) (i : ℕ) : List ℕ := (List.range 256).filter (fun c => h i c ≠ 0)

/-- The concatenation of the first `m` rows' lists. -/
def allList (h : HintVec) (m : ℕ) : List ℕ := (List.range m).flatMap (rowList h)

/-- The number of nonzero coefficients of `h` in rows `0 … k − 1`. -/
def weight (k : ℕ) (h : HintVec) : ℕ := (allList h k).length

theorem allList_succ (h : HintVec) (i : ℕ) : allList h (i + 1) = allList h i ++ rowList h i := by
  simp [allList, List.range_succ, List.flatMap_append]

theorem allList_length_mono (h : HintVec) {i j : ℕ} (hij : i ≤ j) :
    (allList h i).length ≤ (allList h j).length := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact le_rfl
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with he | hlt
    · subst he; exact le_rfl
    · rw [allList_succ, List.length_append]
      have := ih (by omega)
      omega

theorem rowList_pairwise (h : HintVec) (i : ℕ) : (rowList h i).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem mem_rowList (h : HintVec) (i c : ℕ) : c ∈ rowList h i ↔ c < 256 ∧ h i c ≠ 0 := by
  simp [rowList]

theorem rowList_filter_prefix (h : HintVec) (i c : ℕ) (hc : c ≤ 256) :
    ((List.range c).filter (fun c => h i c ≠ 0)).length ≤ (rowList h i).length :=
  ((List.range_sublist.mpr hc).filter _).length_le

/-! ## Closed form of `HintBitPack` -/

theorem set_before (A B : List ℕ) (n x : ℕ) (hn : n < A.length) :
    (A ++ B).set n x = A.set n x ++ B := by
  rw [List.set_append, ite_eq_left hn]

theorem set_after (A B : List ℕ) (n x : ℕ) :
    (A ++ B).set (A.length + n) x = A ++ B.set n x := by
  rw [List.set_append, ite_eq_right (by omega), Nat.add_sub_cancel_left]

/-- The inner loop of `HintBitPack` on row `i`, after coefficients `0 … c − 1`. -/
theorem pack_inner (ω : ℕ) (h : HintVec) (i : ℕ) (B : List ℕ)
    (hw : (allList h (i + 1)).length ≤ ω) :
    ∀ c, c ≤ 256 →
      (List.range c).foldl (fun (st : List ℕ × ℕ) j =>
          if h i j ≠ 0 then (st.1.set st.2 j, st.2 + 1) else st)
        ((allList h i ++ List.replicate (ω - (allList h i).length) 0) ++ B, (allList h i).length) =
      ((allList h i ++ (List.range c).filter (fun c => h i c ≠ 0)) ++
          List.replicate (ω - (allList h i ++ (List.range c).filter (fun c => h i c ≠ 0)).length) 0
          ++ B,
        (allList h i ++ (List.range c).filter (fun c => h i c ≠ 0)).length) := by
  intro c
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro hc
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      List.filter_append]
    generalize hA : allList h i ++ (List.range c).filter (fun c => h i c ≠ 0) = A
    have hlen : (allList h i ++ (List.range (c + 1)).filter (fun c => h i c ≠ 0)).length ≤ ω := by
      have := rowList_filter_prefix h i (c + 1) hc
      rw [allList_succ, List.length_append] at hw
      rw [List.length_append]; omega
    by_cases hic : h i c ≠ 0
    · rw [ite_eq_left hic]
      have hf : (List.filter (fun c => decide (h i c ≠ 0)) [c]) = [c] := by simp [hic]
      rw [hf, ← List.append_assoc, hA]
      have hAlen : A.length + 1 ≤ ω := by
        rw [List.range_succ, List.filter_append, hf, ← List.append_assoc, hA] at hlen
        simpa using hlen
      obtain ⟨m, hm⟩ : ∃ m, ω - A.length = m + 1 := ⟨ω - A.length - 1, by omega⟩
      rw [hm, set_before (A ++ List.replicate (m + 1) 0) B A.length c (by simp),
        Packer.set_length_append_replicate A c m]
      simp only [List.length_append, List.length_singleton]
      rw [show ω - (A.length + 1) = m by omega]
    · rw [ite_eq_right hic]
      have hf : (List.filter (fun c => decide (h i c ≠ 0)) [c]) = [] := by simp [hic]
      rw [hf, List.append_nil, hA]

/-- The state of `HintBitPack` after rows `0 … i − 1`. -/
theorem pack_rows (k ω : ℕ) (h : HintVec) (hw : weight k h ≤ ω) :
    ∀ i, i ≤ k →
      (List.range i).foldl (fun (st : List ℕ × ℕ) i =>
          let st := (List.range 256).foldl (fun (st : List ℕ × ℕ) j =>
            if h i j ≠ 0 then (st.1.set st.2 j, st.2 + 1) else st) st
          (st.1.set (ω + i) st.2, st.2)) (List.replicate (ω + k) 0, 0) =
        ((allList h i ++ List.replicate (ω - (allList h i).length) 0) ++
            ((List.range i).map (fun j => (allList h (j + 1)).length) ++ List.replicate (k - i) 0),
          (allList h i).length) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil, allList, List.flatMap_nil, List.length_nil,
      List.nil_append, Nat.sub_zero, List.map_nil, List.replicate_add]
  | succ i ih =>
    intro hi
    rw [List.range_succ (n := i), List.foldl_append, ih (by omega), List.foldl_cons,
      List.foldl_nil]
    simp only
    have hw' : (allList h (i + 1)).length ≤ ω :=
      le_trans (allList_length_mono h (by omega)) hw
    rw [pack_inner ω h i _ hw' 256 le_rfl]
    have hrow : allList h i ++ (List.range 256).filter (fun c => h i c ≠ 0) = allList h (i + 1) := by
      rw [allList_succ]; rfl
    rw [hrow]
    have hF : (allList h (i + 1) ++ List.replicate (ω - (allList h (i + 1)).length) 0).length = ω := by
      simp; omega
    rw [List.append_assoc, show ω + i = (allList h (i + 1) ++
        List.replicate (ω - (allList h (i + 1)).length) 0).length + i by rw [hF],
      ← List.append_assoc, set_after]
    obtain ⟨m, hm⟩ : ∃ m, k - i = m + 1 := ⟨k - i - 1, by omega⟩
    have := Packer.set_length_append_replicate ((List.range i).map (fun j => (allList h (j + 1)).length))
      (allList h (i + 1)).length m
    simp only [List.length_map, List.length_range] at this
    rw [hm, this, show k - (i + 1) = m by omega, List.map_append, List.map_singleton]

/-- **Closed form of Algorithm 20.** For `h` with at most `ω` nonzero
coefficients, `HintBitPack(h)` is the concatenated index lists, zero padding
up to `ω` bytes, and the cumulative counts. -/
theorem hintBitPack_eq (k ω : ℕ) (h : HintVec) (hw : weight k h ≤ ω) :
    hintBitPack k ω h =
      (allList h k ++ List.replicate (ω - weight k h) 0) ++
        (List.range k).map (fun i => (allList h (i + 1)).length) := by
  unfold hintBitPack
  rw [pack_rows k ω h hw k le_rfl]
  simp [weight]

theorem length_hintBitPack (k ω : ℕ) (h : HintVec) (hw : weight k h ≤ ω) :
    (hintBitPack k ω h).length = ω + k := by
  rw [hintBitPack_eq k ω h hw]
  simp [weight] at hw ⊢; omega

/-! ## (b) Decoding an encoding -/

theorem getD_pack_low (L E : List ℕ) (ω t : ℕ) (hL : L.length ≤ ω) (ht : t < ω) :
    ((L ++ List.replicate (ω - L.length) 0) ++ E).getD t 0 = L.getD t 0 := by
  have hlen : (L ++ List.replicate (ω - L.length) 0).length = ω := by simp; omega
  rw [List.getD_append _ _ _ _ (by rw [hlen]; exact ht)]
  by_cases htl : t < L.length
  · rw [List.getD_append _ _ _ _ htl]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default L _ (by omega),
      List.getD_eq_getElem _ _ (by simp; omega), List.getElem_replicate]

theorem getD_pack_high (L E : List ℕ) (ω i : ℕ) (hL : L.length ≤ ω) :
    ((L ++ List.replicate (ω - L.length) 0) ++ E).getD (ω + i) 0 = E.getD i 0 := by
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  congr 1; simp; omega

theorem slice_middle (A R M : List ℕ) :
    (List.range' A.length R.length).map (fun t => (A ++ R ++ M).getD t 0) = R := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range']
    rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
      show A.length + 1 * j - A.length = j by omega, List.getD_append _ _ _ _ h2,
      List.getD_eq_getElem _ _ h2]

theorem getD_middle (A R M : List ℕ) (s : ℕ) (h1 : A.length ≤ s) (h2 : s - A.length < R.length) :
    (A ++ R ++ M).getD s 0 = R[s - A.length] := by
  rw [List.append_assoc, List.getD_append_right _ _ _ _ h1, List.getD_append _ _ _ _ h2,
    List.getD_eq_getElem _ _ h2]

/-- **(b) Round trip.** For every `h` with entries in `{0, 1}`, zero outside
rows `0 … k − 1` and coefficients `0 … 255`, and at most `ω` ones:
`HintBitUnpack(HintBitPack(h)) = h`. -/
theorem decode_encode (k ω : ℕ) (h : HintVec) (h01 : ∀ r c, h r c ≤ 1)
    (hdom : ∀ r c, k ≤ r ∨ 256 ≤ c → h r c = 0) (hw : weight k h ≤ ω) :
    hintBitUnpack k ω (hintBitPack k ω h) = some h := by
  rw [hintBitUnpack_eq, hintBitPack_eq k ω h hw]
  set L := allList h k with hLdef
  set y := (L ++ List.replicate (ω - weight k h) 0) ++
    (List.range k).map (fun i => (allList h (i + 1)).length) with hy
  have hLw : L.length ≤ ω := hw
  have hy' : y = (L ++ List.replicate (ω - L.length) 0) ++
      (List.range k).map (fun i => (allList h (i + 1)).length) := rfl
  have hlow : ∀ t < ω, y.getD t 0 = L.getD t 0 := fun t ht => by
    rw [hy']; exact getD_pack_low _ _ _ _ hLw ht
  have hep : ∀ i < k, ep ω y i = (allList h (i + 1)).length := by
    intro i hi
    unfold ep
    rw [hy', getD_pack_high _ _ _ _ hLw, List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  have hst : ∀ i ≤ k, st ω y i = (allList h i).length := by
    intro i hi
    unfold st
    split_ifs with h0
    · subst h0; simp [allList]
    · rw [hep (i - 1) (by omega), show i - 1 + 1 = i by omega]
  have hmono : ∀ i ≤ k, (allList h i).length ≤ L.length := fun i hi => allList_length_mono h hi
  -- `L = allList h i ++ rowList h i ++ rest`
  have hsplit : ∀ i < k, ∃ M, L = allList h i ++ rowList h i ++ M := by
    intro i hi
    have : ∀ j, i + 1 + j ≤ k → ∃ M, allList h (i + 1 + j) = allList h i ++ rowList h i ++ M := by
      intro j
      induction j with
      | zero => intro _; exact ⟨[], by rw [Nat.add_zero, allList_succ, List.append_nil]⟩
      | succ j ihj =>
        intro hj
        obtain ⟨M, hM⟩ := ihj (by omega)
        exact ⟨M ++ rowList h (i + 1 + j), by
          rw [show i + 1 + (j + 1) = (i + 1 + j) + 1 by ring, allList_succ, hM]; simp⟩
    obtain ⟨M, hM⟩ := this (k - (i + 1)) (by omega)
    exact ⟨M, by rw [hLdef, ← hM]; congr 1; omega⟩
  have hseg : ∀ i < k, seg ω y i = rowList h i := by
    intro i hi
    obtain ⟨M, hM⟩ := hsplit i hi
    unfold seg
    rw [hep i hi, hst i hi.le, allList_succ, List.length_append, Nat.add_sub_cancel_left]
    have : (List.range' (allList h i).length (rowList h i).length).map (fun t => y.getD t 0) =
        (List.range' (allList h i).length (rowList h i).length).map (fun t => L.getD t 0) := by
      apply List.map_congr_left
      intro t ht
      rw [List.mem_range'] at ht
      apply hlow
      have := hmono (i + 1) hi
      rw [allList_succ, List.length_append] at this
      omega
    rw [this, hM, slice_middle]
  have hacc : Accepts k ω y := by
    refine ⟨fun i hi => ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hep i hi, hst i hi.le]; exact allList_length_mono h (by omega)
    · rw [hep i hi]; exact le_trans (hmono (i + 1) hi) hLw
    · intro t ht hst'
      rw [hep i hi] at ht
      rw [hst i hi.le] at hst'
      obtain ⟨M, hM⟩ := hsplit i hi
      have hlt : t < L.length := lt_of_lt_of_le ht (hmono (i + 1) hi)
      rw [hlow t (by omega), hlow (t - 1) (by omega), hM]
      have hrl := rowList_pairwise h i
      rw [allList_succ, List.length_append] at ht
      have h1 : t - 1 - (allList h i).length < (rowList h i).length := by omega
      have h2 : t - (allList h i).length < (rowList h i).length := by omega
      rw [getD_middle _ _ _ _ (by omega) h1, getD_middle _ _ _ _ (by omega) h2]
      exact List.pairwise_iff_getElem.mp hrl _ _ h1 h2 (by omega)
    · intro t ht hkt
      rw [hst k le_rfl] at hkt
      rw [hlow t ht, List.getD_eq_default _ _ hkt]
  rw [ite_eq_left hacc]
  congr 1
  funext r c
  unfold decoded
  by_cases hr : r < k
  · simp only [hseg r hr, mem_rowList]
    by_cases hc : c < 256 ∧ h r c ≠ 0
    · rw [ite_eq_left ⟨hr, hc⟩]; have := h01 r c; omega
    · rw [ite_eq_right (fun h' => hc h'.2)]
      by_cases hc' : c < 256
      · have : h r c = 0 := by by_contra h'; exact hc ⟨hc', h'⟩
        rw [this]
      · rw [hdom r c (Or.inr (by omega))]
  · rw [ite_eq_right (fun h' => hr h'.1), hdom r c (Or.inl (by omega))]

/-! ## (c) Canonicity and (d) the weight bound -/

section
variable (k ω : ℕ) (y : List ℕ)

theorem strictMono_of_adjacent (g : ℕ → ℕ) (a b : ℕ)
    (hadj : ∀ t < b, a < t → g (t - 1) < g t) :
    ∀ j i, i < j → a + j < b → g (a + i) < g (a + j) := by
  intro j
  induction j with
  | zero => intro i hi; omega
  | succ j ih =>
    intro i hi hj
    have hstep : g (a + j) < g (a + (j + 1)) := by
      have := hadj (a + (j + 1)) hj (by omega)
      rwa [show a + (j + 1) - 1 = a + j by omega] at this
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with he | hlt
    · subst he; exact hstep
    · exact lt_trans (ih i hlt (by omega)) hstep

theorem seg_pairwise (i : ℕ) (hrow : RowOK ω y i) : (seg ω y i).Pairwise (· < ·) := by
  unfold seg
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab
  simp only [List.getElem_map, List.getElem_range', one_mul]
  simp only [List.length_map, List.length_range'] at ha hb
  exact strictMono_of_adjacent (fun t => y.getD t 0) (st ω y i) (ep ω y i) hrow.2.2 b a hab
    (by omega)

theorem seg_lt (hb : ∀ x ∈ y, x < 256) (i : ℕ) : ∀ c ∈ seg ω y i, c < 256 := by
  intro c hc
  unfold seg at hc
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hc
  exact getD_lt_of_all (by norm_num) hb t

theorem rowList_decoded (hb : ∀ x ∈ y, x < 256) (hacc : Accepts k ω y) (i : ℕ) (hi : i < k) :
    rowList (decoded k ω y) i = seg ω y i := by
  apply List.Pairwise.eq_of_mem_iff (rowList_pairwise _ i) (seg_pairwise ω y i (hacc.1 i hi))
  intro c
  rw [mem_rowList]
  unfold decoded
  constructor
  · rintro ⟨-, hc⟩
    by_contra hn
    exact hc (ite_eq_right (fun h' => hn h'.2))
  · intro hc
    exact ⟨seg_lt ω y hb i c hc, by rw [ite_eq_left ⟨hi, hc⟩]; norm_num⟩

theorem st_le_ep (hacc : Accepts k ω y) (i : ℕ) (hi : i < k) : st ω y i ≤ ep ω y i :=
  (hacc.1 i hi).1

theorem allList_decoded (hb : ∀ x ∈ y, x < 256) (hacc : Accepts k ω y) :
    ∀ m ≤ k, allList (decoded k ω y) m = (List.range (st ω y m)).map (fun t => y.getD t 0) := by
  intro m
  induction m with
  | zero => intro _; simp [allList, st]
  | succ m ih =>
    intro hm
    rw [allList_succ, ih (by omega), rowList_decoded k ω y hb hacc m (by omega), st_succ]
    unfold seg
    have hle := st_le_ep k ω y hacc m (by omega)
    rw [List.range_eq_range', List.range_eq_range', ← List.map_append]
    have happ := List.range'_append (s := 0) (m := st ω y m) (n := ep ω y m - st ω y m) (step := 1)
    simp only [zero_add, one_mul] at happ
    rw [happ]
    congr 2
    omega

theorem st_k_le (hacc : Accepts k ω y) : st ω y k ≤ ω := by
  unfold st
  split_ifs with hk
  · omega
  · exact (hacc.1 (k - 1) (by omega)).2.1

/-- **(d) Weight bound.** Every hint vector accepted by `HintBitUnpack` has
at most `ω` nonzero coefficients. -/
theorem weight_decoded_le (hb : ∀ x ∈ y, x < 256) (hacc : Accepts k ω y) :
    weight k (decoded k ω y) ≤ ω := by
  unfold weight
  rw [allList_decoded k ω y hb hacc k le_rfl]
  simpa using st_k_le k ω y hacc

/-- **(c) Canonicity.** If `HintBitUnpack` accepts a byte string `y` of length
`ω + k`, then `y` is exactly `HintBitPack` of the decoded hint. -/
theorem encode_decoded (hlen : y.length = ω + k) (hb : ∀ x ∈ y, x < 256)
    (hacc : Accepts k ω y) : hintBitPack k ω (decoded k ω y) = y := by
  have hw := weight_decoded_le k ω y hb hacc
  rw [hintBitPack_eq k ω _ hw]
  have hL := allList_decoded k ω y hb hacc k le_rfl
  have hwk : weight k (decoded k ω y) = st ω y k := by unfold weight; rw [hL]; simp
  have hcum : ∀ i < k, (allList (decoded k ω y) (i + 1)).length = y.getD (ω + i) 0 := by
    intro i hi
    rw [allList_decoded k ω y hb hacc (i + 1) hi, st_succ]
    simp [ep]
  rw [hL, hwk]
  have hstk := st_k_le k ω y hacc
  apply List.ext_getElem
  · simp [hlen]; omega
  · intro t h1 h2
    by_cases ht : t < ω
    · rw [List.getElem_append_left (by simp; omega)]
      by_cases hts : t < st ω y k
      · rw [List.getElem_append_left (by simpa using hts)]
        simp [List.getElem?_eq_getElem h2]
      · rw [List.getElem_append_right (by simpa using hts)]
        simp only [List.getElem_replicate]
        have := hacc.2 t ht (by omega)
        rw [List.getD_eq_getElem _ _ h2] at this
        exact this.symm
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range, List.length_append, List.length_map,
        List.length_range, List.length_replicate]
      have hi : t - (st ω y k + (ω - st ω y k)) < k := by
        simp [hlen] at h2; omega
      rw [hcum _ hi, List.getD_eq_getElem _ _ (by omega)]
      congr 1; omega

end

/-- **(c) Canonicity**, stated on the decoder: `HintBitUnpack(y) = h` implies
`HintBitPack(h) = y`, for every byte string `y` of length `ω + k`. -/
theorem encode_decode (k ω : ℕ) (y : List ℕ) (hlen : y.length = ω + k)
    (hb : ∀ x ∈ y, x < 256) (h : HintVec) (hdec : hintBitUnpack k ω y = some h) :
    hintBitPack k ω h = y := by
  rw [hintBitUnpack_eq] at hdec
  split_ifs at hdec with hacc
  cases hdec
  exact encode_decoded k ω y hlen hb hacc

/-- **(d) Weight bound**, stated on the decoder. -/
theorem weight_le_of_decode (k ω : ℕ) (y : List ℕ) (hb : ∀ x ∈ y, x < 256) (h : HintVec)
    (hdec : hintBitUnpack k ω y = some h) : weight k h ≤ ω := by
  rw [hintBitUnpack_eq] at hdec
  split_ifs at hdec with hacc
  cases hdec
  exact weight_decoded_le k ω y hb hacc

/-- Decoded hints have entries in `{0, 1}` and vanish outside rows `0 … k − 1`
and coefficients `0 … 255`. -/
theorem decoded_valid (k ω : ℕ) (y : List ℕ) (hb : ∀ x ∈ y, x < 256) (h : HintVec)
    (hdec : hintBitUnpack k ω y = some h) :
    (∀ r c, h r c ≤ 1) ∧ ∀ r c, k ≤ r ∨ 256 ≤ c → h r c = 0 := by
  rw [hintBitUnpack_eq] at hdec
  split_ifs at hdec with hacc
  cases hdec
  refine ⟨fun r c => by unfold decoded; split_ifs <;> omega, fun r c hrc => ?_⟩
  unfold decoded
  rw [ite_eq_right]
  rintro ⟨hr, hc⟩
  rcases hrc with h' | h'
  · omega
  · have := seg_lt ω y hb r c hc; omega

/-- **Write safety of the encoder.** For `h` with at most `ω` ones, the write
`y[Index] ← j` of row `i`, coefficient `j` (with `h[i]_j ≠ 0`) is at
`Index < ω`: before row `i` and coefficient `j`, `Index` counts the ones seen
so far, which is below the total weight. The values written are `j < 256`
and counts `≤ ω`. -/
theorem encode_writes_in_bounds (k ω : ℕ) (h : HintVec) (hw : weight k h ≤ ω) (i j : ℕ)
    (hi : i < k) (hj : j < 256) (hij : h i j ≠ 0) :
    (allList h i ++ (List.range j).filter (fun c => h i c ≠ 0)).length < ω := by
  have h1 := rowList_filter_prefix h i (j + 1) (by omega)
  have h2 : ((List.range (j + 1)).filter (fun c => h i c ≠ 0)).length =
      ((List.range j).filter (fun c => h i c ≠ 0)).length + 1 := by
    rw [List.range_succ, List.filter_append]; simp [hij]
  have h3 := allList_length_mono h (show i + 1 ≤ k by omega)
  rw [allList_succ, List.length_append] at h3
  unfold weight at hw
  rw [List.length_append]
  omega

end OcamlPq.Encoding.Hint
