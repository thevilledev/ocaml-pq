import OcamlPq.Hash.Sha2Lemmas

/-!
# Byte-level lemmas for SHA-2: big-endian loads and stores, output strings
-/

namespace OcamlPq.Hash.Sha2

open FIPS180 Keccak

/-- A loop `for i = 0 to n - 1 do l.(g i) <- v i done` with pairwise distinct
positions: position `g i` ends up holding `v i`, all others are untouched. -/
theorem foldl_set_inj {α : Type*} [Inhabited α] (n : ℕ) (g : ℕ → ℕ) (v : ℕ → α) (l : List α)
    (hg : ∀ i < n, ∀ i' < n, g i = g i' → i = i') :
    ((List.range n).foldl (fun l i => l.set (g i) (v i)) l).length = l.length ∧
    (∀ i < n, g i < l.length → ((List.range n).foldl (fun l i => l.set (g i) (v i)) l)[g i]! = v i) ∧
    (∀ j, (∀ i < n, g i ≠ j) → ((List.range n).foldl (fun l i => l.set (g i) (v i)) l)[j]! = l[j]!) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih (fun i hi i' hi' h => hg i (by omega) i' (by omega) h)
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [List.length_set, ih1], fun i hi hgi => ?_, fun j hj => ?_⟩
    · rw [List.getElem!_set', ih1]
      by_cases hin : i = n
      · subst hin; rw [ite_eq_left ⟨rfl, hgi⟩]
      · have hne : g n ≠ g i := fun h => hin (hg i hi n (by omega) h.symm)
        rw [ite_eq_right (by tauto), ih2 i (by omega) hgi]
    · rw [List.getElem!_set', ite_eq_right (by have := hj n (by omega); tauto),
        ih3 j (fun i hi => hj i (by omega))]

/-- `get_u32_be s off` is the 32-bit word whose big-endian bit string is bits
`8·off … 8·off + 31` of `s`. -/
theorem getU32Be_eq (s : List UInt8) (off : ℕ) (h : off + 4 ≤ s.length) :
    getU32Be s off = wordOfBits 32 (((bytesToBitsBE s).drop (8 * off)).take 32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_wordOfBits 32 _ (by simp; omega) j hj, List.getElem_take, List.getElem_drop,
    bytesToBitsBE_getElem]
  have e1 : (8 * off + (32 - 1 - j)) / 8 = off + (31 - j) / 8 := by omega
  have e2 : (8 * off + (32 - 1 - j)) % 8 = (31 - j) % 8 := by omega
  simp only [e1, e2]
  simp only [getU32Be, int32OfByte, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat]
  rw [← getElem!_pos s _ (by omega)]
  interval_cases j <;> simp [UInt8.testBit_ge]

/-- `set_u32_be` writes the four big-endian bytes of `x` at `off … off + 3`. -/
theorem setU32Be_spec (b : List UInt8) (off : ℕ) (x : BitVec 32) (h : off + 4 ≤ b.length) :
    (setU32Be b off x).length = b.length ∧
    (∀ q < 4, (setU32Be b off x)[off + q]! = byteOfInt32 ((x >>> (24 - 8 * q)) &&& 0xff#32)) ∧
    (∀ j, (j < off ∨ off + 4 ≤ j) → (setU32Be b off x)[j]! = b[j]!) := by
  refine ⟨by simp [setU32Be], fun q hq => ?_, fun j hj => ?_⟩
  · simp only [setU32Be, List.getElem!_set', List.length_set]
    interval_cases q <;> simp <;> omega
  · simp only [setU32Be, List.getElem!_set', List.length_set]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]

theorem testBit_byteOfInt32 (x : BitVec 32) (s t : ℕ) (ht : t < 8) :
    (byteOfInt32 ((x >>> s) &&& 0xff#32)).toNat.testBit t = x.getLsbD (s + t) := by
  have hlt : ((x >>> s) &&& 0xff#32).toNat < 256 := by
    rw [BitVec.toNat_and]
    exact lt_of_le_of_lt Nat.and_le_right (by decide)
  rw [byteOfInt32, UInt8.toNat_ofNat', show 2 ^ 8 = 256 from rfl, Nat.mod_eq_of_lt hlt,
    BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  have : (0xff#32).getLsbD t = true := by interval_cases t <;> decide
  rw [this, Bool.and_true]

theorem flatMap_wordToBits_length {w : ℕ} (n : ℕ) (H : Fin n → BitVec w) :
    ((List.finRange n).flatMap fun j => wordToBits (H j)).length = n * w := by
  simp [List.length_flatMap, wordToBits_length]

/-- The output string `H_0 ‖ … ‖ H_{n−1}` indexed bit by bit. -/
theorem flatMap_wordToBits_getD {w : ℕ} (hw : 0 < w) :
    ∀ (n : ℕ) (H : Fin n → BitVec w) (b : ℕ) (hb : b < n * w),
      ((List.finRange n).flatMap fun j => wordToBits (H j)).getD b false =
        (H ⟨b / w, by rw [Nat.div_lt_iff_lt_mul hw]; exact hb⟩).getLsbD (w - 1 - b % w) := by
  intro n
  induction n with
  | zero => intro H b hb; simp at hb
  | succ n ih =>
    intro H b hb
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    by_cases hlt : b < w
    · rw [List.getD_append _ _ _ _ (by simpa using hlt), List.getD_eq_getElem _ _ (by simpa using hlt),
        wordToBits_getElem]
      congr 2
      · ext; simp [Nat.div_eq_of_lt hlt]
      · rw [Nat.mod_eq_of_lt hlt]
    · rw [List.getD_append_right _ _ _ _ (by simp; omega), wordToBits_length]
      have hb' : b - w < n * w := by rw [Nat.succ_mul] at hb; omega
      rw [ih (fun j => H j.succ) (b - w) hb']
      have e1 : (b - w) / w + 1 = b / w := by
        rw [← Nat.sub_add_cancel (show w ≤ b by omega), Nat.add_div_right _ hw]
        simp
      have e2 : (b - w) % w = b % w := by
        conv_rhs => rw [← Nat.sub_add_cancel (show w ≤ b by omega)]
        simp
      simp only [e2]
      congr 2
      ext; simp only [Fin.val_succ]; exact e1

end OcamlPq.Hash.Sha2
