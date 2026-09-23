import OcamlPq.MLKEMAlg.Params

/-!
# `ct_equal` and `select_secret`

`ct_equal` (lib/mlkem_engine.ml:411-417) compares two strings with an
`Int32` bit trick. `select_secret` (lib/mlkem_engine.ml:474-482) chooses
between two 32-byte strings with an arithmetic mask. `decapsulate` combines
them for implicit rejection.
-/

namespace OcamlPq.MLKEMAlg

/-! ## `ct_equal` -/

/-- The accumulation loop of `ct_equal` (lib/mlkem_engine.ml:412-415):
    `diff := !diff lor (get_u8 a i lxor get_u8 b i)` for `i < String.length a`.
    All values are non-negative, so they are modelled in `ℕ`. -/
def ctDiff (a b : Bytes) : ℕ :=
  (List.range a.length).foldl (fun diff i => diff ||| (getU8 a i ^^^ getU8 b i)) 0

/-- The final step of `ct_equal` (lib/mlkem_engine.ml:416-417):
    `Int32.to_int (Int32.logand (Int32.shift_right_logical (Int32.logor d (Int32.neg d)) 31) 1l) lxor 1`
    with `d = Int32.of_int diff`. -/
def ctFinal (diff : ℕ) : ℤ :=
  let d : BitVec 32 := BitVec.ofInt 32 diff
  Int.xor (((d ||| -d) >>> 31) &&& 1#32).toInt 1

/-- `ct_equal a b` (lib/mlkem_engine.ml:411-417). -/
def ctEqual (a b : Bytes) : ℤ := ctFinal (ctDiff a b)

theorem foldl_or_eq_zero (f : ℕ → ℕ) (L : List ℕ) (acc : ℕ) :
    L.foldl (fun d i => d ||| f i) acc = 0 ↔ acc = 0 ∧ ∀ i ∈ L, f i = 0 := by
  induction L generalizing acc with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldl_cons, ih, Nat.or_eq_zero_iff, List.mem_cons, forall_eq_or_imp]
    tauto

theorem foldl_or_lt (f : ℕ → ℕ) (hf : ∀ i, f i < 256) (L : List ℕ) (acc : ℕ) (hacc : acc < 256) :
    L.foldl (fun d i => d ||| f i) acc < 256 := by
  induction L generalizing acc with
  | nil => simpa
  | cons x L ih =>
    exact ih _ (Nat.or_lt_two_pow (n := 8) hacc (hf x))

theorem ctDiff_lt (a b : Bytes) : ctDiff a b < 256 :=
  foldl_or_lt _ (fun i => Nat.xor_lt_two_pow (n := 8) (getU8_lt a i) (getU8_lt b i)) _ _ (by norm_num)

/-- The `Int32` trick maps `0` to `1` and every other byte-sized value to `0`. -/
theorem ctFinal_eq : ∀ x : Fin 256, ctFinal x = if x.val = 0 then 1 else 0 := by
  unfold ctFinal; decide +kernel

theorem ctDiff_eq_zero_iff (a b : Bytes) (hlen : a.length = b.length) : ctDiff a b = 0 ↔ a = b := by
  unfold ctDiff
  rw [foldl_or_eq_zero]
  simp only [true_and, List.mem_range, Nat.xor_eq_zero_iff]
  constructor
  · intro h
    apply List.ext_getElem hlen
    intro i h1 h2
    have := h i h1
    rw [getU8_of_lt h1, getU8_of_lt h2] at this
    exact Fin.ext this
  · rintro rfl i _; rfl

/-- **`ct_equal` correctness.** For strings of equal length, `ct_equal`
    returns 1 if they are equal and 0 otherwise. -/
theorem ctEqual_spec (a b : Bytes) (hlen : a.length = b.length) :
    ctEqual a b = if a = b then 1 else 0 := by
  unfold ctEqual
  have h := ctFinal_eq ⟨ctDiff a b, ctDiff_lt a b⟩
  simp only at h
  rw [h]
  by_cases hab : a = b
  · rw [ite_eq_left ((ctDiff_eq_zero_iff a b hlen).2 hab), ite_eq_left hab]
  · rw [ite_eq_right (fun h => hab ((ctDiff_eq_zero_iff a b hlen).1 h)), ite_eq_right hab]

/-- `ct_equal` reads `b` only below `String.length a` (`unsafe_get`); with
    equal lengths every read is in bounds, and `diff` is a byte. -/
theorem ctEqual_portable (a b : Bytes) (hlen : a.length = b.length) (i : ℕ) (hi : i < a.length) :
    i < b.length ∧ Portable (ctDiff a b : ℤ) :=
  ⟨hlen ▸ hi, Portable.of_nat_lt (by have := ctDiff_lt a b; omega)⟩

/-! ## `select_secret` -/

/-- The byte written by `select_secret` (lib/mlkem_engine.ml:479-480). -/
def selectByte (mask l r : ℤ) : ℤ := Int.lor (Int.land l (Int.lnot mask)) (Int.land r mask)

/-- `select_secret ~choose_left left right` (lib/mlkem_engine.ml:474-482).
    `garbage` is the uninitialised content of `Bytes.create`. -/
def selectSecret (garbage : ℕ → Byte) (chooseLeft : ℤ) (left right : Bytes) : Bytes :=
  let nz := Int.xor chooseLeft 1
  let mask := -nz
  let out := (List.range 32).foldl
    (fun out i => setU8 out i (selectByte mask (getU8 left i) (getU8 right i))) garbage
  bufToList out 0 32

theorem Int.land_natCast_neg_one (m : ℕ) : Int.land m (-1) = m := by
  show Int.land (Int.ofNat m) (Int.negSucc 0) = _
  simp only [Int.land, Nat.cast_inj]
  exact Nat.eq_of_testBit_eq fun i => by simp [Nat.testBit_ldiff]

theorem Int.land_natCast_zero (m : ℕ) : Int.land m 0 = 0 := by
  show Int.land (Int.ofNat m) (Int.ofNat 0) = _
  simp [Int.land]

theorem Int.lor_natCast_zero (m : ℕ) : Int.lor m 0 = m := by
  show Int.lor (Int.ofNat m) (Int.ofNat 0) = _
  simp [Int.lor]

theorem Int.lor_zero_natCast (m : ℕ) : Int.lor 0 m = m := by
  show Int.lor (Int.ofNat 0) (Int.ofNat m) = _
  simp [Int.lor]

theorem Int.land_natCast_255 (m : ℕ) (h : m < 256) : Int.land m 0xff = m := by
  show Int.land (Int.ofNat m) (Int.ofNat 255) = _
  simp only [Int.land, Nat.cast_inj]
  rw [show (255 : ℕ) = 2 ^ 8 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem selectByte_left (l r : ℕ) : selectByte (-(Int.xor 1 1)) l r = l := by
  have h1 : Int.xor 1 1 = 0 := by decide
  have h2 : Int.lnot 0 = -1 := rfl
  simp only [selectByte, h1, neg_zero, h2, Int.land_natCast_neg_one, Int.land_natCast_zero,
    Int.lor_natCast_zero]

theorem selectByte_right (l r : ℕ) : selectByte (-(Int.xor 0 1)) l r = r := by
  have h1 : Int.xor 0 1 = 1 := by decide
  have h2 : Int.lnot (-1) = 0 := rfl
  simp only [selectByte, h1, h2, Int.land_natCast_neg_one, Int.land_natCast_zero,
    Int.lor_zero_natCast]

/-- **`select_secret` correctness.** With `choose_left ∈ {0, 1}` and two
    strings of at least 32 bytes, `select_secret` returns the first 32 bytes
    of `left` if `choose_left = 1` and of `right` otherwise, whatever the
    uninitialised buffer held. -/
theorem selectSecret_spec (garbage : ℕ → Byte) (c : ℤ) (hc : c = 0 ∨ c = 1) (left right : Bytes)
    (hl : 32 ≤ left.length) (hr : 32 ≤ right.length) :
    selectSecret garbage c left right = if c = 1 then left.take 32 else right.take 32 := by
  unfold selectSecret
  dsimp only
  simp only [setU8, bytesSet]
  rw [foldl_update_eq]
  apply List.ext_getElem
  · split_ifs <;> simp <;> omega
  · intro i h1 h2
    simp only [bufToList_length] at h1
    simp only [bufToList, List.getElem_ofFn, zero_add, List.mem_range, ite_eq_left h1]
    rcases hc with rfl | rfl
    · simp only [show ¬((0 : ℤ) = 1) by decide, ite_false, List.getElem_take]
      rw [selectByte_right, Int.land_natCast_255 _ (getU8_lt _ _), getU8_of_lt (by omega)]
      exact Fin.ext (unsafeChr_val_nat (Fin.isLt _))
    · simp only [ite_true, List.getElem_take]
      rw [selectByte_left, Int.land_natCast_255 _ (getU8_lt _ _), getU8_of_lt (by omega)]
      exact Fin.ext (unsafeChr_val_nat (Fin.isLt _))

/-- **Implicit-rejection selection.** The last line of `decapsulate`,
    `select_secret ~choose_left:(ct_equal c c') candidate rejection`, returns
    `candidate` if `c = c'` and `rejection` otherwise (for equal-length
    ciphertexts and 32-byte secrets). -/
theorem select_ctEqual (garbage : ℕ → Byte) (c c' candidate rejection : Bytes)
    (hlen : c.length = c'.length) (h1 : candidate.length = 32) (h2 : rejection.length = 32) :
    selectSecret garbage (ctEqual c c') candidate rejection = if c = c' then candidate else rejection := by
  rw [ctEqual_spec c c' hlen]
  by_cases h : c = c'
  · rw [ite_eq_left h, selectSecret_spec _ _ (Or.inr rfl) _ _ (by omega) (by omega), ite_eq_left rfl,
      ite_eq_left h, List.take_of_length_le (by omega)]
  · rw [ite_eq_right h, selectSecret_spec _ _ (Or.inl rfl) _ _ (by omega) (by omega),
      ite_eq_right (by decide), ite_eq_right h, List.take_of_length_le (by omega)]

end OcamlPq.MLKEMAlg
