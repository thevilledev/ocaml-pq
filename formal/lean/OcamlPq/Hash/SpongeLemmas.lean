import OcamlPq.Hash.KeccakModel
import OcamlPq.Hash.KeccakSpec
import OcamlPq.Hash.ArrayLemmas

/-!
# Byte-level lemmas for the sponge

Characterisations of the byte loops of `lib/keccak.ml`: `load64_le`,
`store64_le`, `xor_block`, `Bytes.blit_string`, and of FIPS 202's byte-to-bit
conversion.
-/

namespace OcamlPq.Hash

open FIPS202 Keccak

/-! ## Generic loop lemmas -/

/-- A `for i = 0 to n - 1 do l.(off + i) <- v i done` loop on a list. -/
theorem foldl_set_range {α : Type*} [Inhabited α] (n off : ℕ) (v : ℕ → α) (l : List α) :
    ((List.range n).foldl (fun l i => l.set (off + i) (v i)) l).length = l.length ∧
    ∀ j, ((List.range n).foldl (fun l i => l.set (off + i) (v i)) l)[j]! =
      if off ≤ j ∧ j < off + n ∧ j < l.length then v (j - off) else l[j]! := by
  induction n with
  | zero =>
    refine ⟨rfl, fun j => ?_⟩
    rw [ite_eq_right (by omega)]
    rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, List.length_set]
    refine ⟨ih.1, fun j => ?_⟩
    by_cases hj : j < l.length
    · rw [getElem!_pos _ j (by rw [List.length_set, ih.1]; exact hj), List.getElem_set,
        ← getElem!_pos _ j (by rw [ih.1]; exact hj), ih.2 j]
      by_cases h1 : off + n = j
      · subst h1
        rw [ite_eq_left rfl, ite_eq_left (by omega), Nat.add_sub_cancel_left]
      · rw [ite_eq_right h1]
        by_cases hc : off ≤ j ∧ j < off + n ∧ j < l.length
        · rw [ite_eq_left hc, ite_eq_left (by omega)]
        · rw [ite_eq_right hc, ite_eq_right (by omega)]
    · rw [getElem!_neg _ j (by rw [List.length_set, ih.1]; exact hj), getElem!_neg _ j hj]
      rw [ite_eq_right (by omega)]

/-- A `for i = 0 to n - 1 do st.(i) <- f i st.(i) done` loop on an array. -/
theorem foldl_set!_self {α : Type*} [Inhabited α] (n : ℕ) (f : ℕ → α → α) (st : Array α) :
    ((List.range n).foldl (fun st i => st.set! i (f i st[i]!)) st).size = st.size ∧
    ∀ j, ((List.range n).foldl (fun st i => st.set! i (f i st[i]!)) st)[j]! =
      if j < n ∧ j < st.size then f j st[j]! else st[j]! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [Array.size_set!, ih.1], fun j => ?_⟩
    rw [Array.getElem!_set!, ih.1, ih.2 j, ih.2 n]
    by_cases h1 : n = j
    · subst h1
      by_cases hs : n < st.size
      · rw [ite_eq_left ⟨rfl, hs⟩, ite_eq_right (by omega), ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega)]
      by_cases hc : j < n ∧ j < st.size
      · rw [ite_eq_left hc, ite_eq_left (by omega)]
      · rw [ite_eq_right hc, ite_eq_right (by omega)]

/-! ## Bytes and bits -/

theorem UInt8.testBit_ge (b : UInt8) {i : ℕ} (hi : 8 ≤ i) : b.toNat.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le b.toNat_lt (Nat.pow_le_pow_right (by norm_num) hi))

@[simp] theorem bytesToBits_nil : bytesToBits [] = [] := rfl

theorem bytesToBits_cons (b : UInt8) (bs : List UInt8) :
    bytesToBits (b :: bs) = ((List.range 8).map fun i => b.toNat.testBit i) ++ bytesToBits bs := by
  simp [bytesToBits]

theorem bytesToBits_append (bs cs : List UInt8) :
    bytesToBits (bs ++ cs) = bytesToBits bs ++ bytesToBits cs := by
  simp [bytesToBits]

@[simp] theorem bytesToBits_length (bs : List UInt8) : (bytesToBits bs).length = 8 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [bytesToBits_cons]; simp [ih]; ring

/-- Bit `k` of the FIPS 202 bit string of `bs` is bit `k mod 8` of byte `k / 8`. -/
theorem bytesToBits_getElem (bs : List UInt8) (k : ℕ) (hk : k < (bytesToBits bs).length) :
    (bytesToBits bs)[k] =
      (bs[k / 8]'(by rw [bytesToBits_length] at hk; omega)).toNat.testBit (k % 8) := by
  induction bs generalizing k with
  | nil => simp at hk
  | cons b bs ih =>
    simp only [bytesToBits_cons]
    by_cases h8 : k < 8
    · rw [List.getElem_append_left (by simpa using h8)]
      simp [Nat.div_eq_of_lt h8, Nat.mod_eq_of_lt h8]
    · rw [List.getElem_append_right (by simpa using h8)]
      simp only [List.length_map, List.length_range]
      rw [ih (k - 8) (by simp [bytesToBits_length] at hk ⊢; omega)]
      have h1 : k / 8 = (k - 8) / 8 + 1 := by omega
      have h2 : (k - 8) % 8 = k % 8 := by omega
      simp only [h1, h2, List.getElem_cons_succ]

theorem bytesToBits_eq_ofFn (bs : List UInt8) :
    bytesToBits bs = List.ofFn fun k : Fin (8 * bs.length) =>
      (bs[k.val / 8]'(by omega)).toNat.testBit (k.val % 8) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  rw [bytesToBits_getElem, List.getElem_ofFn]

/-! ## `load64_le`, `store64_le`, `xor_block`, `blit_string` -/

theorem getLsbD_int64OfByte (b : UInt8) (i : ℕ) :
    (int64OfByte b).getLsbD i = b.toNat.testBit i := by
  simp only [int64OfByte, BitVec.getLsbD_ofNat]
  by_cases hi : i < 64
  · simp [hi]
  · simp [hi, UInt8.testBit_ge b (show 8 ≤ i by omega)]

set_option maxHeartbeats 1000000 in
/-- Bit `k` of `load64_le s off` is bit `k mod 8` of byte `off + k / 8`. -/
theorem getLsbD_load64Le (s : List UInt8) (off : ℕ) (k : ℕ) (hk : k < 64) :
    (load64Le s off).getLsbD k = (s[off + k / 8]!).toNat.testBit (k % 8) := by
  rw [load64Le, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    getLsbD_int64OfByte]
  interval_cases k <;> simp [UInt8.testBit_ge]

/-- The byte `Char.unsafe_chr (Int64.to_int (logand (shift_right_logical x (8i)) 0xff))`
has bit `t` equal to bit `8i + t` of `x`. -/
theorem testBit_byteOfInt64 (x : BitVec 64) (i t : ℕ) (ht : t < 8) :
    (byteOfInt64 ((x >>> (8 * i)) &&& 0xff#64)).toNat.testBit t = x.getLsbD (8 * i + t) := by
  have hlt : ((x >>> (8 * i)) &&& 0xff#64).toNat < 256 := by
    rw [BitVec.toNat_and]
    exact lt_of_le_of_lt Nat.and_le_right (by decide)
  rw [byteOfInt64, UInt8.toNat_ofNat', show 2 ^ 8 = 256 from rfl, Nat.mod_eq_of_lt hlt,
    BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  have : (0xff#64).getLsbD t = true := by interval_cases t <;> decide
  rw [this, Bool.and_true]

theorem store64Le_length (b : List UInt8) (off : ℕ) (x : BitVec 64) :
    (store64Le b off x).length = b.length :=
  (foldl_set_range 8 off _ b).1

theorem store64Le_get (b : List UInt8) (off : ℕ) (x : BitVec 64) (j : ℕ) :
    (store64Le b off x)[j]! =
      if off ≤ j ∧ j < off + 8 ∧ j < b.length then byteOfInt64 ((x >>> (8 * (j - off))) &&& 0xff#64)
      else b[j]! :=
  (foldl_set_range 8 off (fun i => byteOfInt64 ((x >>> (8 * i)) &&& 0xff#64)) b).2 j

theorem blitString_length (src : List UInt8) (so : ℕ) (dst : List UInt8) (doff len : ℕ) :
    (blitString src so dst doff len).length = dst.length :=
  (foldl_set_range len doff _ dst).1

theorem blitString_get (src : List UInt8) (so : ℕ) (dst : List UInt8) (doff len j : ℕ) :
    (blitString src so dst doff len)[j]! =
      if doff ≤ j ∧ j < doff + len ∧ j < dst.length then src[so + (j - doff)]! else dst[j]! :=
  (foldl_set_range len doff (fun i => src[so + i]!) dst).2 j

theorem xorBlock_size (st : Array (BitVec 64)) (block : List UInt8) :
    (xorBlock st block).size = st.size :=
  (foldl_set!_self (block.length / 8) (fun i v => v ^^^ load64Le block (8 * i)) st).1

theorem xorBlock_get (st : Array (BitVec 64)) (block : List UInt8) (j : ℕ) :
    (xorBlock st block)[j]! =
      if j < block.length / 8 ∧ j < st.size then st[j]! ^^^ load64Le block (8 * j) else st[j]! :=
  (foldl_set!_self (block.length / 8) (fun i v => v ^^^ load64Le block (8 * i)) st).2 j

end OcamlPq.Hash
