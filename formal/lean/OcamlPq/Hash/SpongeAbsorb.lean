import OcamlPq.Hash.KeccakPermute
import OcamlPq.Hash.SpongeLemmas

/-!
# The absorbing phase of `sponge`

`absorb_eq`: the state that `lib/keccak.ml` `sponge` holds after absorbing
the input (lines 88–101) is, as a FIPS 202 string, the state `S` of
Algorithm 8 after step 6, for `N = M ‖ ds` and `pad = pad10*1`, whenever the
suffix byte encodes `ds` followed by the first `1` of the padding
(`SuffixOK`). In particular the byte-level tail
(`tail.(rem) ← suffix`, `tail.(rate−1) ← tail.(rate−1) lor 0x80`), including
the case `rem = rate − 1` where both land in one byte, is exactly the last
block of `M ‖ ds ‖ pad10*1`.
-/

namespace OcamlPq.Hash.Keccak

open FIPS202

/-- The suffix byte `suffix` encodes the FIPS 202 domain bits `ds` followed by
the first `1` of `pad10*1`: bit `k` of `suffix` is `ds[k]` for `k < |ds|`,
`1` for `k = |ds|` and `0` above. `|ds| ≤ 6`, so bit 7 is clear. -/
structure SuffixOK (suffix : ℕ) (ds : Bits) : Prop where
  len : ds.length ≤ 6
  lt : suffix < 128
  bit : ∀ k < 8, suffix.testBit k = if h : k < ds.length then ds[k] else decide (k = ds.length)

/-- SHA-3: `suffix = 0x06` encodes `01` (§6.1). -/
theorem suffixOK_sha3 : SuffixOK 0x06 [false, true] :=
  ⟨by decide, by decide, by decide⟩

/-- SHAKE: `suffix = 0x1f` encodes `1111` (§6.2). -/
theorem suffixOK_shake : SuffixOK 0x1f [true, true, true, true] :=
  ⟨by decide, by decide, by decide⟩

/-! ## Byte strings, blocks, and `xor_block` -/

theorem bytesToBits_drop (bs : List UInt8) (n : ℕ) :
    (bytesToBits bs).drop (8 * n) = bytesToBits (bs.drop n) := by
  induction bs generalizing n with
  | nil => simp
  | cons b bs ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [bytesToBits_cons, show 8 * (n + 1) = 8 + 8 * n by ring, ← List.drop_drop,
        List.drop_left' (by simp), ih]
      rfl

theorem bytesToBits_take (bs : List UInt8) (n : ℕ) :
    (bytesToBits bs).take (8 * n) = bytesToBits (bs.take n) := by
  induction bs generalizing n with
  | nil => simp
  | cons b bs ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [bytesToBits_cons, show 8 * (n + 1) = 8 + 8 * n by ring, List.take_add,
        List.take_left' (by simp), List.drop_left' (by simp), ih]
      rfl

@[simp] theorem laneBits_replicate_zero : laneBits (Array.replicate 25 0) = List.replicate 1600 false := by
  apply List.ext_getElem (by rw [laneBits_length, List.length_replicate])
  intro k h1 h2
  have hk : k < 1600 := by rw [laneBits_length] at h1; exact h1
  simp only [laneBits, List.getElem_ofFn, List.getElem_replicate]
  rw [getElem!_pos _ _ (by rw [Array.size_replicate]; omega)]
  simp

/-- `xor_block` of a `rate`-byte block XORs the block's bits into the first
`8 · rate` bits of the state: `S ⊕ (P ‖ 0^c)`. -/
theorem laneBits_xorBlock (st : Array (BitVec 64)) (hst : st.size = 25) (blk : List UInt8)
    (r : ℕ) (hlen : blk.length = r) (hr8 : r % 8 = 0) (hr : r ≤ 200) :
    laneBits (xorBlock st blk) =
      xorBits (laneBits st) (bytesToBits blk ++ List.replicate (b - 8 * r) false) := by
  apply List.ext_getElem
  · simp [xorBits, b, hlen]; omega
  · intro k h1 h2
    have hk : k < 1600 := by rw [laneBits_length] at h1; exact h1
    simp only [laneBits, List.getElem_ofFn, xorBits, List.getElem_zipWith]
    rw [xorBlock_get, hst, hlen]
    by_cases hkr : k < 8 * r
    · rw [ite_eq_left ⟨by omega, by omega⟩, BitVec.getLsbD_xor, getLsbD_load64Le _ _ _ (by omega),
        List.getElem_append_left (by simp [hlen]; omega), bytesToBits_getElem]
      have e1 : 8 * (k / 64) + k % 64 / 8 = k / 8 := by omega
      have e2 : k % 64 % 8 = k % 8 := by omega
      rw [e1, e2, getElem!_pos blk (k / 8) (by omega)]
    · rw [ite_eq_right (by omega), List.getElem_append_right (by simp [hlen]; omega)]
      simp

/-! ## The padded message `P = M ‖ ds ‖ pad10*1(8·rate, |M ‖ ds|)` -/

section padding
variable (r : ℕ) (M : List UInt8) (ds : Bits)

theorem pad101_length (x m : ℕ) : (pad101 x m).length = ((-(m : ℤ) - 2) % (x : ℤ)).toNat + 2 := by
  simp [pad101]

/-- The number of zeros in `pad10*1` for the byte-aligned case. -/
theorem pad101_zeros (hr : 0 < r) (hds : ds.length ≤ 6) :
    ((-((8 * M.length + ds.length : ℕ) : ℤ) - 2) % ((8 * r : ℕ) : ℤ)).toNat =
      8 * r - (8 * (M.length % r) + ds.length + 2) := by
  have hdm := Nat.div_add_mod M.length r
  have hlt := Nat.mod_lt M.length hr
  set q := M.length / r
  set m := M.length % r
  have hbound : 8 * m + ds.length + 2 ≤ 8 * r := by omega
  have key : (-((8 * M.length + ds.length : ℕ) : ℤ) - 2) =
      ((8 * r - (8 * m + ds.length + 2) : ℕ) : ℤ) + ((8 * r : ℕ) : ℤ) * (-(q + 1 : ℤ)) := by
    rw [← hdm]; push_cast [hbound]; ring
  rw [key, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by push_cast; omega)]
  simp

/-- `|P| = (⌊|M| / rate⌋ + 1) · 8 · rate`: the padded message is exactly one
block longer than the full input blocks. -/
theorem padded_length (hr : 0 < r) (hds : ds.length ≤ 6) :
    (bytesToBits M ++ ds ++ pad101 (8 * r) (bytesToBits M ++ ds).length).length =
      (M.length / r + 1) * (8 * r) := by
  simp only [List.length_append, bytesToBits_length, pad101_length]
  rw [pad101_zeros r M ds hr hds]
  have hdm := Nat.div_add_mod M.length r
  have hlt := Nat.mod_lt M.length hr
  set q := M.length / r
  set m := M.length % r
  have : 8 * m + ds.length + 2 ≤ 8 * r := by omega
  rw [← hdm]
  have e : (q + 1) * (8 * r) = 8 * (r * q) + 8 * r := by ring
  rw [e]
  omega

end padding

/-! ## The byte-level tail block -/

/-- The tail block that `sponge` builds (`lib/keccak.ml` lines 94–99). -/
def tailBlock (rate suffix : ℕ) (input : List UInt8) : List UInt8 :=
  let fullBlocks := input.length / rate
  let rem := input.length % rate
  let tail := List.replicate rate (0 : UInt8)
  let tail := blitString input (fullBlocks * rate) tail 0 rem
  let tail := tail.set rem (UInt8.ofNat suffix)
  tail.set (rate - 1) (UInt8.ofNat (tail[rate - 1]!.toNat ||| 0x80))

theorem absorb_eq_tail (rate suffix : ℕ) (input : List UInt8) :
    absorb rate suffix input =
      permute (xorBlock ((List.range (input.length / rate)).foldl (fun st block =>
        permute (xorBlock st (stringSub input (block * rate) rate))) (Array.replicate 25 0))
        (tailBlock rate suffix input)) := rfl

theorem tailBlock_length (rate suffix : ℕ) (input : List UInt8) :
    (tailBlock rate suffix input).length = rate := by
  simp [tailBlock, blitString_length]

theorem testBit_128 (k : ℕ) (hk : k < 8) : (128 : ℕ).testBit k = decide (k = 7) := by
  interval_cases k <;> decide

/-- The bytes of the tail block: message bytes, then the suffix byte, then
zeros, with `0x80` OR-ed into the last byte. -/
theorem tailBlock_toNat (rate suffix : ℕ) (input : List UInt8) (hr : 0 < rate)
    (hs : suffix < 128) (j : ℕ) (hj : j < rate) :
    ((tailBlock rate suffix input)[j]!).toNat =
      (if j < input.length % rate then (input[input.length / rate * rate + j]!).toNat
        else if j = input.length % rate then suffix else 0) |||
      (if j = rate - 1 then 128 else 0) := by
  have hrem := Nat.mod_lt input.length hr
  have hs256 : suffix < 256 := by omega
  simp only [tailBlock]
  rw [List.getElem!_set']
  simp only [List.length_set, blitString_length, List.length_replicate]
  -- value of the byte after the `blit` and the `suffix` store
  have hmid : ∀ i, i < rate →
      (((blitString input (input.length / rate * rate) (List.replicate rate 0) 0
          (input.length % rate)).set (input.length % rate) (UInt8.ofNat suffix))[i]!).toNat =
      if i < input.length % rate then (input[input.length / rate * rate + i]!).toNat
      else if i = input.length % rate then suffix else 0 := by
    intro i hi
    rw [List.getElem!_set', blitString_length, List.length_replicate, blitString_get,
      List.length_replicate, List.getElem!_replicate_zero]
    by_cases h1 : input.length % rate = i
    · subst h1
      rw [ite_eq_left ⟨rfl, hi⟩, ite_eq_right (by omega), ite_eq_left rfl]
      simp [Nat.mod_eq_of_lt hs256]
    · rw [ite_eq_right (by omega), ite_eq_right (Ne.symm h1)]
      by_cases h2 : i < input.length % rate
      · rw [ite_eq_left ⟨by omega, by omega, by omega⟩, ite_eq_left h2, Nat.sub_zero]
      · rw [ite_eq_right (by omega), ite_eq_right h2]; rfl
  by_cases hl : rate - 1 = j
  · subst hl
    rw [ite_eq_left ⟨rfl, hj⟩, ite_eq_left rfl]
    have hlt : ((((blitString input (input.length / rate * rate) (List.replicate rate 0) 0
          (input.length % rate)).set (input.length % rate) (UInt8.ofNat suffix))[rate - 1]!).toNat |||
          0x80) < 256 :=
      Nat.or_lt_two_pow (n := 8) (UInt8.toNat_lt _) (by norm_num)
    simp only [UInt8.toNat_ofNat', show 2 ^ 8 = 256 from rfl, Nat.mod_eq_of_lt hlt]
    rw [hmid _ hj]
  · rw [ite_eq_right (by omega), hmid _ hj, ite_eq_right (Ne.symm hl), Nat.or_zero]

/-! ## The blocks of `P` -/

/-- FIPS 202 Algorithm 8 step 1 for `N = M ‖ ds`, `x = 8 · rate`:
`P = N ‖ pad10*1(8·rate, |N|)`. -/
def padded (r : ℕ) (M : List UInt8) (ds : Bits) : Bits :=
  bytesToBits M ++ ds ++ pad101 (8 * r) (bytesToBits M ++ ds).length

theorem pad101_getElem (x m t : ℕ) (ht : t < (pad101 x m).length) :
    (pad101 x m)[t] = decide (t = 0 ∨ t = (pad101 x m).length - 1) := by
  unfold pad101 at ht ⊢
  generalize ((-(m : ℤ) - 2) % (x : ℤ)).toNat = j at ht ⊢
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate] at ht ⊢
  by_cases h0 : t = 0
  · subst h0; simp
  · by_cases hl : t = j + 1
    · subst hl
      rw [List.getElem_append_right (by simp)]
      simp; omega
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      simp only [List.length_cons, List.length_nil, List.getElem_replicate]
      simp; omega

/-- Full input block `i` of `P` is the bit string of `String.sub input (i·rate) rate`. -/
theorem padded_block_full (r : ℕ) (M : List UInt8) (ds : Bits) (i : ℕ) (hi : i < M.length / r) :
    ((padded r M ds).drop (i * (8 * r))).take (8 * r) = bytesToBits (stringSub M (i * r) r) := by
  have h1 : (i + 1) * r ≤ M.length :=
    le_trans (Nat.mul_le_mul_right r hi) (Nat.div_mul_le_self M.length r)
  have e : i * (8 * r) = 8 * (i * r) := by ring
  have h2 : (i + 1) * r = i * r + r := by ring
  unfold padded
  rw [List.append_assoc, e, List.drop_append_of_le_length (by simp; omega),
    List.take_append_of_le_length (by simp; omega), bytesToBits_drop, bytesToBits_take]
  rfl

/-- The last block of `P` is the bit string of the tail block. -/
theorem padded_block_last (r suffix : ℕ) (M : List UInt8) (ds : Bits) (hr : 0 < r)
    (hs : SuffixOK suffix ds) :
    ((padded r M ds).drop (M.length / r * (8 * r))).take (8 * r) =
      bytesToBits (tailBlock r suffix M) := by
  have hdm := Nat.div_add_mod M.length r
  have hlt := Nat.mod_lt M.length hr
  have hℓ := hs.len
  have hlenP : (padded r M ds).length = (M.length / r + 1) * (8 * r) :=
    padded_length r M ds hr hs.len
  have hpl := pad101_length (8 * r) (bytesToBits M ++ ds).length
  simp only [List.length_append, bytesToBits_length] at hpl
  rw [pad101_zeros r M ds hr hℓ] at hpl
  set q := M.length / r with hq
  set m := M.length % r with hm
  have e1 : q * (8 * r) = 8 * (q * r) := by ring
  have e2 : (q + 1) * (8 * r) = 8 * (q * r) + 8 * r := by ring
  have h8len : 8 * M.length = 8 * (q * r) + 8 * m := by rw [← hdm]; ring
  have hdm' : q * r + m = M.length := by rw [Nat.mul_comm]; exact hdm
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, bytesToBits_length, tailBlock_length]
    rw [hlenP]; omega
  intro k hk1 hk2
  have hk : k < 8 * r := by simpa [tailBlock_length] using hk2
  rw [List.getElem_take, List.getElem_drop, bytesToBits_getElem,
    ← getElem!_pos (tailBlock r suffix M) (k / 8) (by rw [tailBlock_length]; omega),
    tailBlock_toNat r suffix M hr hs.lt (k / 8) (by omega), Nat.testBit_or, ← hq, ← hm]
  have h128 : ∀ c : ℕ, c = 128 ∨ c = 0 → c.testBit (k % 8) = decide (c = 128 ∧ k % 8 = 7) := by
    rintro c (rfl | rfl)
    · rw [testBit_128 _ (by omega)]; simp
    · simp
  rw [h128 (if k / 8 = r - 1 then 128 else 0) (by split <;> simp)]
  unfold padded
  by_cases hA : k < 8 * m
  · -- a message bit
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      bytesToBits_getElem, ite_eq_left (show k / 8 < m by omega), getElem!_pos M _ (by omega)]
    have : ¬ ((if k / 8 = r - 1 then 128 else 0 : ℕ) = 128 ∧ k % 8 = 7) := by
      rintro ⟨h, -⟩; split at h <;> omega
    rw [decide_eq_false this, Bool.or_false]
    have i1 : (q * (8 * r) + k) / 8 = q * r + k / 8 := by omega
    have i2 : (q * (8 * r) + k) % 8 = k % 8 := by omega
    simp only [i1, i2]
  by_cases hB : k < 8 * m + ds.length
  · -- a domain-separation bit
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega),
      ite_eq_right (show ¬ k / 8 < m by omega), ite_eq_left (show k / 8 = m by omega),
      hs.bit _ (by omega), dite_eq_left (by omega)]
    have : ¬ ((if k / 8 = r - 1 then 128 else 0 : ℕ) = 128 ∧ k % 8 = 7) := by
      rintro ⟨-, h⟩; omega
    rw [decide_eq_false this, Bool.or_false]
    congr 1
    simp only [bytesToBits_length]; omega
  · -- a padding bit
    rw [List.getElem_append_right (by simp; omega), pad101_getElem]
    simp only [List.length_append, bytesToBits_length]
    rw [hpl]
    by_cases hk8 : k / 8 = m
    · rw [ite_eq_right (show ¬ k / 8 < m by omega), ite_eq_left hk8, hs.bit _ (by omega),
        dite_eq_right (by omega)]
      rw [Bool.eq_iff_iff]
      split <;> simp <;> omega
    · rw [ite_eq_right (show ¬ k / 8 < m by omega), ite_eq_right hk8, Nat.zero_testBit,
        Bool.false_or]
      rw [Bool.eq_iff_iff]
      split <;> simp <;> omega

/-! ## The absorbing phase -/

theorem stringSub_length (M : List UInt8) (r i : ℕ) (hi : i < M.length / r) :
    (stringSub M (i * r) r).length = r := by
  have h1 : (i + 1) * r ≤ M.length :=
    le_trans (Nat.mul_le_mul_right r hi) (Nat.div_mul_le_self M.length r)
  have h2 : (i + 1) * r = i * r + r := by ring
  simp only [stringSub, List.length_take, List.length_drop]
  omega

/-- **Absorbing.** After `sponge` has absorbed the full input blocks and the
padded tail block (`lib/keccak.ml` lines 88–101), its state, as a FIPS 202
string, is the `S` of Algorithm 8 after step 6 for `N = M ‖ ds`,
`pad = pad10*1` and `r = 8 · rate`. -/
theorem absorb_spec (r suffix : ℕ) (ds : Bits) (M : List UInt8) (hr : 0 < r) (hr8 : r % 8 = 0)
    (hr200 : r ≤ 200) (hs : SuffixOK suffix ds) :
    (absorb r suffix M).size = 25 ∧
    laneBits (absorb r suffix M) =
      (List.range ((padded r M ds).length / (8 * r))).foldl
        (fun S i => KeccakF (xorBits S (((padded r M ds).drop (i * (8 * r))).take (8 * r) ++
          List.replicate (b - 8 * r) false)))
        (List.replicate b false) := by
  have hlenP : (padded r M ds).length = (M.length / r + 1) * (8 * r) :=
    padded_length r M ds hr hs.len
  rw [hlenP, Nat.mul_div_cancel _ (by omega : 0 < 8 * r), List.range_succ, List.foldl_append,
    absorb_eq_tail]
  simp only [List.foldl_cons, List.foldl_nil]
  have hA := foldl_rel (List.range (M.length / r))
    (fun st block => permute (xorBlock st (stringSub M (block * r) r)))
    (fun S i => KeccakF (xorBits S (((padded r M ds).drop (i * (8 * r))).take (8 * r) ++
      List.replicate (b - 8 * r) false)))
    laneBits (fun st => st.size = 25)
    (fun st i hi hst => by
      have hi' := List.mem_range.mp hi
      refine ⟨permute_size _ (by rw [xorBlock_size]; exact hst), ?_⟩
      rw [permute_eq_KeccakF _ (by rw [xorBlock_size]; exact hst),
        laneBits_xorBlock _ hst _ r (stringSub_length M r i hi') hr8 hr200,
        padded_block_full r M ds i hi'])
    (Array.replicate 25 0) (by simp)
  refine ⟨permute_size _ (by rw [xorBlock_size]; exact hA.1), ?_⟩
  rw [permute_eq_KeccakF _ (by rw [xorBlock_size]; exact hA.1),
    laneBits_xorBlock _ hA.1 _ r (tailBlock_length r suffix M) hr8 hr200, hA.2,
    laneBits_replicate_zero, padded_block_last r suffix M ds hr hs]
  rfl

end OcamlPq.Hash.Keccak
