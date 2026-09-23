import OcamlPq.Hash.Sha2Bytes

/-!
# `sha256` is FIPS 180-4 SHA-256

`sha256_eq`: for every byte string `M`,
`bytesToBitsBE (sha256 M) = SHA256 (bytesToBitsBE M)` (the FIPS 180-4
hash of the message's bit string), for every content of `Bytes.create 32`.
FIPS 180-4 defines SHA-256 only for `ℓ < 2^64` bits; `sha256_bitLength` shows
that the model's length field is exactly `ℓ = 8·|M|` whenever `|M| < 2^61`,
which holds for every OCaml string (`Sys.max_string_length < 2^57`).
-/

namespace OcamlPq.Hash.Sha2

open FIPS180 Keccak

/-- Discharges list-length side conditions. -/
macro "len_tac" : tactic => `(tactic| first | omega | (simp; omega) | simp)

/-! ## Padding (FIPS 180-4 §5.1.1) -/

/-- `Int64.mul (Int64.of_int len) 8L` is `8·len mod 2^64`. -/
theorem bitLength_eq (len : ℕ) : BitVec.ofNat 64 len * 8#64 = BitVec.ofNat 64 (8 * len) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_comm]

/-- The length field is exact: for `len < 2^61`, `8·len` does not wrap. -/
theorem sha256_bitLength (len : ℕ) (h : len < 2 ^ 61) :
    (BitVec.ofNat 64 len * 8#64).toNat = 8 * len := by
  rw [bitLength_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem sha256Pad_length (M : List UInt8) :
    (sha256Pad M).length = ((M.length + 9 + 63) / 64) * 64 := by
  simp only [sha256Pad]
  rw [(foldl_set_inj 8 _ _ _ (fun i _ i' _ h => by omega)).1]
  simp [blitString_length]

/-- The bytes of the padded message: the input, `0x80`, zeros, and the last
eight bytes big-endian `8·len`. -/
theorem sha256Pad_get (M : List UInt8) (j : ℕ) (hj : j < ((M.length + 9 + 63) / 64) * 64) :
    (sha256Pad M)[j]! =
      if j < M.length then M[j]!
      else if j = M.length then 0x80
      else if ((M.length + 9 + 63) / 64) * 64 - 8 ≤ j then
        byteOfInt64 ((BitVec.ofNat 64 (8 * M.length) >>>
          (8 * (((M.length + 9 + 63) / 64) * 64 - 1 - j))) &&& 0xff#64)
      else 0 := by
  set PL := ((M.length + 9 + 63) / 64) * 64 with hPL
  have hPL9 : M.length + 9 ≤ PL := by omega
  simp only [sha256Pad, ← hPL, bitLength_eq]
  obtain ⟨hl, hset, hkeep⟩ := foldl_set_inj 8 (fun i => PL - 1 - i)
    (fun i => byteOfInt64 ((BitVec.ofNat 64 (8 * M.length) >>> (8 * i)) &&& 0xff#64))
    (((blitString M 0 (List.replicate PL 0) 0 M.length).set M.length 0x80))
    (fun i hi i' hi' h => by omega)
  by_cases hhi : PL - 8 ≤ j
  · have := hset (PL - 1 - j) (by omega)
      (by simp [blitString_length]; omega)
    rw [show PL - 1 - (PL - 1 - j) = j by omega] at this
    rw [this, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hhi]
  · rw [hkeep j (fun i hi => by omega), ite_eq_right hhi, List.getElem!_set', blitString_length,
      List.length_replicate, blitString_get, List.length_replicate, List.getElem!_replicate_zero]
    by_cases h1 : j < M.length
    · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega, by omega⟩, ite_eq_left h1,
        Nat.zero_add, Nat.sub_zero]
    · rw [ite_eq_right h1]
      by_cases h2 : j = M.length
      · rw [ite_eq_left ⟨h2.symm, by omega⟩, ite_eq_left h2]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h2]

theorem testBit_0x80 (t : ℕ) (ht : t < 8) : (0x80 : UInt8).toNat.testBit (7 - t) = decide (t = 0) := by
  interval_cases t <;> decide

/-- **Padding.** The OCaml padded message is FIPS 180-4 §5.1.1 padding of the
message's bit string. -/
theorem sha256Pad_bits (M : List UInt8) : bytesToBitsBE (sha256Pad M) = pad 512 64 (bytesToBitsBE M) := by
  set PL := ((M.length + 9 + 63) / 64) * 64 with hPL
  have hPL9 : M.length + 9 ≤ PL := by omega
  have hPLm : PL % 64 = 0 := by omega
  have hk : ((((512 - 64 : ℕ) : ℤ) - (8 * M.length + 1 : ℕ)) % (512 : ℤ)).toNat =
      8 * PL - 8 * M.length - 65 := by omega
  apply List.ext_getElem
  · simp only [bytesToBitsBE_length, sha256Pad_length, pad, List.length_append, List.length_cons,
      List.length_nil, List.length_replicate, natToBits, wordToBits_length]
    push_cast at hk ⊢
    rw [hk]; omega
  intro b h1 h2
  have hb : b < 8 * PL := by simpa [sha256Pad_length] using h1
  rw [bytesToBitsBE_getElem, ← getElem!_pos (sha256Pad M) (b / 8) (by rw [sha256Pad_length]; omega),
    sha256Pad_get M (b / 8) (by omega)]
  simp only [pad]
  have hlenM : (bytesToBitsBE M).length = 8 * M.length := bytesToBitsBE_length M
  by_cases hA : b < 8 * M.length
  · rw [ite_eq_left (show b / 8 < M.length by omega), List.getElem_append_left (by len_tac),
      List.getElem_append_left (by len_tac), List.getElem_append_left (by len_tac),
      bytesToBitsBE_getElem, getElem!_pos M _ (by omega)]
  by_cases hB : b = 8 * M.length
  · subst hB
    rw [ite_eq_right (by omega), ite_eq_left (by omega), List.getElem_append_left (by len_tac),
      List.getElem_append_left (by len_tac), List.getElem_append_right (by len_tac),
      testBit_0x80 _ (by omega)]
    simp
  have hk' : (((((512 - 64 : ℕ) : ℤ) - ((bytesToBitsBE M).length + 1 : ℕ)) % (512 : ℤ)).toNat) =
      8 * PL - 8 * M.length - 65 := by rw [hlenM]; exact_mod_cast hk
  by_cases hC : b < 8 * PL - 64
  · -- zero padding
    rw [ite_eq_right (show ¬ b / 8 < M.length by omega)]
    rw [List.getElem_append_left (by simp; push_cast at hk' ⊢; omega),
      List.getElem_append_right (by len_tac), List.getElem_replicate]
    by_cases hD : b / 8 = M.length
    · rw [ite_eq_left hD, testBit_0x80 _ (by omega)]
      simp; omega
    · rw [ite_eq_right hD, ite_eq_right (by omega)]
      simp
  · -- the length field
    rw [ite_eq_right (show ¬ b / 8 < M.length by omega), ite_eq_right (show ¬ b / 8 = M.length by omega),
      ite_eq_left (by omega), testBit_byteOfInt64 _ _ _ (by omega),
      List.getElem_append_right (by simp; push_cast at hk' ⊢; omega)]
    simp only [natToBits]
    rw [wordToBits_getElem]
    simp only [hlenM, List.length_append, List.length_cons, List.length_nil, List.length_replicate]
    refine congrArg (BitVec.getLsbD (BitVec.ofNat 64 (8 * M.length))) ?_
    omega

/-! ## Parsing (§5.2.1) and one block -/

/-- **Parsing.** Word `j` of block `i` of the bit string of `padded` is
`get_u32_be padded (64 i + 4 j)`. -/
theorem sha256_parse (padded : List UInt8) :
    parse 32 (bytesToBitsBE padded) =
      (List.range (padded.length / 64)).map fun i => fun j : Fin 16 =>
        getU32Be padded (i * 64 + 4 * j.val) := by
  unfold parse
  rw [bytesToBitsBE_length, show 8 * padded.length / (16 * 32) = padded.length / 64 by omega]
  apply List.map_congr_left
  intro i hi
  funext j
  have hi' := List.mem_range.mp hi
  have hmul : (i + 1) * 64 ≤ padded.length :=
    le_trans (Nat.mul_le_mul_right 64 hi') (Nat.div_mul_le_self _ 64)
  have hj := j.isLt
  rw [getU32Be_eq _ _ (by nlinarith)]
  congr 3
  ring

/-- The SHA-256 parameters of the model's round and schedule loops. -/
theorem sha256Sigma : (∀ x, (fun x => rotr32 x 7 ^^^ (rotr32 x 18 ^^^ (x >>> 3))) x = sigma0_256 x) ∧
    (∀ x, (fun y => rotr32 y 17 ^^^ (rotr32 y 19 ^^^ (y >>> 10))) x = sigma1_256 x) ∧
    (∀ x, (fun a => rotr32 a 2 ^^^ (rotr32 a 13 ^^^ rotr32 a 22)) x = Sigma0_256 x) ∧
    (∀ x, (fun e => rotr32 e 6 ^^^ (rotr32 e 11 ^^^ rotr32 e 25)) x = Sigma1_256 x) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩ <;>
    simp [sigma0_256, sigma1_256, Sigma0_256, Sigma1_256, rotr32, ROTR, SHR, BitVec.xor_assoc]

theorem sha256Block_fst (padded : List UInt8) (h w : Array (BitVec 32)) (i : ℕ) :
    (sha256Block padded (h, w) i).1 =
      addVars h ((List.range 64).foldl (sha256Round (sha256Schedule padded (i * 64) w)) (varsOf h)) := by
  simp only [sha256Block]

theorem sha256Block_snd (padded : List UInt8) (h w : Array (BitVec 32)) (i : ℕ) :
    (sha256Block padded (h, w) i).2 = sha256Schedule padded (i * 64) w := by
  simp only [sha256Block]

theorem sha256Schedule_eq (padded : List UInt8) (base : ℕ) (w : Array (BitVec 32)) :
    sha256Schedule padded base w = (List.range' 16 48).foldl
      (schedStep (fun x => rotr32 x 7 ^^^ (rotr32 x 18 ^^^ (x >>> 3)))
        (fun y => rotr32 y 17 ^^^ (rotr32 y 19 ^^^ (y >>> 10))))
      ((List.range 16).foldl (fun w t => w.set! t (getU32Be padded (base + 4 * t))) w) := by
  unfold sha256Schedule schedStep
  rfl

theorem sha256Round_eq (w : Array (BitVec 32)) :
    sha256Round w = roundStep (fun i => sha256Constants[i]!)
      (fun a => rotr32 a 2 ^^^ (rotr32 a 13 ^^^ rotr32 a 22))
      (fun e => rotr32 e 6 ^^^ (rotr32 e 11 ^^^ rotr32 e 25)) w := by
  funext v i
  unfold sha256Round roundStep
  rfl

/-- **One block.** An iteration of the OCaml block loop is FIPS 180-4
§6.2.2 steps 1–4. -/
theorem sha256Block_spec (padded : List UInt8) (h w : Array (BitVec 32)) (hh : h.size = 8)
    (hw : w.size = 64) (i : ℕ) (H : Fin 8 → BitVec 32) (hH : ∀ j : Fin 8, h[j.val]! = H j) :
    (sha256Block padded (h, w) i).1.size = 8 ∧ (sha256Block padded (h, w) i).2.size = 64 ∧
    ∀ j : Fin 8, (sha256Block padded (h, w) i).1[j.val]! =
      compress sha256Params H (fun j : Fin 16 => getU32Be padded (i * 64 + 4 * j.val)) j := by
  obtain ⟨hs1, hg1⟩ := foldl_set!_const 16 (fun t => getU32Be padded (i * 64 + 4 * t)) w
  have h16 : ∀ t (ht : t < 16),
      ((List.range 16).foldl (fun w t => w.set! t (getU32Be padded (i * 64 + 4 * t))) w)[t]! =
        (fun j : Fin 16 => getU32Be padded (i * 64 + 4 * j.val)) ⟨t, ht⟩ := by
    intro t ht; rw [hg1, ite_eq_left ⟨ht, by omega⟩]
  obtain ⟨hs2, hg2⟩ := sched_spec sha256Params (fun j : Fin 16 => getU32Be padded (i * 64 + 4 * j.val))
    _ _ sha256Sigma.1 sha256Sigma.2.1 64 _ (by rw [hs1, hw]) h16 48 (by norm_num)
  rw [← sha256Schedule_eq] at hs2 hg2
  have hrounds := rounds_spec sha256Params
    (schedule sha256Params (fun j : Fin 16 => getU32Be padded (i * 64 + 4 * j.val)))
    (fun t => sha256Constants[t]!) _ _ (sha256Schedule padded (i * 64) w) 64
    (fun t ht => sha256Constants_eq t ht) (fun t ht => hg2 t ht)
    sha256Sigma.2.2.1 sha256Sigma.2.2.2 (varsOf h)
  rw [← sha256Round_eq] at hrounds
  rw [sha256Block_fst, sha256Block_snd, addVars_size, hh, hs2]
  refine ⟨rfl, rfl, fun j => ?_⟩
  exact compress_eq sha256Params H _ h hh hH _
    (by rw [← toWork_varsOf h H hH]; exact hrounds) j

/-! ## The whole hash -/

theorem sha256_output (junk : List UInt8) (hj : junk.length = 32) (h : Array (BitVec 32))
    (H : Fin 8 → BitVec 32) (hH : ∀ j : Fin 8, h[j.val]! = H j) :
    bytesToBitsBE ((List.range 8).foldl (fun r i => setU32Be r (4 * i) h[i]!) junk) =
      (List.finRange 8).flatMap fun j => wordToBits (H j) := by
  -- the bytes of the result
  have key : ∀ n ≤ 8, ((List.range n).foldl (fun r i => setU32Be r (4 * i) h[i]!) junk).length = 32 ∧
      ∀ k < 4 * n, ((List.range n).foldl (fun r i => setU32Be r (4 * i) h[i]!) junk)[k]! =
        byteOfInt32 ((h[k / 4]! >>> (24 - 8 * (k % 4))) &&& 0xff#32) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hj, fun k hk => absurd hk (by omega)⟩
    | succ n ih =>
      intro hn
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      obtain ⟨s1, s2, s3⟩ := setU32Be_spec _ (4 * n) h[n]! (by rw [ih1]; omega)
      refine ⟨by rw [s1, ih1], fun k hk => ?_⟩
      by_cases hk' : k < 4 * n
      · rw [s3 k (Or.inl hk'), ih2 k hk']
      · have := s2 (k - 4 * n) (by omega)
        rw [show 4 * n + (k - 4 * n) = k by omega] at this
        rw [this, show k / 4 = n by omega, show k % 4 = k - 4 * n by omega]
  obtain ⟨k1, k2⟩ := key 8 le_rfl
  apply List.ext_getElem
  · rw [bytesToBitsBE_length, k1, flatMap_wordToBits_length]
  intro b hb1 hb2
  have hb : b < 256 := by rw [bytesToBitsBE_length, k1] at hb1; omega
  rw [bytesToBitsBE_getElem, ← getElem!_pos _ _ (by rw [k1]; omega), k2 _ (by omega),
    testBit_byteOfInt32 _ _ _ (by omega), ← List.getD_eq_getElem _ false hb2,
    flatMap_wordToBits_getD (by norm_num) 8 H b (by omega), ← hH]
  have e1 : b / 8 / 4 = b / 32 := by omega
  have e2 : 24 - 8 * (b / 8 % 4) + (7 - b % 8) = 32 - 1 - b % 32 := by omega
  rw [e1, e2]

theorem sha256_blocks (M : List UInt8) :
    (List.range ((sha256Pad M).length / 64)).foldl (sha256Block (sha256Pad M))
        (sha256H0, Array.replicate 64 0) |>.1.size = 8 ∧
    ∀ j : Fin 8, ((List.range ((sha256Pad M).length / 64)).foldl (sha256Block (sha256Pad M))
        (sha256H0, Array.replicate 64 0)).1[j.val]! =
      ((List.range ((sha256Pad M).length / 64)).map (fun i => fun j : Fin 16 =>
        getU32Be (sha256Pad M) (i * 64 + 4 * j.val))).foldl (compress sha256Params) H0_256 j := by
  rw [List.foldl_map]
  have := foldl_rel (List.range ((sha256Pad M).length / 64)) (sha256Block (sha256Pad M))
    (fun H i => compress sha256Params H (fun j : Fin 16 => getU32Be (sha256Pad M) (i * 64 + 4 * j.val)))
    (fun hw => fun j : Fin 8 => hw.1[j.val]!) (fun hw => hw.1.size = 8 ∧ hw.2.size = 64)
    (fun hw i _ hinv => by
      obtain ⟨a1, a2, a3⟩ := sha256Block_spec (sha256Pad M) hw.1 hw.2 hinv.1 hinv.2 i
        (fun j => hw.1[j.val]!) (fun _ => rfl)
      exact ⟨⟨a1, a2⟩, funext a3⟩)
    (sha256H0, Array.replicate 64 0) ⟨rfl, rfl⟩
  have e : (fun j : Fin 8 => (sha256H0, (Array.replicate 64 0 : Array (BitVec 32))).1[j.val]!) =
      H0_256 := funext sha256H0_eq
  rw [e] at this
  exact ⟨this.1.1, fun j => congrFun this.2 j⟩

theorem SHA256_def (M : Bits) : SHA256 M = (List.finRange 8).flatMap fun j => wordToBits
    (((parse 32 (pad 512 64 M)).foldl (compress sha256Params) H0_256) j) := rfl

theorem sha256With_def (junk M : List UInt8) : sha256With junk M =
    (List.range 8).foldl (fun r i => setU32Be r (4 * i)
      ((List.range ((sha256Pad M).length / 64)).foldl (sha256Block (sha256Pad M))
        (sha256H0, Array.replicate 64 0)).1[i]!) junk := by
  simp only [sha256With]

/-- **SHA-256.** For every byte string `M` and every initial content of the
output buffer, the OCaml `sha256` returns FIPS 180-4 SHA-256 of `M`'s bit
string. -/
theorem sha256With_eq (junk : List UInt8) (hj : junk.length = 32) (M : List UInt8) :
    bytesToBitsBE (sha256With junk M) = SHA256 (bytesToBitsBE M) := by
  obtain ⟨hsz, hH⟩ := sha256_blocks M
  rw [SHA256_def, sha256With_def, ← sha256Pad_bits, sha256_parse]
  exact sha256_output junk hj _ _ hH

theorem sha256_eq (M : List UInt8) : bytesToBitsBE (sha256 M) = SHA256 (bytesToBitsBE M) :=
  sha256With_eq _ (List.length_replicate ..) M

theorem sha256_length (M : List UInt8) : (sha256 M).length = 32 := by
  have h := congrArg List.length (sha256_eq M)
  rw [bytesToBitsBE_length] at h
  have : (SHA256 (bytesToBitsBE M)).length = 256 := by
    rw [SHA256_def, flatMap_wordToBits_length]
  omega

end OcamlPq.Hash.Sha2
