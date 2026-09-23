import OcamlPq.Hash.Sha256

/-!
# `sha512` is FIPS 180-4 SHA-512

`sha512_eq`: for every byte string `M` with `|M| < 2^61`,
`bytesToBitsBE (sha512 M) = SHA512 (bytesToBitsBE M)`.

The OCaml code writes only the low 64 bits of FIPS 180-4's 128-bit length
field (`set_u64_be padded (padded_length - 8) bit_length`); the high 64 bits
stay zero from `Bytes.make`. That is correct exactly when `8·|M| < 2^64`,
i.e. `|M| < 2^61`, which every OCaml string satisfies
(`Sys.max_string_length = 2^57 − 9` on 64-bit platforms, less elsewhere).
-/

namespace OcamlPq.Hash.Sha2

open FIPS180 Keccak

/-! ## Big-endian 64-bit loads and stores -/

set_option maxHeartbeats 1000000 in
/-- `get_u64_be s off` is the 64-bit word whose big-endian bit string is bits
`8·off … 8·off + 63` of `s`. -/
theorem getU64Be_eq (s : List UInt8) (off : ℕ) (h : off + 8 ≤ s.length) :
    getU64Be s off = wordOfBits 64 (((bytesToBitsBE s).drop (8 * off)).take 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_wordOfBits 64 _ (by simp; omega) j hj, List.getElem_take, List.getElem_drop,
    bytesToBitsBE_getElem]
  have e1 : (8 * off + (64 - 1 - j)) / 8 = off + (63 - j) / 8 := by omega
  have e2 : (8 * off + (64 - 1 - j)) % 8 = (63 - j) % 8 := by omega
  simp only [e1, e2]
  rw [getU64Be, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    getLsbD_int64OfByte]
  rw [← getElem!_pos s _ (by omega)]
  interval_cases j <;> simp [UInt8.testBit_ge]

theorem setU64Be_length (b : List UInt8) (off : ℕ) (x : BitVec 64) :
    (setU64Be b off x).length = b.length :=
  (foldl_set_range 8 off _ b).1

theorem setU64Be_get (b : List UInt8) (off : ℕ) (x : BitVec 64) (j : ℕ) :
    (setU64Be b off x)[j]! =
      if off ≤ j ∧ j < off + 8 ∧ j < b.length then
        byteOfInt64 ((x >>> (8 * (7 - (j - off)))) &&& 0xff#64)
      else b[j]! :=
  (foldl_set_range 8 off (fun i => byteOfInt64 ((x >>> (8 * (7 - i))) &&& 0xff#64)) b).2 j

/-! ## Padding (FIPS 180-4 §5.1.2) -/

theorem sha512Pad_length (M : List UInt8) :
    (sha512Pad M).length = ((M.length + 17 + 127) / 128) * 128 := by
  simp [sha512Pad, setU64Be_length, blitString_length]

theorem sha512Pad_get (M : List UInt8) (j : ℕ) (hj : j < ((M.length + 17 + 127) / 128) * 128) :
    (sha512Pad M)[j]! =
      if j < M.length then M[j]!
      else if j = M.length then 0x80
      else if ((M.length + 17 + 127) / 128) * 128 - 8 ≤ j then
        byteOfInt64 ((BitVec.ofNat 64 (8 * M.length) >>>
          (8 * (7 - (j - (((M.length + 17 + 127) / 128) * 128 - 8))))) &&& 0xff#64)
      else 0 := by
  set PL := ((M.length + 17 + 127) / 128) * 128 with hPL
  have hPL17 : M.length + 17 ≤ PL := by omega
  simp only [sha512Pad, ← hPL, bitLength_eq]
  rw [setU64Be_get, List.length_set, blitString_length, List.length_replicate]
  by_cases hhi : PL - 8 ≤ j
  · rw [ite_eq_left ⟨hhi, by omega, hj⟩, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left hhi]
  · rw [ite_eq_right (by omega), ite_eq_right hhi, List.getElem!_set', blitString_length,
      List.length_replicate, blitString_get, List.length_replicate, List.getElem!_replicate_zero]
    by_cases h1 : j < M.length
    · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega, by omega⟩, ite_eq_left h1,
        Nat.zero_add, Nat.sub_zero]
    · rw [ite_eq_right h1]
      by_cases h2 : j = M.length
      · rw [ite_eq_left ⟨h2.symm, by omega⟩, ite_eq_left h2]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h2]

/-- `pad` with the number of zeros given explicitly. -/
theorem pad_eq (blockLen lenBits : ℕ) (M : Bits) (k : ℕ)
    (hk : ((((blockLen - lenBits : ℕ) : ℤ) - (M.length + 1)) % (blockLen : ℤ)).toNat = k) :
    pad blockLen lenBits M = M ++ [true] ++ List.replicate k false ++ natToBits lenBits M.length := by
  simp only [pad, hk]

/-- **Padding.** For `|M| < 2^61`, the OCaml padded message is FIPS 180-4
§5.1.2 padding (with the 128-bit length field) of the message's bit string. -/
theorem sha512Pad_bits (M : List UInt8) (hM : M.length < 2 ^ 61) :
    bytesToBitsBE (sha512Pad M) = pad 1024 128 (bytesToBitsBE M) := by
  set PL := ((M.length + 17 + 127) / 128) * 128 with hPL
  have hPL17 : M.length + 17 ≤ PL := by omega
  have hlenM : (bytesToBitsBE M).length = 8 * M.length := bytesToBitsBE_length M
  rw [pad_eq 1024 128 _ (8 * PL - 8 * M.length - 129) (by rw [hlenM]; omega), hlenM]
  apply List.ext_getElem
  · simp only [bytesToBitsBE_length, sha512Pad_length, List.length_append, List.length_cons,
      List.length_nil, List.length_replicate, natToBits, wordToBits_length]
    omega
  intro b h1 h2
  have hb : b < 8 * PL := by simpa [sha512Pad_length] using h1
  rw [bytesToBitsBE_getElem, ← getElem!_pos (sha512Pad M) (b / 8) (by rw [sha512Pad_length]; omega),
    sha512Pad_get M (b / 8) (by omega)]
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
  have hpre : (bytesToBitsBE M ++ [true] ++ List.replicate (8 * PL - 8 * M.length - 129) false).length =
      8 * PL - 128 := by simp; omega
  by_cases hC : b < 8 * PL - 128
  · -- zero padding
    rw [ite_eq_right (show ¬ b / 8 < M.length by omega)]
    rw [List.getElem_append_left (by rw [hpre]; omega),
      List.getElem_append_right (by len_tac), List.getElem_replicate]
    by_cases hD : b / 8 = M.length
    · rw [ite_eq_left hD, testBit_0x80 _ (by omega)]
      simp; omega
    · rw [ite_eq_right hD, ite_eq_right (by omega)]
      simp
  · -- the 128-bit length field
    rw [ite_eq_right (show ¬ b / 8 < M.length by omega), ite_eq_right (show ¬ b / 8 = M.length by omega),
      List.getElem_append_right (by rw [hpre]; omega)]
    simp only [natToBits]
    rw [wordToBits_getElem]
    simp only [hpre, BitVec.getLsbD_ofNat]
    have hidx : 128 - 1 - (b - (8 * PL - 128)) = 8 * PL - 1 - b := by omega
    rw [hidx]
    by_cases hE : b < 8 * PL - 64
    · -- the high 64 bits: zero, since `8·|M| < 2^64`
      rw [ite_eq_right (by omega),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by omega : 8 * M.length < 2 ^ 64)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp
    · -- the low 64 bits, from `set_u64_be`
      rw [ite_eq_left (by omega), testBit_byteOfInt64 _ _ _ (by omega)]
      have : 8 * (7 - (b / 8 - (PL - 8))) + (7 - b % 8) = 8 * PL - 1 - b := by omega
      rw [this, BitVec.getLsbD_ofNat]
      simp only [show 8 * PL - 1 - b < 64 by omega, show 8 * PL - 1 - b < 128 by omega,
        decide_true, Bool.true_and]

/-! ## Parsing (§5.2.2) and one block -/

theorem sha512_parse (padded : List UInt8) :
    parse 64 (bytesToBitsBE padded) =
      (List.range (padded.length / 128)).map fun i => fun j : Fin 16 =>
        getU64Be padded (i * 128 + 8 * j.val) := by
  unfold parse
  rw [bytesToBitsBE_length, show 8 * padded.length / (16 * 64) = padded.length / 128 by omega]
  apply List.map_congr_left
  intro i hi
  funext j
  have hi' := List.mem_range.mp hi
  have hmul : (i + 1) * 128 ≤ padded.length :=
    le_trans (Nat.mul_le_mul_right 128 hi') (Nat.div_mul_le_self _ 128)
  have hj := j.isLt
  rw [getU64Be_eq _ _ (by nlinarith)]
  congr 3
  ring

theorem sha512Sigma : (∀ x, (fun x => rotr64 x 1 ^^^ (rotr64 x 8 ^^^ (x >>> 7))) x = sigma0_512 x) ∧
    (∀ x, (fun y => rotr64 y 19 ^^^ (rotr64 y 61 ^^^ (y >>> 6))) x = sigma1_512 x) ∧
    (∀ x, (fun a => rotr64 a 28 ^^^ (rotr64 a 34 ^^^ rotr64 a 39)) x = Sigma0_512 x) ∧
    (∀ x, (fun e => rotr64 e 14 ^^^ (rotr64 e 18 ^^^ rotr64 e 41)) x = Sigma1_512 x) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩ <;>
    simp [sigma0_512, sigma1_512, Sigma0_512, Sigma1_512, rotr64, ROTR, SHR, BitVec.xor_assoc]

theorem sha512Block_fst (padded : List UInt8) (h w : Array (BitVec 64)) (i : ℕ) :
    (sha512Block padded (h, w) i).1 =
      addVars h ((List.range 80).foldl (sha512Round (sha512Schedule padded (i * 128) w)) (varsOf h)) := by
  simp only [sha512Block]

theorem sha512Block_snd (padded : List UInt8) (h w : Array (BitVec 64)) (i : ℕ) :
    (sha512Block padded (h, w) i).2 = sha512Schedule padded (i * 128) w := by
  simp only [sha512Block]

theorem sha512Schedule_eq (padded : List UInt8) (base : ℕ) (w : Array (BitVec 64)) :
    sha512Schedule padded base w = (List.range' 16 64).foldl
      (schedStep (fun x => rotr64 x 1 ^^^ (rotr64 x 8 ^^^ (x >>> 7)))
        (fun y => rotr64 y 19 ^^^ (rotr64 y 61 ^^^ (y >>> 6))))
      ((List.range 16).foldl (fun w t => w.set! t (getU64Be padded (base + 8 * t))) w) := by
  unfold sha512Schedule schedStep
  rfl

theorem sha512Round_eq (w : Array (BitVec 64)) :
    sha512Round w = roundStep (fun i => sha512Constants[i]!)
      (fun a => rotr64 a 28 ^^^ (rotr64 a 34 ^^^ rotr64 a 39))
      (fun e => rotr64 e 14 ^^^ (rotr64 e 18 ^^^ rotr64 e 41)) w := by
  funext v i
  unfold sha512Round roundStep
  rfl

/-- **One block.** An iteration of the OCaml block loop is FIPS 180-4
§6.4.2 steps 1–4. -/
theorem sha512Block_spec (padded : List UInt8) (h w : Array (BitVec 64)) (hh : h.size = 8)
    (hw : w.size = 80) (i : ℕ) (H : Fin 8 → BitVec 64) (hH : ∀ j : Fin 8, h[j.val]! = H j) :
    (sha512Block padded (h, w) i).1.size = 8 ∧ (sha512Block padded (h, w) i).2.size = 80 ∧
    ∀ j : Fin 8, (sha512Block padded (h, w) i).1[j.val]! =
      compress sha512Params H (fun j : Fin 16 => getU64Be padded (i * 128 + 8 * j.val)) j := by
  obtain ⟨hs1, hg1⟩ := foldl_set!_const 16 (fun t => getU64Be padded (i * 128 + 8 * t)) w
  have h16 : ∀ t (ht : t < 16),
      ((List.range 16).foldl (fun w t => w.set! t (getU64Be padded (i * 128 + 8 * t))) w)[t]! =
        (fun j : Fin 16 => getU64Be padded (i * 128 + 8 * j.val)) ⟨t, ht⟩ := by
    intro t ht; rw [hg1, ite_eq_left ⟨ht, by omega⟩]
  obtain ⟨hs2, hg2⟩ := sched_spec sha512Params (fun j : Fin 16 => getU64Be padded (i * 128 + 8 * j.val))
    _ _ sha512Sigma.1 sha512Sigma.2.1 80 _ (by rw [hs1, hw]) h16 64 (by norm_num)
  rw [← sha512Schedule_eq] at hs2 hg2
  have hrounds := rounds_spec sha512Params
    (schedule sha512Params (fun j : Fin 16 => getU64Be padded (i * 128 + 8 * j.val)))
    (fun t => sha512Constants[t]!) _ _ (sha512Schedule padded (i * 128) w) 80
    (fun t ht => sha512Constants_eq t ht) (fun t ht => hg2 t ht)
    sha512Sigma.2.2.1 sha512Sigma.2.2.2 (varsOf h)
  rw [← sha512Round_eq] at hrounds
  rw [sha512Block_fst, sha512Block_snd, addVars_size, hh, hs2]
  refine ⟨rfl, rfl, fun j => ?_⟩
  exact compress_eq sha512Params H _ h hh hH _
    (by rw [← toWork_varsOf h H hH]; exact hrounds) j

/-! ## The whole hash -/

theorem testBit_byteOfInt64' (x : BitVec 64) (s t : ℕ) (ht : t < 8) :
    (byteOfInt64 ((x >>> s) &&& 0xff#64)).toNat.testBit t = x.getLsbD (s + t) := by
  have hlt : ((x >>> s) &&& 0xff#64).toNat < 256 := by
    rw [BitVec.toNat_and]
    exact lt_of_le_of_lt Nat.and_le_right (by decide)
  rw [byteOfInt64, UInt8.toNat_ofNat', show 2 ^ 8 = 256 from rfl, Nat.mod_eq_of_lt hlt,
    BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  have : (0xff#64).getLsbD t = true := by interval_cases t <;> decide
  rw [this, Bool.and_true]

theorem sha512_output (junk : List UInt8) (hj : junk.length = 64) (h : Array (BitVec 64))
    (H : Fin 8 → BitVec 64) (hH : ∀ j : Fin 8, h[j.val]! = H j) :
    bytesToBitsBE ((List.range 8).foldl (fun r i => setU64Be r (8 * i) h[i]!) junk) =
      (List.finRange 8).flatMap fun j => wordToBits (H j) := by
  have key : ∀ n ≤ 8, ((List.range n).foldl (fun r i => setU64Be r (8 * i) h[i]!) junk).length = 64 ∧
      ∀ k < 8 * n, ((List.range n).foldl (fun r i => setU64Be r (8 * i) h[i]!) junk)[k]! =
        byteOfInt64 ((h[k / 8]! >>> (8 * (7 - k % 8))) &&& 0xff#64) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hj, fun k hk => absurd hk (by omega)⟩
    | succ n ih =>
      intro hn
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      refine ⟨by rw [setU64Be_length, ih1], fun k hk => ?_⟩
      rw [setU64Be_get, ih1]
      by_cases hk' : k < 8 * n
      · rw [ite_eq_right (by omega), ih2 k hk']
      · rw [ite_eq_left ⟨by omega, by omega, by omega⟩, show k / 8 = n by omega,
          show k % 8 = k - 8 * n by omega]
  obtain ⟨k1, k2⟩ := key 8 le_rfl
  apply List.ext_getElem
  · rw [bytesToBitsBE_length, k1, flatMap_wordToBits_length]
  intro b hb1 hb2
  have hb : b < 512 := by rw [bytesToBitsBE_length, k1] at hb1; omega
  rw [bytesToBitsBE_getElem, ← getElem!_pos _ _ (by rw [k1]; omega), k2 _ (by omega),
    testBit_byteOfInt64' _ _ _ (by omega), ← List.getD_eq_getElem _ false hb2,
    flatMap_wordToBits_getD (by norm_num) 8 H b (by omega), ← hH]
  have e1 : b / 8 / 8 = b / 64 := by omega
  have e2 : 8 * (7 - b / 8 % 8) + (7 - b % 8) = 64 - 1 - b % 64 := by omega
  rw [e1, e2]

theorem sha512_blocks (M : List UInt8) :
    (List.range ((sha512Pad M).length / 128)).foldl (sha512Block (sha512Pad M))
        (sha512H0, Array.replicate 80 0) |>.1.size = 8 ∧
    ∀ j : Fin 8, ((List.range ((sha512Pad M).length / 128)).foldl (sha512Block (sha512Pad M))
        (sha512H0, Array.replicate 80 0)).1[j.val]! =
      ((List.range ((sha512Pad M).length / 128)).map (fun i => fun j : Fin 16 =>
        getU64Be (sha512Pad M) (i * 128 + 8 * j.val))).foldl (compress sha512Params) H0_512 j := by
  rw [List.foldl_map]
  have := foldl_rel (List.range ((sha512Pad M).length / 128)) (sha512Block (sha512Pad M))
    (fun H i => compress sha512Params H (fun j : Fin 16 => getU64Be (sha512Pad M) (i * 128 + 8 * j.val)))
    (fun hw => fun j : Fin 8 => hw.1[j.val]!) (fun hw => hw.1.size = 8 ∧ hw.2.size = 80)
    (fun hw i _ hinv => by
      obtain ⟨a1, a2, a3⟩ := sha512Block_spec (sha512Pad M) hw.1 hw.2 hinv.1 hinv.2 i
        (fun j => hw.1[j.val]!) (fun _ => rfl)
      exact ⟨⟨a1, a2⟩, funext a3⟩)
    (sha512H0, Array.replicate 80 0) ⟨rfl, rfl⟩
  have e : (fun j : Fin 8 => (sha512H0, (Array.replicate 80 0 : Array (BitVec 64))).1[j.val]!) =
      H0_512 := funext sha512H0_eq
  rw [e] at this
  exact ⟨this.1.1, fun j => congrFun this.2 j⟩

theorem SHA512_def (M : Bits) : SHA512 M = (List.finRange 8).flatMap fun j => wordToBits
    (((parse 64 (pad 1024 128 M)).foldl (compress sha512Params) H0_512) j) := rfl

theorem sha512With_def (junk M : List UInt8) : sha512With junk M =
    (List.range 8).foldl (fun r i => setU64Be r (8 * i)
      ((List.range ((sha512Pad M).length / 128)).foldl (sha512Block (sha512Pad M))
        (sha512H0, Array.replicate 80 0)).1[i]!) junk := by
  simp only [sha512With]

/-- **SHA-512.** For every byte string `M` with `|M| < 2^61` (every OCaml
string) and every initial content of the output buffer, the OCaml `sha512`
returns FIPS 180-4 SHA-512 of `M`'s bit string. -/
theorem sha512With_eq (junk : List UInt8) (hj : junk.length = 64) (M : List UInt8)
    (hM : M.length < 2 ^ 61) :
    bytesToBitsBE (sha512With junk M) = SHA512 (bytesToBitsBE M) := by
  obtain ⟨hsz, hH⟩ := sha512_blocks M
  rw [SHA512_def, sha512With_def, ← sha512Pad_bits M hM, sha512_parse]
  exact sha512_output junk hj _ _ hH

theorem sha512_eq (M : List UInt8) (hM : M.length < 2 ^ 61) :
    bytesToBitsBE (sha512 M) = SHA512 (bytesToBitsBE M) :=
  sha512With_eq _ (List.length_replicate ..) M hM

theorem sha512_length (M : List UInt8) : (sha512 M).length = 64 := by
  have k := (sha512_blocks M).1
  simp only [sha512, sha512With_def]
  -- every `set_u64_be` preserves the length of the 64-byte buffer
  have : ∀ n (r : List UInt8), r.length = 64 →
      ((List.range n).foldl (fun r i => setU64Be r (8 * i)
        ((List.range ((sha512Pad M).length / 128)).foldl (sha512Block (sha512Pad M))
          (sha512H0, Array.replicate 80 0)).1[i]!) r).length = 64 := by
    intro n
    induction n with
    | zero => intro r hr; exact hr
    | succ n ih =>
      intro r hr
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [setU64Be_length, ih r hr]
  exact this 8 _ (List.length_replicate ..)

end OcamlPq.Hash.Sha2
