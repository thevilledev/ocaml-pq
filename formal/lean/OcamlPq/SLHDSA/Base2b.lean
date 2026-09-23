import OcamlPq.SLHDSA.Params

/-!
# SLH-DSA: `base_2b`, FORS indices and WOTS+ digits

* `message_to_fors_indices` (slhdsa_engine.ml 394–408) is proved equal to
  FIPS 205 Algorithm 4 `base_2b(md, a, k)`. The code's accumulator `total`
  is an OCaml `int` that is shifted left by 8 for every input byte and never
  masked, so for `k·a > w` it wraps around. The model therefore runs the
  code on `w`-bit two's-complement integers (`BitVec w`, where OCaml's
  `lsl`, `+`, `lsr`, `land` are `<<<`, `+`, `>>>`, `&&&`), and the theorem
  holds for every width `w ≥ a + 7` — in particular for the 63-, 32- and
  31-bit `int`s of all OCaml platforms, where `a ≤ 14`.
* `base_w_nibbles` / `chain_lengths` (282–299) are proved equal to the
  message-plus-checksum digits of FIPS 205 Algorithm 7 (lines 1–7; the same
  lines open Algorithm 8).

Byte strings are `List ℕ` (the `Char.code` of each character).
-/

namespace OcamlPq.SLHDSA.Base2b

/-! ## FIPS 205 Algorithms 3 and 4 -/

/-- The `while bits < b` loop of FIPS 205 Algorithm 4 (lines 5–9):
    `total ← (total ≪ 8) + X[in]; in ← in + 1; bits ← bits + 8`. -/
def fipsFill (X : List ℕ) (b : ℕ) (inp bits total : ℕ) : ℕ × ℕ × ℕ :=
  if bits < b then fipsFill X b (inp + 1) (bits + 8) ((total <<< 8) + X.getD inp 0)
  else (inp, bits, total)
termination_by b - bits

theorem fipsFill_of_lt {X : List ℕ} {b inp bits total : ℕ} (h : bits < b) :
    fipsFill X b inp bits total = fipsFill X b (inp + 1) (bits + 8) ((total <<< 8) + X.getD inp 0) := by
  rw [fipsFill]; simp [h]

theorem fipsFill_of_ge {X : List ℕ} {b inp bits total : ℕ} (h : b ≤ bits) :
    fipsFill X b inp bits total = (inp, bits, total) := by
  rw [fipsFill]; simp [Nat.not_lt.mpr h]

/-- FIPS 205 Algorithm 4 `base_2b(X, b, out_len)`: the `for out` loop with
    state `(in, bits, total)`, emitting `(total ≫ bits) mod 2^b` after
    `bits ← bits − b`. -/
def fipsBase2b (X : List ℕ) (b outLen : ℕ) : List ℕ := go 0 0 0 outLen
where
  /-- The remaining `count` iterations of the `for out` loop. -/
  go (inp bits total : ℕ) : ℕ → List ℕ
  | 0 => []
  | count + 1 =>
    let r := fipsFill X b inp bits total
    let bits' := r.2.1 - b
    ((r.2.2 >>> bits') % 2 ^ b) :: go r.1 bits' r.2.2 count

/-- FIPS 205 Algorithm 3 `toByte(x, n)`, collected in the order it writes:
    `S[n−1−i] ← total mod 256; total ← total ≫ 8`. -/
def toByteRev (x : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => (x % 256) :: toByteRev (x >>> 8) n

/-- FIPS 205 Algorithm 3 `toByte(x, n)` (big-endian). -/
def fipsToByte (x n : ℕ) : List ℕ := (toByteRev x n).reverse

/-! ## Code model: `message_to_fors_indices` on `w`-bit integers -/

/-- The `while !bits < P.a` loop of `message_to_fors_indices`
    (lines 400–406) with `total` an OCaml `int` of width `w`. Reading past
    the end of the string (`String.unsafe_get`) would be undefined
    behaviour; the model returns `none` there. -/
def codeFill (w a : ℕ) (X : List ℕ) (inp bits : ℕ) (total : BitVec w) :
    Option (ℕ × ℕ × BitVec w) :=
  if bits < a then
    match X[inp]? with
    | none => none
    | some byte => codeFill w a X (inp + 1) (bits + 8) ((total <<< 8) + BitVec.ofNat w byte)
  else some (inp, bits, total)
termination_by a - bits

/-- `message_to_fors_indices message` (lines 394–408) with OCaml `int`s of
    width `w`: `Array.init P.k` evaluates its closure for indices
    `0, …, k−1` in order, each call running the fill loop and then
    `bits := !bits - P.a; (!total lsr !bits) land mask` with
    `mask = (1 lsl P.a) - 1`. The result is the signed value of the `int`. -/
def messageToForsIndices (w a k : ℕ) (X : List ℕ) : Option (List ℤ) := go 0 0 0 k
where
  /-- The remaining `count` calls of the `Array.init` closure. -/
  go (inp bits : ℕ) (total : BitVec w) : ℕ → Option (List ℤ)
  | 0 => some []
  | count + 1 =>
    match codeFill w a X inp bits total with
    | none => none
    | some (inp', bits', total') =>
      let bits'' := bits' - a
      let v := ((total' >>> bits'') &&& BitVec.ofNat w (2 ^ a - 1)).toInt
      (go inp' bits'' total' count).map (v :: ·)

/-! ## Correctness under wrap-around -/

theorem fipsFill_props (X : List ℕ) (b : ℕ) :
    ∀ inp bits total, let r := fipsFill X b inp bits total;
      b ≤ r.2.1 ∧ (bits < b + 8 → r.2.1 < b + 8) ∧ 8 * r.1 + bits = 8 * inp + r.2.1 := by
  intro inp bits total
  induction h : b - bits using Nat.strong_induction_on generalizing inp bits total with
  | _ m ih =>
    rw [fipsFill]
    split_ifs with hb
    · have := ih (b - (bits + 8)) (by omega) (inp + 1) (bits + 8)
        ((total <<< 8) + X.getD inp 0) rfl
      simp only at this ⊢
      omega
    · dsimp only; omega

theorem ofNat_shift_add (w t y : ℕ) :
    (BitVec.ofNat w t <<< 8) + BitVec.ofNat w y = BitVec.ofNat w ((t <<< 8) + y) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.add_mod, Nat.mul_mod]

/-- The code's fill loop is the specification's fill loop, reduced modulo
    `2^w`, and never reads out of bounds while the bits it still needs are
    available (`8·in + a ≤ 8·|X| + bits`). -/
theorem codeFill_eq (w a : ℕ) (X : List ℕ) :
    ∀ inp bits total, 8 * inp + a ≤ 8 * X.length + bits →
      codeFill w a X inp bits (BitVec.ofNat w total) =
        some ((fipsFill X a inp bits total).1, (fipsFill X a inp bits total).2.1,
          BitVec.ofNat w (fipsFill X a inp bits total).2.2) := by
  intro inp bits total
  induction h : a - bits using Nat.strong_induction_on generalizing inp bits total with
  | _ m ih =>
    intro hlen
    rw [codeFill, fipsFill]
    split_ifs with hb
    · have hin : inp < X.length := by omega
      rw [List.getElem?_eq_getElem hin]
      simp only
      rw [ofNat_shift_add, List.getD_eq_getElem _ _ hin]
      exact ih (a - (bits + 8)) (by omega) (inp + 1) (bits + 8) _ rfl (by omega)
    · rfl

/-- Extracting `a` bits at offset `s` from the `w`-bit residue of `T` gives
    the same bits as from `T` itself whenever `s + a ≤ w`. -/
theorem extract_eq (w a s T : ℕ) (hw : s + a ≤ w) :
    ((BitVec.ofNat w T >>> s) &&& BitVec.ofNat w (2 ^ a - 1)).toNat = (T >>> s) % 2 ^ a := by
  have ha : 2 ^ a - 1 < 2 ^ w := by
    have : 2 ^ a ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 0 < 2 ^ a := by positivity
    omega
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow]
  have hsplit : 2 ^ w = 2 ^ s * 2 ^ (w - s) := by rw [← pow_add]; congr 1; omega
  rw [hsplit, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : a ≤ w - s))]

theorem extract_toInt (w a s T : ℕ) (hw : s + a ≤ w) (ha : a + 1 ≤ w) :
    ((BitVec.ofNat w T >>> s) &&& BitVec.ofNat w (2 ^ a - 1)).toInt =
      (((T >>> s) % 2 ^ a : ℕ) : ℤ) := by
  rw [BitVec.toInt_eq_toNat_of_lt, extract_eq w a s T hw]
  rw [extract_eq w a s T hw]
  have h1 : (T >>> s) % 2 ^ a < 2 ^ a := Nat.mod_lt _ (by positivity)
  have h2 : 2 * 2 ^ a ≤ 2 ^ w := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) ha
  omega

theorem go_eq (w a : ℕ) (X : List ℕ) (hw : a + 7 ≤ w) :
    ∀ count inp bits total, bits < 8 → bits ≤ 8 * inp →
      8 * inp + count * a ≤ 8 * X.length + bits →
      messageToForsIndices.go w a X inp bits (BitVec.ofNat w total) count =
        some ((fipsBase2b.go X a inp bits total count).map (fun d : ℕ => (d : ℤ))) := by
  intro count
  induction count with
  | zero => intro _ _ _ _ _ _; rfl
  | succ count ih =>
    intro inp bits total hb8 hbi hlen
    have hprops := fipsFill_props X a inp bits total
    simp only at hprops
    obtain ⟨hge, hlt, hinv⟩ := hprops
    have hlt' := hlt (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hlen
    have hca : count * a ≥ 0 := Nat.zero_le _
    rw [messageToForsIndices.go, codeFill_eq w a X inp bits total (by omega)]
    simp only [fipsBase2b.go]
    rw [ih _ _ _ (by omega) (by omega) (by omega), Option.map_some, List.map_cons,
      extract_toInt w a _ _ (by omega) (by omega)]

/-- **`message_to_fors_indices` = `base_2b(md, a, k)` under wrap-around.**
    For every accumulator width `w ≥ a + 7` and every input with at least
    `k·a` bits, the code (with `total` wrapping at `w` bits) returns exactly
    the digits of FIPS 205 Algorithm 4, and never reads past the input. -/
theorem messageToForsIndices_eq (w a k : ℕ) (X : List ℕ) (hw : a + 7 ≤ w)
    (hlen : k * a ≤ 8 * X.length) :
    messageToForsIndices w a k X = some ((fipsBase2b X a k).map (fun d : ℕ => (d : ℤ))) := by
  have := go_eq w a X hw k 0 0 0 (by omega) (by omega) (by omega)
  simpa [messageToForsIndices, fipsBase2b] using this

/-- The FORS indices are correct on every OCaml platform (63-bit native,
    32-bit `js_of_ocaml`, 31-bit native/wasm `int`) for every parameter set
    (`a ≤ 14`), given the `⌈k·a/8⌉`-byte FORS digest. -/
theorem messageToForsIndices_platform (p : Platform) (P : Params) (hP : P ∈ allParams)
    (X : List ℕ) (hX : X.length = P.forsMessageBytes) :
    messageToForsIndices p.intBits P.a P.k X =
      some ((fipsBase2b X P.a P.k).map (fun d : ℕ => (d : ℤ))) := by
  have ha : P.a ≤ 14 := (sizes_portable P hP).2.2.2.1
  have hp := p.intBits_ge
  apply messageToForsIndices_eq _ _ _ _ (by omega)
  rw [hX]; exact (forsMessageBytes_spec P).1

/-- Every digit of `base_2b(X, b, ·)` is below `2^b`. -/
theorem fipsBase2b_lt (X : List ℕ) (b : ℕ) :
    ∀ count inp bits total, ∀ d ∈ fipsBase2b.go X b inp bits total count, d < 2 ^ b := by
  intro count
  induction count with
  | zero => intro _ _ _ d hd; simp [fipsBase2b.go] at hd
  | succ count ih =>
    intro inp bits total d hd
    simp only [fipsBase2b.go, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ (by positivity)
    · exact ih _ _ _ d hd

theorem fipsBase2b_go_length (X : List ℕ) (b : ℕ) :
    ∀ count inp bits total, (fipsBase2b.go X b inp bits total count).length = count := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ count ih => intros; simp [fipsBase2b.go, ih]

theorem fipsBase2b_length (X : List ℕ) (b outLen : ℕ) : (fipsBase2b X b outLen).length = outLen :=
  fipsBase2b_go_length X b outLen 0 0 0

/-! ## Bridge to `Common.Int.wrap` -/

/-- `BitVec w` arithmetic is the `wrap` semantics of `Common/Int.lean`: the
    signed value of the `w`-bit pattern of `x` is `wrap w x`. -/
theorem toInt_ofInt_eq_wrap (w : ℕ) (hw : 1 ≤ w) (x : ℤ) :
    (BitVec.ofInt w x).toInt = wrap w x := by
  rw [BitVec.toInt_ofInt]
  unfold wrap Int.bmod
  have hM : (2 : ℤ) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : (0 : ℤ) < 2 ^ (w - 1) := by positivity
  have hcast : ((2 ^ w : ℕ) : ℤ) = (2 : ℤ) ^ w := by push_cast; ring
  simp only [hcast]
  have hhalf : ((2 : ℤ) ^ w + 1) / 2 = 2 ^ (w - 1) := by
    rw [hM]; omega
  rw [hhalf]
  set M : ℤ := 2 ^ (w - 1)
  set m : ℤ := 2 ^ w
  have hmpos : 0 < m := by rw [hM]; omega
  have hx : x = x % m + m * (x / m) := (Int.emod_add_mul_ediv x m).symm
  have hr0 : 0 ≤ x % m := Int.emod_nonneg _ (by omega)
  have hr1 : x % m < m := Int.emod_lt_of_pos _ hmpos
  set r := x % m
  set q := x / m
  have hshift : (x + M) % m = (r + M) % m := by
    rw [hx, show r + m * q + M = (r + M) + m * q by ring, Int.add_mul_emod_self_left]
  rw [hshift]
  split_ifs with h
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]; ring
  · rw [show r + M = (r + M - m) + m * 1 by ring, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (by omega) (by omega)]
    ring

/-! ## WOTS+ message and checksum digits -/

/-- `base_w_nibbles message` (lines 282–285), with `wots_len1` as `len1`. -/
def baseWNibbles (len1 : ℕ) (msg : List ℕ) : List ℕ :=
  (List.range len1).map fun index =>
    let byte := msg.getD (index / 2) 0
    if index &&& 1 = 0 then byte >>> 4 else byte &&& 0x0f

/-- `chain_lengths message` (lines 287–299): the `len1` nibbles, then the
    checksum `Σ (wots_w − 1 − digit)` shifted left by 4 and split into three
    nibbles. -/
def chainLengths (len1 : ℕ) (msg : List ℕ) : List ℕ :=
  let digits := baseWNibbles len1 msg
  let checksum := digits.foldl (fun c d => c + (16 - 1 - d)) 0
  let checksum := checksum <<< 4
  digits ++ [(checksum >>> 12) &&& 0x0f, (checksum >>> 8) &&& 0x0f, (checksum >>> 4) &&& 0x0f]

/-- FIPS 205 Algorithm 7 lines 1–7 (identical to Algorithm 8 lines 1–7)
    with `lg_w = 4`, `w = 16`, `len1 = 2n`, `len2 = 3`: the base-`w` message
    digits followed by the base-`w` checksum digits. -/
def fipsWotsDigits (n : ℕ) (M : List ℕ) : List ℕ :=
  let lgw := 4
  let w := 16
  let len1 := 2 * n
  let len2 := 3
  let msg := fipsBase2b M lgw len1
  let csum := msg.foldl (fun c d => c + (w - 1 - d)) 0
  let csum := csum <<< ((8 - ((len2 * lgw) % 8)) % 8)
  msg ++ fipsBase2b (fipsToByte csum ((len2 * lgw + 7) / 8)) lgw len2

/-- Every WOTS+ digit is below `w = 16`. -/
theorem fipsWotsDigits_lt (n : ℕ) (M : List ℕ) : ∀ d ∈ fipsWotsDigits n M, d < 16 := by
  intro d hd
  simp only [fipsWotsDigits, List.mem_append] at hd
  rcases hd with hd | hd
  · exact fipsBase2b_lt M 4 _ 0 0 0 d hd
  · exact fipsBase2b_lt _ 4 _ 0 0 0 d hd

theorem fipsWotsDigits_getD_lt (n : ℕ) (M : List ℕ) (i : ℕ) : (fipsWotsDigits n M).getD i 0 < 16 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (fipsWotsDigits n M)[i]? with
  | none => simp
  | some d => exact fipsWotsDigits_lt n M d (List.mem_of_getElem? h)

/-- There are `len = 2n + 3` WOTS+ digits. -/
theorem fipsWotsDigits_length (n : ℕ) (M : List ℕ) : (fipsWotsDigits n M).length = 2 * n + 3 := by
  simp [fipsWotsDigits, fipsBase2b_length]

/-- The two nibbles of a byte, high first. -/
def nibbles : List ℕ → List ℕ
  | [] => []
  | x :: xs => (x / 16) :: (x % 16) :: nibbles xs

theorem fipsBase2b_go_four (X : List ℕ) (hX : ∀ x ∈ X, x < 256) :
    ∀ r j total, j + r ≤ X.length →
      fipsBase2b.go X 4 j 0 total (2 * r) = nibbles ((X.drop j).take r) := by
  intro r
  induction r with
  | zero => intro j total _; simp [fipsBase2b.go, nibbles]
  | succ r ih =>
    intro j total hj
    have hjl : j < X.length := by omega
    have hx := hX _ (List.getElem_mem hjl)
    rw [show 2 * (r + 1) = (2 * r + 1) + 1 by ring]
    simp only [fipsBase2b.go]
    rw [fipsFill_of_lt (by norm_num), fipsFill_of_ge (by norm_num)]
    simp only
    rw [fipsFill_of_ge (by norm_num)]
    simp only [Nat.sub_self]
    rw [ih (j + 1) _ (by omega), List.drop_eq_getElem_cons hjl, List.take_succ_cons, nibbles,
      List.getD_eq_getElem _ _ hjl]
    congr 1
    · simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
      omega
    · congr 1
      simp only [Nat.shiftLeft_eq, Nat.shiftRight_zero]
      omega

theorem nibbles_length (X : List ℕ) : (nibbles X).length = 2 * X.length := by
  induction X with
  | nil => rfl
  | cons x xs ih => simp [nibbles, ih]; ring

theorem nibbles_getElem (X : List ℕ) (i : ℕ) (hi : i < (nibbles X).length) :
    (nibbles X)[i] =
      if i % 2 = 0 then X[i / 2]'(by rw [nibbles_length] at hi; omega) / 16
      else X[i / 2]'(by rw [nibbles_length] at hi; omega) % 16 := by
  induction X generalizing i with
  | nil => simp [nibbles] at hi
  | cons x xs ih =>
    match i with
    | 0 => simp [nibbles]
    | 1 => simp [nibbles]
    | i + 2 =>
      simp only [nibbles, List.getElem_cons_succ]
      rw [ih i (by simp [nibbles] at hi; omega)]
      have h1 : (i + 2) % 2 = i % 2 := by omega
      have h2 : (i + 2) / 2 = i / 2 + 1 := by omega
      simp only [h1, h2, List.getElem_cons_succ]

/-- `base_w_nibbles` splits each byte into its high and low nibble. -/
theorem baseWNibbles_eq (X : List ℕ) : baseWNibbles (2 * X.length) X = nibbles X := by
  apply List.ext_getElem
  · simp [baseWNibbles, nibbles_length]
  · intro i h1 h2
    rw [nibbles_getElem]
    simp only [baseWNibbles, List.getElem_map, List.getElem_range, Nat.and_one_is_mod]
    have hi : i / 2 < X.length := by simp [baseWNibbles] at h1; omega
    rw [List.getD_eq_getElem _ _ hi]
    have h15 : (0x0f : ℕ) = 2 ^ 4 - 1 := rfl
    split_ifs
    · rw [Nat.shiftRight_eq_div_pow]
    · rw [h15, Nat.and_two_pow_sub_one_eq_mod]

theorem fipsBase2b_four (X : List ℕ) (hX : ∀ x ∈ X, x < 256) :
    fipsBase2b X 4 (2 * X.length) = nibbles X := by
  have := fipsBase2b_go_four X hX X.length 0 0 (by omega)
  simpa [fipsBase2b] using this

/-- `base_2b` of a two-byte string with `b = 4`, three digits. -/
theorem fipsBase2b_two_bytes (x0 x1 : ℕ) (hx0 : x0 < 256) (hx1 : x1 < 256) :
    fipsBase2b [x0, x1] 4 3 = [x0 / 16, x0 % 16, x1 / 16] := by
  simp only [fipsBase2b, fipsBase2b.go]
  rw [fipsFill_of_lt (by norm_num), fipsFill_of_ge (by norm_num)]
  simp only
  rw [fipsFill_of_ge (by norm_num)]
  simp only
  rw [fipsFill_of_lt (by norm_num), fipsFill_of_ge (by norm_num)]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.sub_self, pow_zero, Nat.div_one]
  refine List.cons_eq_cons.mpr ⟨by omega, List.cons_eq_cons.mpr ⟨by omega,
    List.cons_eq_cons.mpr ⟨by omega, rfl⟩⟩⟩

/-- Every `base_w_nibbles` digit is at most `w − 1 = 15`. -/
theorem nibbles_le (X : List ℕ) (hX : ∀ x ∈ X, x < 256) : ∀ d ∈ nibbles X, d ≤ 15 := by
  induction X with
  | nil => simp [nibbles]
  | cons x xs ih =>
    intro d hd
    have hx := hX x (by simp)
    simp only [nibbles, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · omega
    · omega
    · exact ih (fun y hy => hX y (by simp [hy])) d hd

theorem foldl_checksum_le (D : List ℕ) (c : ℕ) :
    D.foldl (fun c d => c + (16 - 1 - d)) c ≤ c + 15 * D.length := by
  induction D generalizing c with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (c + (16 - 1 - d)); omega

/-- The checksum bound: `csum ≤ 15·len1`, so `csum ≪ 4 < 2^16` whenever
    `len1 ≤ 273`; for `n ≤ 32` it is at most `15·64 = 960`. -/
theorem checksum_le (X : List ℕ) :
    (nibbles X).foldl (fun c d => c + (16 - 1 - d)) 0 ≤ 15 * (2 * X.length) := by
  have := foldl_checksum_le (nibbles X) 0
  rw [nibbles_length] at this; omega

/-- **`chain_lengths` = the WOTS+ digits of FIPS 205 Algorithm 7/8.** For
    every `n`-byte message with `n ≤ 136` (so that `csum ≪ 4` fits the
    two-byte `toByte(csum, 2)`; the code uses `n ≤ 32`), the code's
    `len = 2n + 3` chain lengths are the base-16 message digits followed by
    the three base-16 checksum digits. -/
theorem chainLengths_eq (X : List ℕ) (hX : ∀ x ∈ X, x < 256) (hn : X.length ≤ 136) :
    chainLengths (2 * X.length) X = fipsWotsDigits X.length X := by
  simp only [chainLengths, fipsWotsDigits, baseWNibbles_eq, fipsBase2b_four X hX]
  congr 1
  set c := (nibbles X).foldl (fun c d => c + (16 - 1 - d)) 0 with hc
  have hcle := checksum_le X
  rw [← hc] at hcle
  have hshift : (8 - 3 * 4 % 8) % 8 = 4 := by norm_num
  have hbytes : (3 * 4 + 7) / 8 = 2 := by norm_num
  rw [hshift, hbytes]
  have hC : c <<< 4 < 65536 := by rw [Nat.shiftLeft_eq]; omega
  have htb : fipsToByte (c <<< 4) 2 = [(c <<< 4) / 256 % 256, (c <<< 4) % 256] := by
    simp [fipsToByte, toByteRev, Nat.shiftRight_eq_div_pow]
  rw [htb, fipsBase2b_two_bytes _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))]
  have h15 : (0x0f : ℕ) = 2 ^ 4 - 1 := rfl
  simp only [h15, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  generalize c <<< 4 = C at hC
  refine List.cons_eq_cons.mpr ⟨by omega, List.cons_eq_cons.mpr ⟨by omega,
    List.cons_eq_cons.mpr ⟨by omega, rfl⟩⟩⟩

end OcamlPq.SLHDSA.Base2b
