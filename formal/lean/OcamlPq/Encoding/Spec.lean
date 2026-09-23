import OcamlPq.Encoding.Digits

/-!
# FIPS 203 and FIPS 204 bit and byte encodings

Transcriptions of

* FIPS 203 Algorithms 3–6 (`BitsToBytes`, `BytesToBits`, `ByteEncode_d`,
  `ByteDecode_d`), and
* FIPS 204 Algorithms 9–13 and 16–19 (`IntegerToBits`, `BitsToInteger`,
  `IntegerToBytes`, `BitsToBytes`, `BytesToBits`, `SimpleBitPack`, `BitPack`,
  `SimpleBitUnpack`, `BitUnpack`).

The definitions follow the pseudocode loop by loop and are written without
reference to the OCaml code. Arrays are `List ℕ` read with `getD _ 0`; bits are
the naturals `0` and `1`. Where the pseudocode writes array entries in index
order (`b[i·d + j]`, `y[8i + j]`), the transcription appends, which is the same
array. `BitsToBytes` accumulates into earlier entries and is transcribed with
`List.modify`.

FIPS 203 Algorithms 3 and 4 and FIPS 204 Algorithms 12 and 13 are the same
algorithms (FIPS 204 allows bit strings whose length is not a multiple of 8),
so each pair has one definition here.

The second half of the file characterises each algorithm as a `Regroup`, which
is what the refinement proofs use.
-/

namespace OcamlPq.Encoding.Spec

open Nat (ofDigits)
open OcamlPq.Encoding

/-- The ML-KEM modulus `q`. -/
def q : ℕ := 3329

/-! ## Transcriptions -/

/-- The loop `for i from 0 to α − 1: y[i] ← x mod B; x ← ⌊x/B⌋`, appending to
`pre`. -/
def digitLoop (B : ℕ) (x α : ℕ) (pre : List ℕ) : ℕ × List ℕ :=
  (List.range α).foldl (fun (s : ℕ × List ℕ) _ => (s.1 / B, s.2 ++ [s.1 % B])) (x, pre)

/-- FIPS 204 Algorithm 9, `IntegerToBits(x, α)`. -/
def integerToBits (x α : ℕ) : List ℕ := (digitLoop 2 x α []).2

/-- FIPS 204 Algorithm 10, `BitsToInteger(y, α)`:
`x ← 0; for i from 1 to α: x ← 2x + y[α − i]`. -/
def bitsToInteger (y : List ℕ) (α : ℕ) : ℕ :=
  (List.range α).foldl (fun x i => 2 * x + y.getD (α - (i + 1)) 0) 0

/-- FIPS 204 Algorithm 11, `IntegerToBytes(x, α)`. -/
def integerToBytes (x α : ℕ) : List ℕ := (digitLoop 256 x α []).2

/-- FIPS 204 Algorithm 12 `BitsToBytes(y)` (= FIPS 203 Algorithm 3):
`z ← 0^⌈α/8⌉; for i from 0 to α − 1: z[⌊i/8⌋] ← z[⌊i/8⌋] + y[i]·2^(i mod 8)`. -/
def bitsToBytes (y : List ℕ) : List ℕ :=
  (List.range y.length).foldl
    (fun (z : List ℕ) i => z.modify (i / 8) (· + y.getD i 0 * 2 ^ (i % 8)))
    (List.replicate ((y.length + 7) / 8) 0)

/-- FIPS 204 Algorithm 13 `BytesToBits(z)` (= FIPS 203 Algorithm 4):
`for i from 0 to α − 1: for j from 0 to 7: y[8i + j] ← z'[i] mod 2;
z'[i] ← ⌊z'[i]/2⌋`. Only `z'[i]` is touched in iteration `i`, so it is kept
in the scalar component of the inner loop state. -/
def bytesToBits (z : List ℕ) : List ℕ :=
  (List.range z.length).foldl (fun (y : List ℕ) i => (digitLoop 2 (z.getD i 0) 8 y).2) []

/-- FIPS 203 Algorithm 5, `ByteEncode_d(F)`:
`for i < 256: a ← F[i]; for j < d: b[i·d + j] ← a mod 2; a ← (a − b[i·d+j])/2`,
then `BitsToBytes(b)`. -/
def byteEncode (d : ℕ) (F : List ℕ) : List ℕ :=
  let b := (List.range 256).foldl (fun (b : List ℕ) i =>
    ((List.range d).foldl (fun (s : ℕ × List ℕ) _ => ((s.1 - s.1 % 2) / 2, s.2 ++ [s.1 % 2]))
      (F.getD i 0, b)).2) []
  bitsToBytes b

/-- The modulus `m` of FIPS 203 Algorithm 6: `2^d` if `d < 12`, `q` if `d = 12`. -/
def byteDecodeModulus (d : ℕ) : ℕ := if d < 12 then 2 ^ d else q

/-- FIPS 203 Algorithm 6, `ByteDecode_d(B)`:
`b ← BytesToBits(B); F[i] ← Σ_{j<d} b[i·d + j]·2^j mod m`. -/
def byteDecode (d : ℕ) (B : List ℕ) : List ℕ :=
  let b := bytesToBits B
  (List.range 256).map fun i =>
    (∑ j ∈ Finset.range d, b.getD (i * d + j) 0 * 2 ^ j) % byteDecodeModulus d

/-- `bitlen a`, the bit length of a positive integer (FIPS 204 §2.3). -/
def bitlen (a : ℕ) : ℕ := a.size

/-- FIPS 204 Algorithm 16, `SimpleBitPack(w, b)`:
`z ← (); for i < 256: z ← z ‖ IntegerToBits(w_i, bitlen b)`; `BitsToBytes(z)`. -/
def simpleBitPack (w : List ℕ) (b : ℕ) : List ℕ :=
  let z := (List.range 256).foldl (fun z i => z ++ integerToBits (w.getD i 0) (bitlen b)) []
  bitsToBytes z

/-- FIPS 204 Algorithm 17, `BitPack(w, a, b)`:
`z ← (); for i < 256: z ← z ‖ IntegerToBits(b − w_i, bitlen(a + b))`;
`BitsToBytes(z)`. The coefficients lie in `[−a, b]`, so `b − w_i ≥ 0`. -/
def bitPack (w : List ℤ) (a b : ℕ) : List ℕ :=
  let z := (List.range 256).foldl
    (fun z i => z ++ integerToBits ((b : ℤ) - w.getD i 0).toNat (bitlen (a + b))) []
  bitsToBytes z

/-- FIPS 204 Algorithm 18, `SimpleBitUnpack(v, b)`:
`c ← bitlen b; z ← BytesToBits(v);
w_i ← BitsToInteger((z[ic], …, z[ic + c − 1]), c)`. -/
def simpleBitUnpack (v : List ℕ) (b : ℕ) : List ℕ :=
  let c := bitlen b
  let z := bytesToBits v
  (List.range 256).map fun i => bitsToInteger ((List.range c).map fun t => z.getD (i * c + t) 0) c

/-- FIPS 204 Algorithm 19, `BitUnpack(v, a, b)`:
`c ← bitlen(a + b); z ← BytesToBits(v);
w_i ← b − BitsToInteger((z[ic], …, z[ic + c − 1]), c)`. -/
def bitUnpack (v : List ℕ) (a b : ℕ) : List ℤ :=
  let c := bitlen (a + b)
  let z := bytesToBits v
  (List.range 256).map fun i =>
    (b : ℤ) - bitsToInteger ((List.range c).map fun t => z.getD (i * c + t) 0) c

/-! ## Closed forms -/

theorem digitLoop_eq (B x α : ℕ) (pre : List ℕ) :
    digitLoop B x α pre = (x / B ^ α, pre ++ (List.range α).map (fun i => x / B ^ i % B)) := by
  induction α with
  | zero => simp [digitLoop]
  | succ α ih =>
    unfold digitLoop at ih ⊢
    rw [List.range_succ, List.foldl_append, ih]
    simp [Nat.div_div_eq_div_mul, pow_succ]

theorem integerToBits_eq (x α : ℕ) :
    integerToBits x α = (List.range α).map (fun i => x / 2 ^ i % 2) := by
  simp [integerToBits, digitLoop_eq]

theorem integerToBytes_eq (x α : ℕ) :
    integerToBytes x α = (List.range α).map (fun i => x / 256 ^ i % 256) := by
  simp [integerToBytes, digitLoop_eq]

theorem length_integerToBits (x α : ℕ) : (integerToBits x α).length = α := by
  simp [integerToBits_eq]

/-- `IntegerToBits(x, α)` are the `α` low bits of `x`. -/
theorem ofDigits_integerToBits (x α : ℕ) : ofDigits 2 (integerToBits x α) = x % 2 ^ α := by
  rw [integerToBits_eq, ofDigits_bits]

/-- The loop `for i < m: acc ← acc ‖ f i`. -/
theorem foldl_append_range {β : Type} (f : ℕ → List β) (m : ℕ) (pre : List β) :
    (List.range m).foldl (fun z i => z ++ f i) pre = pre ++ (List.range m).flatMap f := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, List.foldl_append, ih, List.flatMap_append]

theorem flatMap_range_getD' {α β : Type} (w : List α) (d : α) (f : α → List β) :
    (List.range w.length).flatMap (fun i => f (w.getD i d)) = w.flatMap f := by
  conv_rhs => rw [← map_getD_range' w d]
  rw [List.flatMap_map]

theorem flatMap_range_getD {β : Type} (w : List ℕ) (f : ℕ → List β) :
    (List.range w.length).flatMap (fun i => f (w.getD i 0)) = w.flatMap f :=
  flatMap_range_getD' w 0 f

theorem bytesToBits_eq (z : List ℕ) :
    bytesToBits z = z.flatMap (fun c => (List.range 8).map (fun i => c / 2 ^ i % 2)) := by
  have key : ∀ m, (List.range m).foldl
      (fun (y : List ℕ) i => (digitLoop 2 (z.getD i 0) 8 y).2) [] =
      (List.range m).flatMap (fun i => (List.range 8).map (fun t => z.getD i 0 / 2 ^ t % 2)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, ih, List.flatMap_append]
      simp [digitLoop_eq]
  rw [bytesToBits, key, flatMap_range_getD z (fun c => (List.range 8).map (fun i => c / 2 ^ i % 2))]

/-- `BitsToInteger(y, α)` reads the first `α` entries of `y` as a
little-endian number. -/
theorem bitsToInteger_eq (y : List ℕ) (α : ℕ) :
    bitsToInteger y α = ofDigits 2 ((List.range α).map (fun t => y.getD t 0)) := by
  have key : ∀ m, m ≤ α → (List.range m).foldl (fun x i => 2 * x + y.getD (α - (i + 1)) 0) 0 =
      ofDigits 2 ((List.range m).map (fun t => y.getD (α - m + t) 0)) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      conv_lhs => rw [List.range_succ, List.foldl_append]
      rw [ih (by omega), List.range_succ_eq_map]
      simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_map, Nat.ofDigits_cons]
      have : (List.map ((fun t => y.getD (α - (m + 1) + t) 0) ∘ Nat.succ) (List.range m)) =
          List.map (fun t => y.getD (α - m + t) 0) (List.range m) := by
        apply List.map_congr_left
        intro t _
        simp only [Function.comp_apply]
        congr 1
        omega
      rw [this]
      simp only [Nat.add_zero]
      ring
  rw [bitsToInteger, key α le_rfl]
  simp

theorem ofDigits_modify_add (l : List ℕ) (j δ : ℕ) (hj : j < l.length) :
    ofDigits 256 (l.modify j (· + δ)) = ofDigits 256 l + 256 ^ j * δ := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero => simp [List.modify_zero_cons, Nat.ofDigits_cons]; ring
    | succ j =>
      rw [List.modify_succ_cons, Nat.ofDigits_cons, Nat.ofDigits_cons,
        ih j (by simpa using hj)]
      ring

/-- The state of the `BitsToBytes` loop after `m` iterations. -/
theorem bitsToBytes_loop (y : List ℕ) (hy : ∀ x ∈ y, x < 2) (m : ℕ) (hm : m ≤ y.length) :
    let B := (List.range m).foldl
      (fun (z : List ℕ) i => z.modify (i / 8) (· + y.getD i 0 * 2 ^ (i % 8)))
      (List.replicate ((y.length + 7) / 8) 0)
    B.length = (y.length + 7) / 8 ∧
    ofDigits 256 B = ofDigits 2 ((List.range m).map (fun i => y.getD i 0)) ∧
    ∀ j (hj : j < B.length), B[j] < 2 ^ (min 8 (m - 8 * j)) := by
  induction m with
  | zero =>
    refine ⟨by simp, ?_, ?_⟩
    · simp only [List.range_zero, List.foldl_nil, List.map_nil, Nat.ofDigits_nil]
      induction ((y.length + 7) / 8) with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ, Nat.ofDigits_cons, ih]
    · intro j hj; simp
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    simp only at h1 h2 h3 ⊢
    set B := (List.range m).foldl
      (fun (z : List ℕ) i => z.modify (i / 8) (· + y.getD i 0 * 2 ^ (i % 8)))
      (List.replicate ((y.length + 7) / 8) 0) with hB
    have hstep : (List.range (m + 1)).foldl
        (fun (z : List ℕ) i => z.modify (i / 8) (· + y.getD i 0 * 2 ^ (i % 8)))
        (List.replicate ((y.length + 7) / 8) 0) =
        B.modify (m / 8) (· + y.getD m 0 * 2 ^ (m % 8)) := by
      rw [List.range_succ, List.foldl_append]; rfl
    rw [hstep]
    have hjm : m / 8 < B.length := by rw [h1]; omega
    have hym : y.getD m 0 < 2 := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hy _ (List.getElem_mem _)
    refine ⟨by simp [h1], ?_, ?_⟩
    · rw [ofDigits_modify_add _ _ _ hjm, h2, List.range_succ, List.map_append, List.map_singleton,
        ofDigits_append_single, List.length_map, List.length_range]
      have : (256 : ℕ) ^ (m / 8) * 2 ^ (m % 8) = 2 ^ m := by
        rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul, ← pow_add]
        congr 1; omega
      rw [← this]; ring
    · intro j hj
      rw [List.getElem_modify]
      split_ifs with hj8
      · subst hj8
        have hb := h3 (m / 8) hjm
        have e1 : min 8 (m - 8 * (m / 8)) = m % 8 := by omega
        have e2 : min 8 (m + 1 - 8 * (m / 8)) = m % 8 + 1 := by omega
        rw [e1] at hb; rw [e2, pow_succ]
        have : y.getD m 0 * 2 ^ (m % 8) ≤ 1 * 2 ^ (m % 8) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      · have hb := h3 j (by simpa using hj)
        calc _ < 2 ^ min 8 (m - 8 * j) := hb
          _ ≤ 2 ^ min 8 (m + 1 - 8 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `BitsToBytes` of a bit string whose length is a multiple of 8. -/
theorem bitsToBytes_regroup {y : List ℕ} (hy : ∀ x ∈ y, x < 2) (h8 : 8 ∣ y.length) :
    Regroup 1 8 y (bitsToBytes y) := by
  obtain ⟨h1, h2, h3⟩ := bitsToBytes_loop y hy y.length le_rfl
  refine ⟨?_, by simpa using hy, ?_, ?_⟩
  · rw [bitsToBytes, h1]; omega
  · intro x hx
    rw [bitsToBytes] at hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have := h3 j hj
    rw [h1] at hj
    rwa [show min 8 (y.length - 8 * j) = 8 by omega] at this
  · rw [bitsToBytes, show (2 : ℕ) ^ 8 = 256 by norm_num, h2, map_getD_range, pow_one]

theorem bytesToBits_regroup {z : List ℕ} (hz : ∀ x ∈ z, x < 256) :
    Regroup 8 1 z (bytesToBits z) := by
  rw [bytesToBits_eq]
  exact regroup_flatMap_bits (c := 8) (by simpa using hz)

theorem bytesToBits_lt {z : List ℕ} (hz : ∀ x ∈ z, x < 256) : ∀ x ∈ bytesToBits z, x < 2 := by
  simpa using (bytesToBits_regroup hz).right_lt

theorem length_bytesToBits (z : List ℕ) : (bytesToBits z).length = z.length * 8 := by
  rw [bytesToBits_eq]
  induction z with
  | nil => simp
  | cons x z ih => simp [List.flatMap_cons, ih]; ring

/-! ## `ByteEncode_d` and `ByteDecode_d` -/

/-- The inner loop of `ByteEncode_d`. -/
theorem byteEncode_inner (x d : ℕ) (pre : List ℕ) :
    (List.range d).foldl (fun (s : ℕ × List ℕ) _ => ((s.1 - s.1 % 2) / 2, s.2 ++ [s.1 % 2]))
      (x, pre) = (x / 2 ^ d, pre ++ (List.range d).map (fun i => x / 2 ^ i % 2)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.range_succ, List.foldl_append, ih]
    have h2 : ∀ a : ℕ, (a - a % 2) / 2 = a / 2 := by intro a; omega
    simp [Nat.div_div_eq_div_mul, pow_succ, h2]

theorem byteEncode_bits (d : ℕ) (F : List ℕ) (hF : F.length = 256) :
    (List.range 256).foldl (fun (b : List ℕ) i =>
      ((List.range d).foldl (fun (s : ℕ × List ℕ) _ => ((s.1 - s.1 % 2) / 2, s.2 ++ [s.1 % 2]))
        (F.getD i 0, b)).2) [] =
    F.flatMap (fun x => (List.range d).map (fun i => x / 2 ^ i % 2)) := by
  have hf : (fun (b : List ℕ) i =>
      ((List.range d).foldl (fun (s : ℕ × List ℕ) _ => ((s.1 - s.1 % 2) / 2, s.2 ++ [s.1 % 2]))
        (F.getD i 0, b)).2) =
      (fun (b : List ℕ) i => b ++ (List.range d).map (fun t => F.getD i 0 / 2 ^ t % 2)) := by
    funext b i; rw [byteEncode_inner]
  rw [hf, foldl_append_range (fun i => (List.range d).map (fun t => F.getD i 0 / 2 ^ t % 2)) 256 [],
    List.nil_append, ← hF,
    flatMap_range_getD F (fun x => (List.range d).map (fun t => x / 2 ^ t % 2))]

/-- `ByteEncode_d(F)` for `F ∈ [0, 2^d)^256`: the bytes are the little-endian
regrouping of the `d`-bit coefficients. -/
theorem byteEncode_regroup {d : ℕ} {F : List ℕ} (hF : F.length = 256)
    (hd : ∀ x ∈ F, x < 2 ^ d) : Regroup d 8 F (byteEncode d F) := by
  have h1 := regroup_flatMap_bits hd
  unfold byteEncode
  simp only
  rw [byteEncode_bits d F hF]
  refine h1.trans (bitsToBytes_regroup (by simpa using h1.right_lt) ?_)
  have := h1.length
  rw [hF] at this
  exact ⟨32 * d, by omega⟩

theorem length_byteEncode {d : ℕ} {F : List ℕ} (hF : F.length = 256)
    (hd : ∀ x ∈ F, x < 2 ^ d) : (byteEncode d F).length = 32 * d := by
  have := (byteEncode_regroup hF hd).length
  rw [hF] at this; omega

theorem sum_bits_eq_ofDigits (d : ℕ) (f : ℕ → ℕ) :
    ∑ j ∈ Finset.range d, f j * 2 ^ j = ofDigits 2 ((List.range d).map f) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.map_singleton,
      ofDigits_append_single, List.length_map, List.length_range]
    ring

/-- `ByteDecode_d` before the final reduction modulo `m`. -/
def byteDecodeRaw (d : ℕ) (B : List ℕ) : List ℕ :=
  (List.range 256).map fun i => ∑ j ∈ Finset.range d, (bytesToBits B).getD (i * d + j) 0 * 2 ^ j

theorem byteDecode_eq_map (d : ℕ) (B : List ℕ) :
    byteDecode d B = (byteDecodeRaw d B).map (· % byteDecodeModulus d) := by
  simp [byteDecode, byteDecodeRaw]

/-- The unreduced `ByteDecode_d(B)` for `B ∈ 𝔹^{32d}` is the `d`-bit
regrouping of the bytes. -/
theorem byteDecodeRaw_regroup {d : ℕ} {B : List ℕ} (hB : B.length = 32 * d)
    (hb : ∀ x ∈ B, x < 256) : Regroup d 8 (byteDecodeRaw d B) B := by
  have hz := bytesToBits_regroup hb
  have hc := regroup_chunks (c := d) (N := 256) (z := bytesToBits B) (bytesToBits_lt hb)
    (by rw [length_bytesToBits, hB]; ring)
  have : byteDecodeRaw d B = (List.range 256).map
      (fun i => ofDigits 2 ((List.range d).map (fun t => (bytesToBits B).getD (i * d + t) 0))) := by
    simp only [byteDecodeRaw, sum_bits_eq_ofDigits]
  rw [this]
  exact hc.trans hz.symm

/-- For `d < 12`, `ByteDecode_d` is the `d`-bit regrouping of the bytes. -/
theorem byteDecode_regroup {d : ℕ} (hd : d < 12) {B : List ℕ} (hB : B.length = 32 * d)
    (hb : ∀ x ∈ B, x < 256) : Regroup d 8 (byteDecode d B) B := by
  have h := byteDecodeRaw_regroup hB hb
  have : byteDecode d B = byteDecodeRaw d B := by
    rw [byteDecode_eq_map]
    conv_rhs => rw [← List.map_id (byteDecodeRaw d B)]
    apply List.map_congr_left
    intro x hx
    simp only [byteDecodeModulus, hd, ↓reduceIte, id]
    exact Nat.mod_eq_of_lt (h.left_lt x hx)
  rw [this]; exact h

/-! ## FIPS 204 packing -/

theorem bitlen_eq {a c : ℕ} (h1 : 2 ^ (c - 1) ≤ a) (h2 : a < 2 ^ c) (hc : 1 ≤ c) : bitlen a = c := by
  unfold bitlen
  apply le_antisymm
  · exact Nat.size_le.mpr h2
  · have := Nat.lt_size.mpr h1
    omega

theorem simpleBitPack_eq (w : List ℕ) (b : ℕ) (hw : w.length = 256) :
    simpleBitPack w b =
      bitsToBytes (w.flatMap fun x => (List.range (bitlen b)).map (fun i => x / 2 ^ i % 2)) := by
  unfold simpleBitPack
  simp only
  rw [foldl_append_range, List.nil_append, ← hw, flatMap_range_getD w (fun x => integerToBits x _)]
  simp only [integerToBits_eq]

/-- `SimpleBitPack(w, b)` for `w ∈ [0, 2^bitlen(b))^256`. -/
theorem simpleBitPack_regroup {w : List ℕ} {b : ℕ} (hw : w.length = 256)
    (hlt : ∀ x ∈ w, x < 2 ^ bitlen b) : Regroup (bitlen b) 8 w (simpleBitPack w b) := by
  rw [simpleBitPack_eq w b hw]
  have h1 := regroup_flatMap_bits hlt
  refine h1.trans (bitsToBytes_regroup (by simpa using h1.right_lt) ?_)
  have := h1.length
  rw [hw] at this
  exact ⟨32 * bitlen b, by omega⟩

/-- `BitPack(w, a, b)` is `SimpleBitPack` of the codes `b − w_i`. -/
theorem bitPack_eq (w : List ℤ) (a b : ℕ) (hw : w.length = 256) :
    bitPack w a b = bitsToBytes ((w.map fun x => ((b : ℤ) - x).toNat).flatMap
      fun x => (List.range (bitlen (a + b))).map (fun i => x / 2 ^ i % 2)) := by
  unfold bitPack
  simp only
  rw [foldl_append_range, List.nil_append, List.flatMap_map, ← hw,
    flatMap_range_getD' w 0 (fun x => integerToBits ((b : ℤ) - x).toNat (bitlen (a + b)))]
  simp only [integerToBits_eq]

theorem bitPack_regroup {w : List ℤ} {a b : ℕ} (hw : w.length = 256)
    (hlt : ∀ x ∈ w, ((b : ℤ) - x).toNat < 2 ^ bitlen (a + b)) :
    Regroup (bitlen (a + b)) 8 (w.map fun x => ((b : ℤ) - x).toNat) (bitPack w a b) := by
  rw [bitPack_eq w a b hw]
  have h1 := regroup_flatMap_bits (c := bitlen (a + b))
    (codes := w.map fun x => ((b : ℤ) - x).toNat) (by simpa using hlt)
  refine h1.trans (bitsToBytes_regroup (by simpa using h1.right_lt) ?_)
  have := h1.length
  rw [List.length_map, hw] at this
  exact ⟨32 * bitlen (a + b), by omega⟩

/-- The unpacking loop of `SimpleBitUnpack` for `N` codes of `c` bits:
`z ← BytesToBits(v); w_i ← BitsToInteger((z[ic], …, z[ic + c − 1]), c)`. -/
def unpackCodesSpecN (N : ℕ) (v : List ℕ) (c : ℕ) : List ℕ :=
  (List.range N).map fun i =>
    bitsToInteger ((List.range c).map fun t => (bytesToBits v).getD (i * c + t) 0) c

/-- The `c`-bit codes read by `SimpleBitUnpack`/`BitUnpack` (256 of them). -/
def unpackCodesSpec (v : List ℕ) (c : ℕ) : List ℕ := unpackCodesSpecN 256 v c

theorem unpackCodesSpecN_regroup {N : ℕ} {v : List ℕ} {c : ℕ} (hv : v.length * 8 = N * c)
    (hb : ∀ x ∈ v, x < 256) : Regroup c 8 (unpackCodesSpecN N v c) v := by
  have hz := bytesToBits_regroup hb
  have hc := regroup_chunks (c := c) (N := N) (z := bytesToBits v) (bytesToBits_lt hb)
    (by rw [length_bytesToBits, hv])
  have : unpackCodesSpecN N v c = (List.range N).map
      (fun i => ofDigits 2 ((List.range c).map (fun t => (bytesToBits v).getD (i * c + t) 0))) := by
    unfold unpackCodesSpecN
    apply List.map_congr_left
    intro i _
    rw [bitsToInteger_eq]
    congr 1
    apply List.map_congr_left
    intro t ht
    rw [List.mem_range] at ht
    rw [List.getD_eq_getElem _ _ (by simpa using ht)]
    simp
  rw [this]
  exact hc.trans hz.symm

theorem unpackCodesSpec_regroup {v : List ℕ} {c : ℕ} (hv : v.length = 32 * c)
    (hb : ∀ x ∈ v, x < 256) : Regroup c 8 (unpackCodesSpec v c) v :=
  unpackCodesSpecN_regroup (by rw [hv]; ring) hb

theorem simpleBitUnpack_eq (v : List ℕ) (b : ℕ) :
    simpleBitUnpack v b = unpackCodesSpec v (bitlen b) := rfl

theorem bitUnpack_eq (v : List ℕ) (a b : ℕ) :
    bitUnpack v a b = (unpackCodesSpec v (bitlen (a + b))).map (fun x : ℕ => (b : ℤ) - (x : ℤ)) := by
  unfold bitUnpack unpackCodesSpec unpackCodesSpecN
  rw [List.map_map]
  rfl

end OcamlPq.Encoding.Spec
