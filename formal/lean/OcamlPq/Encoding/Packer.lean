import OcamlPq.Encoding.Spec
import OcamlPq.Common.Int

/-!
# The accumulator bit packer (`pack_codes` / `unpack_codes`)

Models of `pack_codes` and `unpack_codes` (`mldsa/mldsa_engine.ml` lines
265–300), the little-endian accumulator packer used for every ML-DSA
encoding, and of its core loop, which `encode_compressed` /
`decode_compressed` in ML-KEM repeat with an `Int64` accumulator
(`Encoding/Mlkem.lean` reduces those to this file).

## Integer semantics

The OCaml accumulator is an `int`. All values involved are non-negative, and
on non-negative operands OCaml's `lor`, `land` and `lsr` are the `ℕ`
operations `|||`, `&&&` and `>>>`, while `x lsl n` is `x <<< n` as long as the
result does not wrap. The models therefore run over `ℕ`, and the safety
theorems prove that every intermediate value is below `2 ^ (bits + 7)`: for
the widths ML-DSA uses (`bits ≤ 20`) that is below `2 ^ 30`, so it is
`Portable` and no platform wraps (`OcamlPq.wrap_eq_self`).

## Results

* `packCodes_regroup`: for `bits ≥ 1`, codes below `2 ^ bits` and
  `8 ∣ count · bits`, the output bytes are the little-endian regrouping of the
  codes; hence (`packCodes_eq_spec`) `pack_codes` is
  `BitsToBytes(IntegerToBits(c₀, bits) ‖ … ‖ IntegerToBits(c_{n−1}, bits))`.
* `unpackCodes_regroup`: for `bits ∣ 8 · length`, the output codes are the
  regrouping of the input bytes; hence `unpackCodes_packCodes` and
  `packCodes_unpackCodes`: the two are mutually inverse, so every byte string
  of the right length is a valid encoding.
* `packCodes_safe`, `packFlush_step_safe`, `unpackCodes_safe`,
  `unpackRefill_step_safe`: every accumulator value stays below
  `2 ^ (bits + 7)` and every array index is in bounds.
-/

namespace OcamlPq.Encoding.Packer

open Nat (ofDigits)
open OcamlPq.Encoding

/-! ## Bit-level helper lemmas -/

theorem or_shiftLeft_eq_add {a v k : ℕ} (h : a < 2 ^ k) : a ||| (v <<< k) = a + v * 2 ^ k := by
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]; ring

theorem and_ff_eq (x : ℕ) : x &&& 0xff = x % 256 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 8
  simpa using this

theorem shiftRight_eight (x : ℕ) : x >>> 8 = x / 256 := by
  rw [Nat.shiftRight_eq_div_pow]

theorem set_length_append_replicate (E : List ℕ) (x m : ℕ) :
    (E ++ List.replicate (m + 1) 0).set E.length x = (E ++ [x]) ++ List.replicate m 0 := by
  rw [List.set_append]
  simp [List.replicate_succ]

/-! ## `pack_codes` -/

/-- The mutable state of `pack_codes`: `accumulator`, `available`,
`position` and the `output` buffer. -/
structure PackState where
  accumulator : ℕ
  available : ℕ
  position : ℕ
  output : List ℕ

/-- The inner loop of `pack_codes` (`mldsa_engine.ml` lines 274–279):
```
while !available >= 8 do
  set_u8 output !position (!accumulator land 0xff);
  incr position;
  accumulator := !accumulator lsr 8;
  available := !available - 8
done
``` -/
def packFlush (st : PackState) : PackState :=
  if st.available ≥ 8 then
    packFlush { accumulator := st.accumulator >>> 8, available := st.available - 8,
                position := st.position + 1,
                output := st.output.set st.position (st.accumulator &&& 0xff) }
  else st
termination_by st.available

/-- One iteration of the `Array.iter` body of `pack_codes` (lines 272–279):
```
accumulator := !accumulator lor (value lsl !available);
available := !available + bits;
<flush>
``` -/
def packStep (bits : ℕ) (st : PackState) (value : ℕ) : PackState :=
  packFlush { st with accumulator := st.accumulator ||| (value <<< st.available),
                      available := st.available + bits }

/-- The initial state: `Bytes.make (Array.length codes * bits / 8) '\000'` and
zero counters. -/
def packInit (bits : ℕ) (codes : List ℕ) : PackState :=
  ⟨0, 0, 0, List.replicate (codes.length * bits / 8) 0⟩

/-- `pack_codes ~bits codes` (`mldsa/mldsa_engine.ml` lines 265–281). -/
def packCodes (bits : ℕ) (codes : List ℕ) : List ℕ :=
  (codes.foldl (packStep bits) (packInit bits codes)).output

/-- The loop invariant of `pack_codes`. `done` are the codes consumed so far,
`E` the bytes emitted so far, `total = count · bits`. -/
structure PackInv (bits total : ℕ) (done E : List ℕ) (st : PackState) : Prop where
  acc_lt : st.accumulator < 2 ^ st.available
  consumed : 8 * E.length + st.available = done.length * bits
  done_le : done.length * bits ≤ total
  position : st.position = E.length
  output : st.output = E ++ List.replicate (total / 8 - E.length) 0
  bytes_lt : ∀ x ∈ E, x < 256
  value : ofDigits (2 ^ bits) done = ofDigits 256 E + 256 ^ E.length * st.accumulator

/-- One flush iteration is safe: the write index is inside the buffer, the
written value is a byte, and the invariant is preserved. -/
theorem packFlush_step_safe {bits total : ℕ} {done E : List ℕ} {st : PackState}
    (h : PackInv bits total done E st) (h8 : st.available ≥ 8) :
    st.position < st.output.length ∧ st.accumulator &&& 0xff < 256 ∧
    PackInv bits total done (E ++ [st.accumulator % 256])
      { accumulator := st.accumulator >>> 8, available := st.available - 8,
        position := st.position + 1,
        output := st.output.set st.position (st.accumulator &&& 0xff) } := by
  have hc := h.consumed
  have hd := h.done_le
  have hpos : E.length + 1 ≤ total / 8 := by omega
  have hlt : st.accumulator % 256 < 256 := Nat.mod_lt _ (by norm_num)
  refine ⟨?_, by rw [and_ff_eq]; exact hlt, ?_⟩
  · rw [h.output, h.position]; simp; omega
  constructor
  · simp only [shiftRight_eight]
    have := h.acc_lt
    have e : 2 ^ st.available = 2 ^ (st.available - 8) * 256 := by
      rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_add]; congr 1; omega
    rw [e] at this
    exact Nat.div_lt_of_lt_mul (by linarith)
  · simp; omega
  · exact hd
  · simp [h.position]
  · simp only [h.output, h.position, and_ff_eq]
    obtain ⟨m, hm⟩ : ∃ m, total / 8 - E.length = m + 1 := ⟨total / 8 - E.length - 1, by omega⟩
    rw [hm, set_length_append_replicate]
    simp; omega
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h.bytes_lt x hx
    · exact hlt
  · simp only [shiftRight_eight]
    rw [h.value, Nat.ofDigits_append, Nat.ofDigits_singleton, List.length_append,
      List.length_singleton, pow_succ]
    conv_lhs => rw [← Nat.mod_add_div st.accumulator 256]
    ring

/-- The flush loop establishes `available < 8` and preserves the invariant. -/
theorem packFlush_inv {bits total : ℕ} {done : List ℕ} :
    ∀ (st : PackState) (E : List ℕ), PackInv bits total done E st →
      ∃ E', PackInv bits total done E' (packFlush st) ∧ (packFlush st).available < 8 := by
  intro st
  induction st using packFlush.induct with
  | case1 st h8 ih =>
    intro E h
    rw [packFlush, ite_eq_left h8]
    exact ih _ (packFlush_step_safe h h8).2.2
  | case2 st h8 =>
    intro E h
    rw [packFlush, ite_eq_right h8]
    exact ⟨E, h, by omega⟩

/-- The values computed by `accumulator lor (value lsl available)` in one
iteration: both the shifted code and the new accumulator are below
`2 ^ (bits + 7)`. -/
theorem packStep_values_lt {bits total : ℕ} {done E : List ℕ} {st : PackState} {v : ℕ}
    (h : PackInv bits total done E st) (h8 : st.available < 8) (hv : v < 2 ^ bits) :
    v <<< st.available < 2 ^ (bits + 7) ∧
    st.accumulator ||| (v <<< st.available) < 2 ^ (bits + 7) ∧
    st.accumulator ||| (v <<< st.available) = st.accumulator + v * 2 ^ st.available := by
  have hs : v <<< st.available < 2 ^ (bits + st.available) := Nat.shiftLeft_lt hv
  have hpow : 2 ^ (bits + st.available) ≤ 2 ^ (bits + 7) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hacc : st.accumulator < 2 ^ (bits + st.available) :=
    lt_of_lt_of_le h.acc_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine ⟨lt_of_lt_of_le hs hpow, lt_of_lt_of_le (Nat.or_lt_two_pow hacc hs) hpow,
    or_shiftLeft_eq_add h.acc_lt⟩

/-- One iteration of the outer loop preserves the invariant. -/
theorem packStep_inv {bits total : ℕ} {done E : List ℕ} {st : PackState} {v : ℕ}
    (h : PackInv bits total done E st) (h8 : st.available < 8) (hv : v < 2 ^ bits)
    (hle : (done.length + 1) * bits ≤ total) :
    ∃ E', PackInv bits total (done ++ [v]) E' (packStep bits st v) ∧
      (packStep bits st v).available < 8 := by
  apply packFlush_inv
  obtain ⟨-, -, hor⟩ := packStep_values_lt h h8 hv
  have hc := h.consumed
  constructor
  · simp only [hor]
    have := h.acc_lt
    rw [pow_add]
    calc st.accumulator + v * 2 ^ st.available
        < 2 ^ st.available + v * 2 ^ st.available := by omega
      _ = 2 ^ st.available * (v + 1) := by ring
      _ ≤ 2 ^ st.available * 2 ^ bits := Nat.mul_le_mul_left _ hv
  · simp; rw [add_mul, ← hc]; ring
  · simpa using hle
  · exact h.position
  · exact h.output
  · exact h.bytes_lt
  · simp only [hor]
    rw [ofDigits_append_single, h.value, ← pow_mul]
    have e : (2 : ℕ) ^ (bits * done.length) = 256 ^ E.length * 2 ^ st.available := by
      rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul, ← pow_add]; congr 1; linarith
    rw [e]; ring

theorem packFold_inv {bits total : ℕ} :
    ∀ (rest done E : List ℕ) (st : PackState), PackInv bits total done E st →
      st.available < 8 → (done.length + rest.length) * bits ≤ total →
      (∀ v ∈ rest, v < 2 ^ bits) →
      ∃ E', PackInv bits total (done ++ rest) E' (rest.foldl (packStep bits) st) ∧
        (rest.foldl (packStep bits) st).available < 8 := by
  intro rest
  induction rest with
  | nil => intro done E st h h8 _ _; exact ⟨E, by simpa using h, h8⟩
  | cons v rest ih =>
    intro done E st h h8 hle hvs
    obtain ⟨E', h', h8'⟩ := packStep_inv h h8 (hvs v (by simp))
      (by simp at hle; nlinarith)
    have := ih (done ++ [v]) E' _ h' h8' (by simp at hle ⊢; linarith)
      (fun x hx => hvs x (by simp [hx]))
    simpa using this

theorem packInit_inv (bits : ℕ) (codes : List ℕ) :
    PackInv bits (codes.length * bits) [] [] (packInit bits codes) := by
  refine ⟨by simp [packInit], by simp [packInit], by simp, by simp [packInit], by simp [packInit],
    by simp, by simp [packInit]⟩

/-- **Generic packer theorem.** For `bits ≥ 1`, codes below `2 ^ bits` and a
total bit count divisible by 8, `pack_codes` regroups the codes into bytes. -/
theorem packCodes_regroup {bits : ℕ} {codes : List ℕ} (hcodes : ∀ v ∈ codes, v < 2 ^ bits)
    (h8 : 8 ∣ codes.length * bits) : Regroup bits 8 codes (packCodes bits codes) := by
  obtain ⟨E, h, hav⟩ := packFold_inv (bits := bits) (total := codes.length * bits)
    codes [] [] (packInit bits codes) (packInit_inv bits codes)
    (by simp [packInit]) (by simp) hcodes
  simp only [List.nil_append] at h
  have hc := h.consumed
  have hav0 : (codes.foldl (packStep bits) (packInit bits codes)).available = 0 := by omega
  have hacc := h.acc_lt
  rw [hav0, pow_zero, Nat.lt_one_iff] at hacc
  have hout : packCodes bits codes = E := by
    rw [packCodes, h.output]
    have : codes.length * bits / 8 - E.length = 0 := by omega
    rw [this]; simp
  rw [hout]
  refine ⟨by omega, hcodes, by simpa using h.bytes_lt, ?_⟩
  rw [h.value, hacc]; simp

theorem packFlush_output_length (s : PackState) :
    (packFlush s).output.length = s.output.length := by
  induction s using packFlush.induct with
  | case1 s h8 ih2 => rw [packFlush, ite_eq_left h8, ih2]; simp
  | case2 s h8 => rw [packFlush, ite_eq_right h8]

theorem length_packCodes (bits : ℕ) (codes : List ℕ) :
    (packCodes bits codes).length = codes.length * bits / 8 := by
  have : ∀ (rest : List ℕ) (st : PackState), (rest.foldl (packStep bits) st).output.length =
      st.output.length := by
    intro rest
    induction rest with
    | nil => intro st; rfl
    | cons v rest ih =>
      intro st
      rw [List.foldl_cons, ih, packStep, packFlush_output_length]
  rw [packCodes, this]; simp [packInit]

/-- **Safety of `pack_codes`.** At the start of every iteration of the outer
loop (after any prefix `pre` of the codes), `available < 8`, the accumulator
is below `2 ^ available`, and the values `value lsl available` and
`accumulator lor (value lsl available)` are below `2 ^ (bits + 7)`. Together
with `packFlush_step_safe` (every flush writes a byte inside the buffer) this
covers every operation of `pack_codes`. -/
theorem packCodes_safe {bits : ℕ} {codes : List ℕ} (hcodes : ∀ v ∈ codes, v < 2 ^ bits)
    (pre suf : List ℕ) (v : ℕ) (hsplit : codes = pre ++ v :: suf) :
    ∃ E, PackInv bits (codes.length * bits) pre E (pre.foldl (packStep bits) (packInit bits codes)) ∧
    (pre.foldl (packStep bits) (packInit bits codes)).available < 8 ∧
    v <<< (pre.foldl (packStep bits) (packInit bits codes)).available < 2 ^ (bits + 7) ∧
    (pre.foldl (packStep bits) (packInit bits codes)).accumulator |||
      (v <<< (pre.foldl (packStep bits) (packInit bits codes)).available) < 2 ^ (bits + 7) := by
  have hv : v < 2 ^ bits := hcodes v (by simp [hsplit])
  obtain ⟨E, h, hav⟩ := packFold_inv (bits := bits) (total := codes.length * bits)
    pre [] [] (packInit bits codes) (packInit_inv bits codes)
    (by simp [packInit]) (by rw [hsplit]; simp; nlinarith)
    (fun x hx => hcodes x (by simp [hsplit, hx]))
  simp only [List.nil_append] at h
  obtain ⟨h1, h2, -⟩ := packStep_values_lt h hav hv
  exact ⟨E, h, hav, h1, h2⟩

/-! ## `unpack_codes` -/

/-- The mutable state of `unpack_codes`. -/
structure UnpackState where
  accumulator : ℕ
  available : ℕ
  position : ℕ
  output : List ℕ

/-- The refill loop of `unpack_codes` (lines 291–295):
```
while !available < bits do
  accumulator := !accumulator lor (get_u8 input !position lsl !available);
  incr position;
  available := !available + 8
done
``` -/
def unpackRefill (bits : ℕ) (input : List ℕ) (st : UnpackState) : UnpackState :=
  if st.available < bits then
    unpackRefill bits input
      { st with accumulator := st.accumulator ||| (input.getD st.position 0 <<< st.available),
                position := st.position + 1, available := st.available + 8 }
  else st
termination_by bits - st.available

/-- One iteration of the `for index` loop of `unpack_codes` (lines 291–298):
refill, then
```
output.(index) <- !accumulator land mask;
accumulator := !accumulator lsr bits;
available := !available - bits
``` -/
def unpackStep (bits mask : ℕ) (input : List ℕ) (st : UnpackState) (index : ℕ) : UnpackState :=
  let st := unpackRefill bits input st
  { st with output := st.output.set index (st.accumulator &&& mask),
            accumulator := st.accumulator >>> bits, available := st.available - bits }

/-- The loop of `unpack_codes`, for `count` codes, reading from byte `start`.
`unpack_codes` itself starts at 0; ML-KEM's `decode_compressed` starts at an
offset. -/
def unpackLoop (bits count : ℕ) (input : List ℕ) (start : ℕ) : UnpackState :=
  (List.range count).foldl (unpackStep bits ((1 <<< bits) - 1) input)
    ⟨0, 0, start, List.replicate count 0⟩

/-- `unpack_codes ~bits input` (`mldsa/mldsa_engine.ml` lines 283–300). -/
def unpackCodes (bits : ℕ) (input : List ℕ) : List ℕ :=
  (unpackLoop bits (input.length * 8 / bits) input 0).output

/-- The bytes `input[start], …, input[start + m − 1]`. -/
def slice (input : List ℕ) (start m : ℕ) : List ℕ :=
  (List.range m).map (fun t => input.getD (start + t) 0)

theorem slice_succ (input : List ℕ) (start m : ℕ) :
    slice input start (m + 1) = slice input start m ++ [input.getD (start + m) 0] := by
  simp [slice, List.range_succ]

theorem slice_zero_length (input : List ℕ) : slice input 0 input.length = input := by
  rw [slice]; simp only [Nat.zero_add]; exact map_getD_range input

theorem slice_eq_take_drop (input : List ℕ) (start m : ℕ) (h : start + m ≤ input.length) :
    slice input start m = (input.drop start).take m := by
  apply List.ext_getElem
  · simp [slice]; omega
  · intro i h1 h2
    simp [slice, List.getElem?_eq_getElem (show start + i < input.length by simp [slice] at h1; omega)]

theorem slice_lt {input : List ℕ} (hb : ∀ x ∈ input, x < 256) (start m : ℕ) :
    ∀ x ∈ slice input start m, x < 256 := by
  intro x hx
  simp only [slice, List.mem_map, List.mem_range] at hx
  obtain ⟨t, -, rfl⟩ := hx
  by_cases h : start + t < input.length
  · rw [List.getD_eq_getElem _ _ h]; exact hb _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]; norm_num

/-- The loop invariant of the unpacker at the top of an iteration. `O` are the
codes produced so far, `nbytes` the number of input bytes available from
`start`. -/
structure UnpackInv (bits count nbytes start : ℕ) (input : List ℕ) (O : List ℕ)
    (st : UnpackState) : Prop where
  acc_lt : st.accumulator < 2 ^ st.available
  start_le : start ≤ st.position
  consumed : 8 * (st.position - start) = O.length * bits + st.available
  avail_lt : st.available < 8
  outputs_le : O.length ≤ count
  output : st.output = O ++ List.replicate (count - O.length) 0
  codes_lt : ∀ x ∈ O, x < 2 ^ bits
  value : ofDigits 256 (slice input start (st.position - start)) =
    ofDigits (2 ^ bits) O + 2 ^ (bits * O.length) * st.accumulator

/-- The invariant of the refill loop. -/
structure RefillInv (bits count nbytes start : ℕ) (input : List ℕ) (O : List ℕ)
    (st : UnpackState) : Prop where
  acc_lt : st.accumulator < 2 ^ st.available
  start_le : start ≤ st.position
  consumed : 8 * (st.position - start) = O.length * bits + st.available
  avail_le : st.available ≤ bits + 7
  outputs_lt : O.length < count
  value : ofDigits 256 (slice input start (st.position - start)) =
    ofDigits (2 ^ bits) O + 2 ^ (bits * O.length) * st.accumulator

/-- One refill iteration is safe: the byte read is inside the input, the
shifted byte and the new accumulator are below `2 ^ (bits + 7)`, and the
invariant is preserved. -/
theorem unpackRefill_step_safe {bits count nbytes start : ℕ} {input O : List ℕ}
    {st : UnpackState} (hin : start + nbytes ≤ input.length) (hcount : count * bits ≤ 8 * nbytes)
    (hb : ∀ x ∈ input, x < 256)
    (h : RefillInv bits count nbytes start input O st) (hlt : st.available < bits) :
    st.position < input.length ∧
    input.getD st.position 0 <<< st.available < 2 ^ (bits + 7) ∧
    st.accumulator ||| (input.getD st.position 0 <<< st.available) < 2 ^ (bits + 7) ∧
    RefillInv bits count nbytes start input O
      { st with accumulator := st.accumulator ||| (input.getD st.position 0 <<< st.available),
                position := st.position + 1, available := st.available + 8 } := by
  have hc := h.consumed
  have ho := h.outputs_lt
  have hs := h.start_le
  have hpos : st.position < input.length := by
    have : O.length * bits + bits ≤ count * bits := by nlinarith
    omega
  have hbyte : input.getD st.position 0 < 2 ^ 8 := by
    rw [List.getD_eq_getElem _ _ hpos]; exact hb _ (List.getElem_mem hpos)
  have hshift : input.getD st.position 0 <<< st.available < 2 ^ (8 + st.available) :=
    Nat.shiftLeft_lt hbyte
  have hacc : st.accumulator < 2 ^ (8 + st.available) :=
    lt_of_lt_of_le h.acc_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hpow : 2 ^ (8 + st.available) ≤ 2 ^ (bits + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hor := or_shiftLeft_eq_add (v := input.getD st.position 0) h.acc_lt
  refine ⟨hpos, lt_of_lt_of_le hshift hpow, lt_of_lt_of_le (Nat.or_lt_two_pow hacc hshift) hpow, ?_⟩
  constructor
  · simp only [hor]
    have := h.acc_lt
    rw [pow_add, show (2 : ℕ) ^ 8 = 256 by norm_num]
    have hb' : input.getD st.position 0 < 256 := by simpa using hbyte
    calc st.accumulator + input.getD st.position 0 * 2 ^ st.available
        < 2 ^ st.available + input.getD st.position 0 * 2 ^ st.available := by omega
      _ = 2 ^ st.available * (input.getD st.position 0 + 1) := by ring
      _ ≤ 2 ^ st.available * 256 := Nat.mul_le_mul_left _ hb'
  · simp; omega
  · simp; omega
  · simp; omega
  · exact ho
  · simp only [hor]
    rw [show st.position + 1 - start = st.position - start + 1 by omega, slice_succ,
      ofDigits_append_single, h.value, show start + (st.position - start) = st.position by omega]
    simp only [slice, List.length_map, List.length_range]
    have e : (256 : ℕ) ^ (st.position - start) = 2 ^ (bits * O.length) * 2 ^ st.available := by
      rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul, ← pow_add]; congr 1; linarith
    rw [e]; ring

theorem unpackRefill_inv {bits count nbytes start : ℕ} {input O : List ℕ}
    (hin : start + nbytes ≤ input.length) (hcount : count * bits ≤ 8 * nbytes)
    (hb : ∀ x ∈ input, x < 256) :
    ∀ st : UnpackState, RefillInv bits count nbytes start input O st →
      RefillInv bits count nbytes start input O (unpackRefill bits input st) ∧
      bits ≤ (unpackRefill bits input st).available ∧
      (unpackRefill bits input st).output = st.output := by
  intro st
  induction st using unpackRefill.induct (bits := bits) (input := input) with
  | case1 st hlt ih =>
    intro h
    rw [unpackRefill, ite_eq_left hlt]
    exact ih (unpackRefill_step_safe hin hcount hb h hlt).2.2.2
  | case2 st hlt =>
    intro h
    rw [unpackRefill, ite_eq_right hlt]
    exact ⟨h, by omega, rfl⟩

theorem unpackStep_inv {bits count nbytes start : ℕ} {input O : List ℕ} {st : UnpackState}
    (hbits : 1 ≤ bits)
    (hin : start + nbytes ≤ input.length) (hcount : count * bits ≤ 8 * nbytes)
    (hb : ∀ x ∈ input, x < 256)
    (h : UnpackInv bits count nbytes start input O st) (hO : O.length < count) :
    UnpackInv bits count nbytes start input
      (O ++ [(unpackRefill bits input st).accumulator % 2 ^ bits])
      (unpackStep bits ((1 <<< bits) - 1) input st O.length) := by
  have hr : RefillInv bits count nbytes start input O st :=
    ⟨h.acc_lt, h.start_le, h.consumed, by have := h.avail_lt; omega, hO, h.value⟩
  obtain ⟨hr', hge, hout⟩ := unpackRefill_inv hin hcount hb st hr
  set r := unpackRefill bits input st with hrdef
  have hmask : (1 <<< bits) - 1 = 2 ^ bits - 1 := by rw [Nat.shiftLeft_eq, one_mul]
  have hc := hr'.consumed
  have hav := hr'.avail_le
  have hacc := hr'.acc_lt
  have e : 2 ^ r.available = 2 ^ bits * 2 ^ (r.available - bits) := by
    rw [← pow_add]; congr 1; omega
  unfold unpackStep
  simp only [← hrdef, hmask, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  constructor
  · simp only
    rw [e] at hacc
    exact Nat.div_lt_of_lt_mul hacc
  · exact hr'.start_le
  · simp only [List.length_append, List.length_singleton]; rw [hc]; ring_nf; omega
  · simp only; omega
  · simp; omega
  · simp only [hout, h.output]
    obtain ⟨m, hm⟩ : ∃ m, count - O.length = m + 1 := ⟨count - O.length - 1, by omega⟩
    rw [hm, set_length_append_replicate]
    simp; omega
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h.codes_lt x hx
    · exact Nat.mod_lt _ (by positivity)
  · simp only
    rw [hr'.value, ofDigits_append_single, List.length_append, List.length_singleton, ← pow_mul]
    have := Nat.mod_add_div r.accumulator (2 ^ bits)
    rw [show bits * (O.length + 1) = bits * O.length + bits by ring, pow_add]
    conv_lhs => rw [← this]
    ring

theorem unpackLoop_inv {bits count nbytes start : ℕ} {input : List ℕ} (hbits : 1 ≤ bits)
    (hin : start + nbytes ≤ input.length) (hcount : count * bits ≤ 8 * nbytes)
    (hb : ∀ x ∈ input, x < 256) :
    ∀ m, m ≤ count → ∃ O, O.length = m ∧ UnpackInv bits count nbytes start input O
      ((List.range m).foldl (unpackStep bits ((1 <<< bits) - 1) input)
        ⟨0, 0, start, List.replicate count 0⟩) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], rfl, ?_⟩
    exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp [slice]⟩
  | succ m ih =>
    intro hm
    obtain ⟨O, hO, h⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have := unpackStep_inv hbits hin hcount hb h (by omega)
    rw [hO] at this
    exact ⟨_, by simp [hO], this⟩

/-- **Generic unpacker theorem.** Reading `count` codes of `bits ≥ 1` bits
from `nbytes` bytes at offset `start`, where `count · bits = 8 · nbytes`,
yields the `bits`-bit regrouping of those bytes. -/
theorem unpackLoop_regroup {bits count nbytes start : ℕ} {input : List ℕ} (hbits : 1 ≤ bits)
    (hin : start + nbytes ≤ input.length) (hcount : count * bits = 8 * nbytes)
    (hb : ∀ x ∈ input, x < 256) :
    Regroup bits 8 (unpackLoop bits count input start).output (slice input start nbytes) := by
  obtain ⟨O, hO, h⟩ := unpackLoop_inv hbits hin hcount.le hb count le_rfl
  have hc := h.consumed
  have hav := h.avail_lt
  unfold unpackLoop
  -- all `nbytes` bytes are consumed and the accumulator is empty
  have hav0 : ((List.range count).foldl (unpackStep bits ((1 <<< bits) - 1) input)
      ⟨0, 0, start, List.replicate count 0⟩).available = 0 := by
    rw [hO] at hc; omega
  have hpos' : ((List.range count).foldl (unpackStep bits ((1 <<< bits) - 1) input)
      ⟨0, 0, start, List.replicate count 0⟩).position - start = nbytes := by
    rw [hO] at hc; omega
  have hacc := h.acc_lt
  rw [hav0, pow_zero, Nat.lt_one_iff] at hacc
  rw [h.output, hO, Nat.sub_self, List.replicate_zero, List.append_nil]
  refine ⟨?_, h.codes_lt, slice_lt hb start nbytes, ?_⟩
  · simp [slice, hO, hcount]; ring
  · rw [show (2 : ℕ) ^ 8 = 256 by norm_num, ← hpos', h.value, hacc]; simp

theorem unpackCodes_regroup {bits : ℕ} {input : List ℕ} (hbits : 1 ≤ bits)
    (hdiv : bits ∣ input.length * 8) (hb : ∀ x ∈ input, x < 256) :
    Regroup bits 8 (unpackCodes bits input) input := by
  have := unpackLoop_regroup (bits := bits) (count := input.length * 8 / bits)
    (nbytes := input.length) (start := 0) (input := input) hbits (by simp)
    (by rw [Nat.div_mul_cancel hdiv]; ring) hb
  rwa [slice_zero_length] at this

theorem length_unpackCodes {bits : ℕ} {input : List ℕ} (hbits : 1 ≤ bits)
    (hdiv : bits ∣ input.length * 8) (hb : ∀ x ∈ input, x < 256) :
    (unpackCodes bits input).length = input.length * 8 / bits := by
  have := (unpackCodes_regroup hbits hdiv hb).length
  rw [Nat.eq_div_iff_mul_eq_left (by omega) hdiv]
  linarith

/-- **Safety of `unpack_codes`.** At the top of every iteration of the
`for index` loop the invariant holds; `unpackRefill_step_safe` then shows that
every byte read is in bounds and every accumulator value is below
`2 ^ (bits + 7)`, and the output index `index = O.length < count` is in
bounds. -/
theorem unpackCodes_safe {bits count nbytes start : ℕ} {input : List ℕ} (hbits : 1 ≤ bits)
    (hin : start + nbytes ≤ input.length) (hcount : count * bits ≤ 8 * nbytes)
    (hb : ∀ x ∈ input, x < 256) (index : ℕ) (hidx : index < count) :
    ∃ O, O.length = index ∧ index < (List.replicate count 0).length ∧
      UnpackInv bits count nbytes start input O
        ((List.range index).foldl (unpackStep bits ((1 <<< bits) - 1) input)
          ⟨0, 0, start, List.replicate count 0⟩) := by
  obtain ⟨O, hO, h⟩ := unpackLoop_inv hbits hin hcount hb index hidx.le
  exact ⟨O, hO, by simpa using hidx, h⟩

/-! ## Round trips -/

/-- `unpack_codes (pack_codes codes) = codes`. -/
theorem unpackCodes_packCodes {bits : ℕ} {codes : List ℕ} (hbits : 1 ≤ bits)
    (hcodes : ∀ v ∈ codes, v < 2 ^ bits) (h8 : 8 ∣ codes.length * bits) :
    unpackCodes bits (packCodes bits codes) = codes := by
  have hp := packCodes_regroup hcodes h8
  have hdiv : bits ∣ (packCodes bits codes).length * 8 := by
    rw [← hp.length]; exact Dvd.intro_left _ rfl
  exact Regroup.left_unique hbits (unpackCodes_regroup hbits hdiv hp.right_lt) hp.symm.symm

/-- `pack_codes (unpack_codes input) = input`: every byte string whose bit
length is a multiple of `bits` is a valid encoding. -/
theorem packCodes_unpackCodes {bits : ℕ} {input : List ℕ} (hbits : 1 ≤ bits)
    (hdiv : bits ∣ input.length * 8) (hb : ∀ x ∈ input, x < 256) :
    packCodes bits (unpackCodes bits input) = input := by
  have hu := unpackCodes_regroup hbits hdiv hb
  have h8 : 8 ∣ (unpackCodes bits input).length * bits := by
    rw [hu.length]; exact Dvd.intro_left _ rfl
  exact Regroup.right_unique (by norm_num) (packCodes_regroup hu.left_lt h8) hu

/-! ## Relation to the FIPS 204 bit strings -/

/-- `pack_codes ~bits codes = BitsToBytes(IntegerToBits(c₀, bits) ‖ … )`. -/
theorem packCodes_eq_spec {bits : ℕ} {codes : List ℕ}
    (hcodes : ∀ v ∈ codes, v < 2 ^ bits) (h8 : 8 ∣ codes.length * bits) :
    packCodes bits codes = Spec.bitsToBytes (codes.flatMap fun c => Spec.integerToBits c bits) := by
  have h1 := regroup_flatMap_bits hcodes
  simp only [← Spec.integerToBits_eq] at h1
  have h2 := Spec.bitsToBytes_regroup (y := codes.flatMap fun c => Spec.integerToBits c bits)
    (by simpa using h1.right_lt)
    (by have := h1.length; rw [mul_one] at this; rw [← this]; exact h8)
  exact Regroup.right_unique (by norm_num) (packCodes_regroup hcodes h8) (h1.trans h2)

/-- **`unpack_codes` is the FIPS 204 unpacking loop** (`SimpleBitUnpack`
with `N = 8·|input| / bits` codes), for every width `bits ≥ 1` dividing the
input's bit length. -/
theorem unpackCodes_eq_spec {bits : ℕ} {input : List ℕ} (hbits : 1 ≤ bits)
    (hdiv : bits ∣ input.length * 8) (hb : ∀ x ∈ input, x < 256) :
    unpackCodes bits input = Spec.unpackCodesSpecN (input.length * 8 / bits) input bits :=
  Regroup.left_unique hbits (unpackCodes_regroup hbits hdiv hb)
    (Spec.unpackCodesSpecN_regroup (by rw [Nat.div_mul_cancel hdiv]) hb)

/-! ## Portability -/

/-- For `bits ≤ 23` the accumulator bound `2 ^ (bits + 7)` is `Portable`. -/
theorem portable_of_lt_bound {bits x : ℕ} (hbits : bits ≤ 23) (hx : x < 2 ^ (bits + 7)) :
    Portable (x : ℤ) := by
  apply Portable.of_nat_lt
  calc x < 2 ^ (bits + 7) := hx
    _ ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **`pack_codes` is portable** for `bits ≤ 23` (ML-DSA uses 3, 4, 6, 10, 13,
18, 20): at every iteration `value lsl available` and the new accumulator are
`Portable`, so no platform's `int` wraps. -/
theorem packCodes_portable {bits : ℕ} (hbits : bits ≤ 23) {codes : List ℕ}
    (hcodes : ∀ v ∈ codes, v < 2 ^ bits) (pre suf : List ℕ) (v : ℕ)
    (hsplit : codes = pre ++ v :: suf) :
    Portable ((v <<< (pre.foldl (packStep bits) (packInit bits codes)).available : ℕ) : ℤ) ∧
    Portable (((pre.foldl (packStep bits) (packInit bits codes)).accumulator |||
      (v <<< (pre.foldl (packStep bits) (packInit bits codes)).available) : ℕ) : ℤ) := by
  obtain ⟨E, -, -, h1, h2⟩ := packCodes_safe hcodes pre suf v hsplit
  exact ⟨portable_of_lt_bound hbits h1, portable_of_lt_bound hbits h2⟩

/-- **`unpack_codes` is portable** for `bits ≤ 23`: every refill step reads
inside the input and its `get_u8 input position lsl available` and new
accumulator are `Portable`. -/
theorem unpackRefill_portable {bits count nbytes start : ℕ} {input O : List ℕ}
    {st : UnpackState} (hbits : bits ≤ 23) (hin : start + nbytes ≤ input.length)
    (hcount : count * bits ≤ 8 * nbytes) (hb : ∀ x ∈ input, x < 256)
    (h : RefillInv bits count nbytes start input O st) (hlt : st.available < bits) :
    st.position < input.length ∧
    Portable ((input.getD st.position 0 <<< st.available : ℕ) : ℤ) ∧
    Portable ((st.accumulator ||| (input.getD st.position 0 <<< st.available) : ℕ) : ℤ) := by
  obtain ⟨h1, h2, h3, -⟩ := unpackRefill_step_safe hin hcount hb h hlt
  exact ⟨h1, portable_of_lt_bound hbits h2, portable_of_lt_bound hbits h3⟩

end OcamlPq.Encoding.Packer
