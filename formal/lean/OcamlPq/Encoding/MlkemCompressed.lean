import OcamlPq.Encoding.Packer
import OcamlPq.Encoding.Bytes

/-!
# ML-KEM `encode_compressed` / `decode_compressed`

Models of `encode_compressed` and `decode_compressed`
(`lib/mlkem_engine.ml` lines 255–287), the `Int64`-accumulator packers used
for ciphertexts (`d = du, dv`) and messages (`encode_message` /
`decode_message`, `d = 1`, lines 289–290).

`compress` and `decompress` (lines 125–137) are proved correct separately;
here they are arbitrary functions, and the theorems are about the packing:

* `encodeCompressed_eq`: `encode_compressed d f = ByteEncode_d(Compress_d(f))`
  for `d ≤ 56` whenever `compress` returns values below `2 ^ d` (the OCaml
  `compress` ends with `land ((1 lsl d) - 1)`, so it always does).
* `decodeCompressed_eq`: `decode_compressed d s off =
  Decompress_d(ByteDecode_d(s[off : off + 32d]))` for `1 ≤ d < 12`.
* `decodeCompressed_encodeCompressed_codes`: the codes survive a round trip.

The accumulator is modelled with `UInt64`, whose `|||`, `<<<`, `>>>` wrap
exactly like OCaml's `Int64.logor`, `shift_left` and `shift_right_logical`.
`Int64.to_int` is modelled as `UInt64.toNat`; the simulation lemmas show that
the accumulator stays below `2 ^ (d + 7) ≤ 2 ^ 18` for `d ≤ 11`, where every
platform's `Int64.to_int` is exact.
-/

namespace OcamlPq.Encoding.Mlkem

open Nat (ofDigits)
open OcamlPq.Encoding
open OcamlPq.Encoding.Packer

/-! ## `UInt64` arithmetic on small values -/

theorem u64_shiftRight_toNat (a : UInt64) (k : ℕ) (hk : k < 64) :
    (a >>> UInt64.ofNat k).toNat = a.toNat >>> k := by
  rw [UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt hk]

theorem u64_shiftRight8_toNat (a : UInt64) : (a >>> (8 : UInt64)).toNat = a.toNat >>> 8 := by
  rw [UInt64.toNat_shiftRight]; rfl

theorem u64_shiftLeft_toNat (c k : ℕ) (hc : c * 2 ^ k < 2 ^ 64) (hk : k < 64) :
    (UInt64.ofNat c <<< UInt64.ofNat k).toNat = c <<< k := by
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  have hc' : c < 2 ^ 64 := by
    have : c ≤ c * 2 ^ k := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  rw [Nat.mod_eq_of_lt hc', Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt hc]

/-! ## `encode_compressed` -/

/-- The mutable state of `encode_compressed`. -/
structure Pack64 where
  accumulator : UInt64
  bits : ℕ
  pos : ℕ
  out : List ℕ

/-- The inner loop of `encode_compressed` (lines 263–268):
```
while !bits >= 8 do
  set_u8 out !pos (Int64.to_int !accumulator);
  incr pos;
  accumulator := Int64.shift_right_logical !accumulator 8;
  bits := !bits - 8
done
```
(`set_u8` stores `x land 0xff`, line 103). -/
def flush64 (st : Pack64) : Pack64 :=
  if st.bits ≥ 8 then
    flush64 { accumulator := st.accumulator >>> 8, bits := st.bits - 8, pos := st.pos + 1,
              out := st.out.set st.pos (st.accumulator.toNat &&& 0xff) }
  else st
termination_by st.bits

/-- One iteration of the `for i` loop of `encode_compressed` (lines 260–268):
```
accumulator := Int64.logor !accumulator
    (Int64.shift_left (Int64.of_int (compress (Array.unsafe_get f i) d)) !bits);
bits := !bits + d;
<flush>
``` -/
def encStep64 (compress : ℕ → ℕ → ℕ) (d : ℕ) (f : List ℕ) (st : Pack64) (i : ℕ) : Pack64 :=
  flush64 { st with
    accumulator := st.accumulator |||
      (UInt64.ofNat (compress (f.getD i 0) d) <<< UInt64.ofNat st.bits),
    bits := st.bits + d }

/-- `encode_compressed d f` (`lib/mlkem_engine.ml` lines 255–270), with
`n = 256`. -/
def encodeCompressed (compress : ℕ → ℕ → ℕ) (d : ℕ) (f : List ℕ) : List ℕ :=
  ((List.range 256).foldl (encStep64 compress d f) ⟨0, 0, 0, List.replicate (256 * d / 8) 0⟩).out

/-- `encode_message f = encode_compressed 1 f` (line 289). -/
def encodeMessage (compress : ℕ → ℕ → ℕ) (f : List ℕ) : List ℕ := encodeCompressed compress 1 f

/-- The `Int64` state seen as the `ℕ` state of the generic packer. -/
def Pack64.toNat (st : Pack64) : PackState := ⟨st.accumulator.toNat, st.bits, st.pos, st.out⟩

theorem flush64_sim (st : Pack64) : (flush64 st).toNat = packFlush st.toNat := by
  induction st using flush64.induct with
  | case1 st h8 ih =>
    have e : packFlush st.toNat = packFlush
        { accumulator := st.toNat.accumulator >>> 8, available := st.toNat.available - 8,
          position := st.toNat.position + 1,
          output := st.toNat.output.set st.toNat.position (st.toNat.accumulator &&& 0xff) } := by
      rw [packFlush, ite_eq_left (show st.toNat.available ≥ 8 from h8)]
    rw [flush64, ite_eq_left h8, ih, e]
    simp only [Pack64.toNat, u64_shiftRight8_toNat]
  | case2 st h8 =>
    have e : packFlush st.toNat = st.toNat := by
      rw [packFlush, ite_eq_right (show ¬ st.toNat.available ≥ 8 from h8)]
    rw [flush64, ite_eq_right h8, e]

theorem encStep64_sim (compress : ℕ → ℕ → ℕ) (d : ℕ) (f : List ℕ) (st : Pack64) (i : ℕ)
    (hd : d ≤ 56) (hc : compress (f.getD i 0) d < 2 ^ d) (hb : st.bits < 8) :
    (encStep64 compress d f st i).toNat = packStep d st.toNat (compress (f.getD i 0) d) := by
  unfold encStep64 packStep
  rw [flush64_sim]
  congr 1
  simp only [Pack64.toNat, UInt64.toNat_or]
  congr 2
  apply u64_shiftLeft_toNat _ _ _ (by omega)
  calc compress (f.getD i 0) d * 2 ^ st.bits < 2 ^ d * 2 ^ 8 :=
        Nat.mul_lt_mul_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hb.le) (by positivity)
    _ = 2 ^ (d + 8) := by rw [pow_add]
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The `Int64` loop computes exactly the generic packer's states. -/
theorem encodeCompressed_sim (compress : ℕ → ℕ → ℕ) (d : ℕ) (f : List ℕ) (hd : d ≤ 56)
    (hc : ∀ x, compress x d < 2 ^ d) (m : ℕ) (hm : m ≤ 256) :
    ((List.range m).foldl (encStep64 compress d f) ⟨0, 0, 0, List.replicate (256 * d / 8) 0⟩).toNat =
      ((List.range m).map (fun i => compress (f.getD i 0) d)).foldl (packStep d)
        ⟨0, 0, 0, List.replicate (256 * d / 8) 0⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.map_append, List.foldl_append, List.map_singleton,
      List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil, ← ih (by omega)]
    apply encStep64_sim _ _ _ _ _ hd (hc _)
    -- the generic invariant bounds `bits` at the top of each iteration
    have hinit : PackInv d (256 * d) [] [] ⟨0, 0, 0, List.replicate (256 * d / 8) 0⟩ :=
      ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
    obtain ⟨E, -, hav⟩ := packFold_inv (bits := d) (total := 256 * d)
      ((List.range m).map (fun i => compress (f.getD i 0) d)) [] [] _ hinit (by simp)
      (by simp; nlinarith) (by simp [hc])
    rw [← ih (by omega)] at hav
    exact hav

theorem codes_eq (compress : ℕ → ℕ → ℕ) (d : ℕ) (f : List ℕ) (hf : f.length = 256) :
    (List.range 256).map (fun i => compress (f.getD i 0) d) = f.map (fun x => compress x d) := by
  rw [← hf]
  conv_rhs => rw [← map_getD_range f]
  rw [List.map_map]; rfl

/-- `encode_compressed d f` is the generic packer on `Compress_d(f)`. -/
theorem encodeCompressed_eq_packCodes (compress : ℕ → ℕ → ℕ) (d : ℕ) (f : List ℕ)
    (hf : f.length = 256) (hd : d ≤ 56) (hc : ∀ x, compress x d < 2 ^ d) :
    encodeCompressed compress d f = packCodes d (f.map (fun x => compress x d)) := by
  have := encodeCompressed_sim compress d f hd hc 256 le_rfl
  rw [codes_eq compress d f hf] at this
  unfold encodeCompressed packCodes packInit
  have hlen : (f.map (fun x => compress x d)).length * d / 8 = 256 * d / 8 := by simp [hf]
  rw [hlen, ← this]
  rfl

/-- **`encode_compressed d f = ByteEncode_d(Compress_d(f))`** for `d ≤ 56`
and any `compress` whose values are below `2 ^ d`. -/
theorem encodeCompressed_eq (compress : ℕ → ℕ → ℕ) (d : ℕ) (f : List ℕ)
    (hf : f.length = 256) (hd : d ≤ 56) (hc : ∀ x, compress x d < 2 ^ d) :
    encodeCompressed compress d f = Spec.byteEncode d (f.map (fun x => compress x d)) := by
  rw [encodeCompressed_eq_packCodes compress d f hf hd hc]
  have hcodes : ∀ v ∈ f.map (fun x => compress x d), v < 2 ^ d := by simp [hc]
  have hlen : (f.map (fun x => compress x d)).length = 256 := by simp [hf]
  exact Regroup.right_unique (by norm_num)
    (packCodes_regroup hcodes (by rw [hlen]; exact ⟨32 * d, by ring⟩))
    (Spec.byteEncode_regroup hlen hcodes)

theorem length_encodeCompressed (compress : ℕ → ℕ → ℕ) (d : ℕ) (f : List ℕ)
    (hf : f.length = 256) (hd : d ≤ 56) (hc : ∀ x, compress x d < 2 ^ d) :
    (encodeCompressed compress d f).length = 32 * d := by
  rw [encodeCompressed_eq_packCodes compress d f hf hd hc, length_packCodes]; simp [hf]; omega

/-- **Accumulator bound for `encode_compressed`.** At the top of every
iteration the `Int64` accumulator is below `2 ^ bits` with `bits < 8`, so the
value after `logor` is below `2 ^ (d + 7)` (at most `2 ^ 18` for `d ≤ 11`). -/
theorem encodeCompressed_acc_lt (compress : ℕ → ℕ → ℕ) (d : ℕ) (f : List ℕ) (hd : d ≤ 56)
    (hc : ∀ x, compress x d < 2 ^ d) (m : ℕ) (hm : m < 256) :
    let st := (List.range m).foldl (encStep64 compress d f) ⟨0, 0, 0, List.replicate (256 * d / 8) 0⟩
    st.bits < 8 ∧ st.accumulator.toNat < 2 ^ st.bits ∧
      (st.accumulator ||| (UInt64.ofNat (compress (f.getD m 0) d) <<< UInt64.ofNat st.bits)).toNat <
        2 ^ (d + 7) := by
  intro st
  have hsim := encodeCompressed_sim compress d f hd hc m hm.le
  have hinit : PackInv d (256 * d) [] [] ⟨0, 0, 0, List.replicate (256 * d / 8) 0⟩ :=
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  obtain ⟨E, hinv, hav⟩ := packFold_inv (bits := d) (total := 256 * d)
    ((List.range m).map (fun i => compress (f.getD i 0) d)) [] [] _ hinit (by simp)
    (by simp; nlinarith) (by simp [hc])
  rw [← hsim] at hinv hav
  have hlt := packStep_values_lt hinv hav (hc (f.getD m 0))
  refine ⟨hav, hinv.acc_lt, ?_⟩
  rw [UInt64.toNat_or]
  have hb : compress (f.getD m 0) d * 2 ^ st.bits < 2 ^ 64 := by
    calc compress (f.getD m 0) d * 2 ^ st.bits < 2 ^ d * 2 ^ 8 :=
          Nat.mul_lt_mul_of_lt_of_le (hc _) (Nat.pow_le_pow_right (by norm_num) hav.le)
            (by positivity)
      _ = 2 ^ (d + 8) := by rw [pow_add]
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hav' : st.bits < 8 := hav
  rw [u64_shiftLeft_toNat _ _ hb (by omega)]
  exact hlt.2.1

/-! ## `decode_compressed` -/

/-- The mutable state of `decode_compressed`. -/
structure Unpack64 where
  accumulator : UInt64
  bits : ℕ
  pos : ℕ
  out : List ℕ

/-- The refill loop of `decode_compressed` (lines 277–282):
```
while !bits < d do
  accumulator := Int64.logor !accumulator
      (Int64.shift_left (Int64.of_int (get_u8 s !pos)) !bits);
  incr pos;
  bits := !bits + 8
done
``` -/
def refill64 (d : ℕ) (s : List ℕ) (st : Unpack64) : Unpack64 :=
  if st.bits < d then
    refill64 d s { st with
      accumulator := st.accumulator ||| (UInt64.ofNat (s.getD st.pos 0) <<< UInt64.ofNat st.bits),
      pos := st.pos + 1, bits := st.bits + 8 }
  else st
termination_by d - st.bits

/-- One iteration of the `for i` loop of `decode_compressed` (lines 277–285):
refill, then
```
Array.unsafe_set out i (decompress (Int64.to_int !accumulator land mask) d);
accumulator := Int64.shift_right_logical !accumulator d;
bits := !bits - d
``` -/
def decStep64 (decompress : ℕ → ℕ → ℕ) (d : ℕ) (s : List ℕ) (mask : ℕ) (st : Unpack64) (i : ℕ) :
    Unpack64 :=
  let st := refill64 d s st
  { st with out := st.out.set i (decompress (st.accumulator.toNat &&& mask) d),
            accumulator := st.accumulator >>> UInt64.ofNat d, bits := st.bits - d }

/-- `decode_compressed d s off` (`lib/mlkem_engine.ml` lines 272–287), with
`poly_zero ()` as the initial output and `n = 256`. -/
def decodeCompressed (decompress : ℕ → ℕ → ℕ) (d : ℕ) (s : List ℕ) (off : ℕ) : List ℕ :=
  ((List.range 256).foldl (decStep64 decompress d s ((1 <<< d) - 1))
    ⟨0, 0, off, List.replicate 256 0⟩).out

/-- `decode_message s = decode_compressed 1 s 0` (line 290). -/
def decodeMessage (decompress : ℕ → ℕ → ℕ) (s : List ℕ) : List ℕ := decodeCompressed decompress 1 s 0

/-- The `Int64` state seen as the generic unpacker's state, with the output
buffer `out` of the generic run. -/
def Unpack64.toNat (st : Unpack64) (out : List ℕ) : UnpackState :=
  ⟨st.accumulator.toNat, st.bits, st.pos, out⟩

theorem refill64_sim {d nbytes off : ℕ} {s O : List ℕ} (hd : d ≤ 56)
    (hin : off + nbytes ≤ s.length) (hcount : 256 * d ≤ 8 * nbytes) (hb : ∀ x ∈ s, x < 256) :
    ∀ (st : Unpack64) (out : List ℕ), RefillInv d 256 nbytes off s O (st.toNat out) →
      (refill64 d s st).toNat out = unpackRefill d s (st.toNat out) ∧
      (refill64 d s st).out = st.out := by
  intro st
  induction st using refill64.induct (d := d) (s := s) with
  | case1 st hlt ih =>
    intro out h
    obtain ⟨-, -, -, h'⟩ := unpackRefill_step_safe hin hcount hb h hlt
    have hbyte : s.getD st.pos 0 * 2 ^ st.bits < 2 ^ 64 := by
      have h1 := getD_lt_of_all (by norm_num) hb st.pos
      calc s.getD st.pos 0 * 2 ^ st.bits < 2 ^ 8 * 2 ^ d :=
            Nat.mul_lt_mul_of_lt_of_le (by simpa using h1)
              (Nat.pow_le_pow_right (by norm_num) hlt.le) (by positivity)
        _ = 2 ^ (8 + d) := by rw [pow_add]
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hstep : ({ st with
        accumulator := st.accumulator ||| (UInt64.ofNat (s.getD st.pos 0) <<< UInt64.ofNat st.bits),
        pos := st.pos + 1, bits := st.bits + 8 } : Unpack64).toNat out =
        { st.toNat out with
          accumulator := (st.toNat out).accumulator ||| (s.getD (st.toNat out).position 0 <<<
            (st.toNat out).available),
          position := (st.toNat out).position + 1, available := (st.toNat out).available + 8 } := by
      simp only [Unpack64.toNat, UInt64.toNat_or, u64_shiftLeft_toNat _ _ hbyte (by omega)]
    have ih' := ih out (by rw [hstep]; exact h')
    rw [hstep] at ih'
    have e1 : refill64 d s st = refill64 d s { st with
        accumulator := st.accumulator ||| (UInt64.ofNat (s.getD st.pos 0) <<< UInt64.ofNat st.bits),
        pos := st.pos + 1, bits := st.bits + 8 } := by
      rw [refill64, ite_eq_left hlt]
    have e2 : unpackRefill d s (st.toNat out) = unpackRefill d s { st.toNat out with
          accumulator := (st.toNat out).accumulator ||| (s.getD (st.toNat out).position 0 <<<
            (st.toNat out).available),
          position := (st.toNat out).position + 1, available := (st.toNat out).available + 8 } := by
      rw [unpackRefill, ite_eq_left (show (st.toNat out).available < d from hlt)]
    rw [e1, e2]
    exact ⟨ih'.1, ih'.2⟩
  | case2 st hlt =>
    intro out _
    have e1 : refill64 d s st = st := by rw [refill64, ite_eq_right hlt]
    have e2 : unpackRefill d s (st.toNat out) = st.toNat out := by
      rw [unpackRefill, ite_eq_right (show ¬ (st.toNat out).available < d from hlt)]
    rw [e1, e2]
    exact ⟨rfl, rfl⟩

/-- The joint invariant of the `Int64` decoder and the generic unpacker after
`m` iterations: same accumulator, bit count and position; the `Int64` output
holds `Decompress_d` of the codes produced so far. -/
theorem decodeCompressed_loop (decompress : ℕ → ℕ → ℕ) (d : ℕ) (s : List ℕ) (off : ℕ)
    (hd1 : 1 ≤ d) (hd : d ≤ 56) (hin : off + 32 * d ≤ s.length) (hb : ∀ x ∈ s, x < 256) :
    ∀ m, m ≤ 256 → ∃ O, O.length = m ∧
      UnpackInv d 256 (32 * d) off s O
        ((List.range m).foldl (unpackStep d ((1 <<< d) - 1) s) ⟨0, 0, off, List.replicate 256 0⟩) ∧
      ((List.range m).foldl (decStep64 decompress d s ((1 <<< d) - 1))
          ⟨0, 0, off, List.replicate 256 0⟩).toNat
        ((List.range m).foldl (unpackStep d ((1 <<< d) - 1) s)
          ⟨0, 0, off, List.replicate 256 0⟩).output =
        (List.range m).foldl (unpackStep d ((1 <<< d) - 1) s) ⟨0, 0, off, List.replicate 256 0⟩ ∧
      ((List.range m).foldl (decStep64 decompress d s ((1 <<< d) - 1))
          ⟨0, 0, off, List.replicate 256 0⟩).out =
        O.map (fun c => decompress c d) ++ List.replicate (256 - m) 0 := by
  have hcount : 256 * d ≤ 8 * (32 * d) := by omega
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], rfl, ?_, rfl, rfl⟩
    exact ⟨show (0 : ℕ) < 2 ^ 0 by norm_num, show off ≤ off from le_rfl,
      show 8 * (off - off) = 0 * d + 0 by simp, show 0 < 8 by norm_num, show 0 ≤ 256 by norm_num,
      rfl, fun x hx => absurd hx (List.not_mem_nil),
      show ofDigits 256 (slice s off (off - off)) = ofDigits (2 ^ d) [] + 2 ^ (d * 0) * 0 by
        simp [slice]⟩
  | succ m ih =>
    intro hm
    obtain ⟨O, hO, hinv, hsim, hout⟩ := ih (by omega)
    set st := (List.range m).foldl (unpackStep d ((1 <<< d) - 1) s) ⟨0, 0, off, List.replicate 256 0⟩
      with hst
    set st64 := (List.range m).foldl (decStep64 decompress d s ((1 <<< d) - 1))
      ⟨0, 0, off, List.replicate 256 0⟩ with hst64
    have hnew := unpackStep_inv hd1 hin hcount hb hinv (by omega)
    rw [hO] at hnew
    have hr : RefillInv d 256 (32 * d) off s O (st64.toNat st.output) := by
      rw [hsim]
      exact ⟨hinv.acc_lt, hinv.start_le, hinv.consumed, by have := hinv.avail_lt; omega,
        by omega, hinv.value⟩
    obtain ⟨hrs, hrout⟩ := refill64_sim hd (O := O) hin hcount hb st64 st.output hr
    rw [hsim] at hrs
    set r := unpackRefill d s st with hrdef
    set r64 := refill64 d s st64 with hr64def
    have hacc : r64.accumulator.toNat = r.accumulator := congrArg UnpackState.accumulator hrs
    have hbits : r64.bits = r.available := congrArg UnpackState.available hrs
    have hpos : r64.pos = r.position := congrArg UnpackState.position hrs
    have hmask : (1 <<< d) - 1 = 2 ^ d - 1 := by rw [Nat.shiftLeft_eq, one_mul]
    refine ⟨O ++ [r.accumulator % 2 ^ d], by simp [hO], ?_, ?_, ?_⟩
    · rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact hnew
    · simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [decStep64, unpackStep, Unpack64.toNat, ← hr64def, ← hrdef, ← hst, ← hst64]
      rw [u64_shiftRight_toNat _ _ (by omega), hacc, hbits, hpos]
    · rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [decStep64, ← hst64, ← hr64def]
      rw [hrout, hout, hacc, hmask, Nat.and_two_pow_sub_one_eq_mod]
      obtain ⟨k, hk⟩ : ∃ k, 256 - m = k + 1 := ⟨255 - m, by omega⟩
      have hlen : (O.map (fun c => decompress c d)).length = m := by simp [hO]
      have := set_length_append_replicate (O.map (fun c => decompress c d))
        (decompress (r.accumulator % 2 ^ d) d) k
      rw [hlen] at this
      rw [hk, this, List.map_append, List.map_singleton, show 256 - (m + 1) = k by omega]

/-- **`decode_compressed d s off = Decompress_d(ByteDecode_d(s[off : off + 32d]))`**
for `1 ≤ d < 12` and `off + 32 d ≤ |s|` (the ciphertext length is checked by
`ciphertext_of_octets`). -/
theorem decodeCompressed_eq (decompress : ℕ → ℕ → ℕ) (d : ℕ) (s : List ℕ) (off : ℕ)
    (hd1 : 1 ≤ d) (hd : d < 12) (hin : off + 32 * d ≤ s.length) (hb : ∀ x ∈ s, x < 256) :
    decodeCompressed decompress d s off =
      (Spec.byteDecode d (sub s off (32 * d))).map (fun c => decompress c d) := by
  obtain ⟨O, hO, hinv, -, hout⟩ :=
    decodeCompressed_loop decompress d s off hd1 (by omega) hin hb 256 le_rfl
  have hreg := unpackLoop_regroup (bits := d) (count := 256) (nbytes := 32 * d) (start := off)
    (input := s) hd1 hin (by ring) hb
  have houtO : (unpackLoop d 256 s off).output = O := by
    unfold unpackLoop
    rw [hinv.output, hO, Nat.sub_self, List.replicate_zero, List.append_nil]
  rw [houtO] at hreg
  have hsl : slice s off (32 * d) = sub s off (32 * d) := slice_eq_take_drop s off (32 * d) hin
  rw [hsl] at hreg
  have hspec := Spec.byteDecode_regroup (d := d) hd (B := sub s off (32 * d))
    (length_sub s off (32 * d) hin) (sub_lt hb off (32 * d))
  have hOeq : O = Spec.byteDecode d (sub s off (32 * d)) := Regroup.left_unique hd1 hreg hspec
  unfold decodeCompressed
  rw [hout, Nat.sub_self, List.replicate_zero, List.append_nil, hOeq]

/-- **Round trip on codes.** Decoding what `encode_compressed` wrote (followed
by any further bytes `R`) gives back `Decompress_d(Compress_d(f))`: the codes
are transmitted exactly. -/
theorem decodeCompressed_encodeCompressed (compress decompress : ℕ → ℕ → ℕ) (d : ℕ)
    (f : List ℕ) (hf : f.length = 256) (hd1 : 1 ≤ d) (hd : d < 12)
    (hc : ∀ x, compress x d < 2 ^ d) (R : List ℕ) (hR : ∀ x ∈ R, x < 256) :
    decodeCompressed decompress d (encodeCompressed compress d f ++ R) 0 =
      f.map (fun x => decompress (compress x d) d) := by
  have henc := encodeCompressed_eq_packCodes compress d f hf (by omega) hc
  have hcodes : ∀ v ∈ f.map (fun x => compress x d), v < 2 ^ d := by simp [hc]
  have hlen : (f.map (fun x => compress x d)).length = 256 := by simp [hf]
  have hreg := packCodes_regroup hcodes (by rw [hlen]; exact ⟨32 * d, by ring⟩)
  rw [← henc] at hreg
  have hplen : (encodeCompressed compress d f).length = 32 * d :=
    length_encodeCompressed compress d f hf (by omega) hc
  have hsub : sub (encodeCompressed compress d f ++ R) 0 (32 * d) =
      encodeCompressed compress d f := by
    have := sub_prefix [] (encodeCompressed compress d f) R
    simpa [hplen] using this
  have hb : ∀ x ∈ encodeCompressed compress d f ++ R, x < 256 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hreg.right_lt x h
    · exact hR x h
  rw [decodeCompressed_eq decompress d _ 0 hd1 hd (by simp [hplen]) hb, hsub]
  have hspec := Spec.byteDecode_regroup (d := d) hd (B := encodeCompressed compress d f) hplen
    hreg.right_lt
  rw [Regroup.left_unique hd1 hspec hreg, List.map_map]
  rfl

/-! ## Messages (`d = 1`) -/

/-- `encode_message f = ByteEncode_1(Compress_1(f))`. -/
theorem encodeMessage_eq (compress : ℕ → ℕ → ℕ) (f : List ℕ) (hf : f.length = 256)
    (hc : ∀ x, compress x 1 < 2) :
    encodeMessage compress f = Spec.byteEncode 1 (f.map (fun x => compress x 1)) :=
  encodeCompressed_eq compress 1 f hf (by norm_num) (by simpa using hc)

/-- `decode_message m = Decompress_1(ByteDecode_1(m))` for a 32-byte message. -/
theorem decodeMessage_eq (decompress : ℕ → ℕ → ℕ) (m : List ℕ) (hm : m.length = 32)
    (hb : ∀ x ∈ m, x < 256) :
    decodeMessage decompress m = (Spec.byteDecode 1 m).map (fun c => decompress c 1) := by
  unfold decodeMessage
  rw [decodeCompressed_eq decompress 1 m 0 le_rfl (by norm_num) (by rw [hm]) hb]
  congr 2
  unfold sub
  rw [List.drop_zero, List.take_of_length_le (by rw [hm])]

end OcamlPq.Encoding.Mlkem
