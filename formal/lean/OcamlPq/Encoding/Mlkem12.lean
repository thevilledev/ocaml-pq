import OcamlPq.Encoding.Packer
import OcamlPq.Encoding.Bytes

/-!
# ML-KEM `encode_12` / `decode_12`

Models of `encode_12` and `decode_12` (`lib/mlkem_engine.ml` lines 230–253),
which pack two 12-bit coefficients into three bytes at a time.

Results:

* `encode12_eq_byteEncode`: `encode_12 f = ByteEncode_12(f)` for every
  polynomial with coefficients below `2 ^ 12` (in particular every canonical
  one, coefficients below `q`), whatever the uninitialised `Bytes.create`
  buffer contained.
* `decode12_eq_some_iff`, `decode12_eq_none_iff`: `decode_12` returns `Ok`
  exactly when the FIPS 203 §7.2 modulus check
  `ByteEncode_12(ByteDecode_12(B)) = B` passes, and then returns
  `ByteDecode_12(B)`; `decode12_eq_raw` states the same with the code's own
  test "every 12-bit value is below `q`", and `modulus_check_iff` proves the two
  tests equivalent.
* `decode12_encode12`: `decode_12 (encode_12 f) = Ok f` for canonical `f`.
* `encode12_values_lt`, `decode12_values_lt`: the intermediate `x` is below
  `2 ^ 24`, hence `Portable`.
-/

namespace OcamlPq.Encoding.Mlkem

open Nat (ofDigits)
open OcamlPq.Encoding
open OcamlPq.Encoding.Packer (or_shiftLeft_eq_add and_ff_eq shiftRight_eight)

/-- The ML-KEM modulus. -/
def q : ℕ := 3329

theorem q_eq : q = Spec.q := rfl

/-! ## `encode_12` -/

/-- The loop body of `encode_12` (`lib/mlkem_engine.ml` lines 233–238):
```
let a = Array.unsafe_get f (2 * i) in
let b = Array.unsafe_get f ((2 * i) + 1) in
let x = a lor (b lsl 12) in
set_u8 out (3 * i) x;
set_u8 out ((3 * i) + 1) (x lsr 8);
set_u8 out ((3 * i) + 2) (x lsr 16)
```
where `set_u8 b i x` stores `x land 0xff` (line 103). -/
def encode12Body (f : List ℕ) (out : List ℕ) (i : ℕ) : List ℕ :=
  let a := f.getD (2 * i) 0
  let b := f.getD (2 * i + 1) 0
  let x := a ||| (b <<< 12)
  ((out.set (3 * i) (x &&& 0xff)).set (3 * i + 1) ((x >>> 8) &&& 0xff)).set (3 * i + 2)
    ((x >>> 16) &&& 0xff)

/-- `encode_12 f` (`lib/mlkem_engine.ml` lines 230–240). `init` is the
uninitialised buffer returned by `Bytes.create encoding_size_12`. -/
def encode12 (init : List ℕ) (f : List ℕ) : List ℕ :=
  (List.range 128).foldl (encode12Body f) init

theorem three_bytes (x : ℕ) (hx : x < 2 ^ 24) :
    ofDigits 256 [x % 256, x / 256 % 256, x / 65536 % 256] = x := by
  simp [Nat.ofDigits_cons]; omega

theorem ofDigits_4096_pair (g : ℕ → ℕ) (t : ℕ) :
    ofDigits 4096 ((List.range (2 * t + 2)).map g) =
      ofDigits 4096 ((List.range (2 * t)).map g) + 256 ^ (3 * t) * (g (2 * t) + 4096 * g (2 * t + 1)) := by
  rw [show 2 * t + 2 = (2 * t + 1) + 1 by ring, List.range_succ, List.range_succ, List.map_append,
    List.map_append, List.map_singleton, List.map_singleton, List.append_assoc, Nat.ofDigits_append]
  simp only [List.length_map, List.length_range, List.singleton_append, Nat.ofDigits_cons,
    Nat.ofDigits_nil]
  rw [show (4096 : ℕ) ^ (2 * t) = 256 ^ (3 * t) by
    rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul,
      ← pow_mul]; ring_nf]
  ring

/-- The loop body of `encode_12` in arithmetic form. -/
theorem encode12Body_eq (f out : List ℕ) (i : ℕ) (ha : f.getD (2 * i) 0 < 2 ^ 12) :
    encode12Body f out i =
      ((out.set (3 * i) ((f.getD (2 * i) 0 + 4096 * f.getD (2 * i + 1) 0) % 256)).set (3 * i + 1)
        ((f.getD (2 * i) 0 + 4096 * f.getD (2 * i + 1) 0) / 256 % 256)).set (3 * i + 2)
        ((f.getD (2 * i) 0 + 4096 * f.getD (2 * i + 1) 0) / 65536 % 256) := by
  unfold encode12Body
  simp only [or_shiftLeft_eq_add ha, and_ff_eq, Nat.shiftRight_eq_div_pow]
  norm_num
  ring_nf

/-- The state of `encode_12` after `t` iterations. -/
theorem encode12_loop {f init : List ℕ} (hf : ∀ x ∈ f, x < 2 ^ 12) (hinit : init.length = 384)
    (t : ℕ) (ht : t ≤ 128) :
    ∃ E, E.length = 3 * t ∧
      (List.range t).foldl (encode12Body f) init = E ++ init.drop (3 * t) ∧
      (∀ x ∈ E, x < 256) ∧
      ofDigits 256 E = ofDigits 4096 ((List.range (2 * t)).map (fun i => f.getD i 0)) := by
  induction t with
  | zero => exact ⟨[], rfl, by simp, by simp, by simp⟩
  | succ t ih =>
    obtain ⟨E, hE, hout, hlt, hval⟩ := ih (by omega)
    have hget := getD_lt_of_all (by norm_num) hf
    have ha := hget (2 * t)
    have hb := hget (2 * t + 1)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hout,
      encode12Body_eq _ _ _ ha]
    generalize hag : f.getD (2 * t) 0 = a at ha ⊢
    generalize hbg : f.getD (2 * t + 1) 0 = b at hb
    have hx24 : a + 4096 * b < 2 ^ 24 := by omega
    generalize hxg : a + 4096 * b = x at hx24
    refine ⟨E ++ [x % 256, x / 256 % 256, x / 65536 % 256], by simp [hE]; ring, ?_, ?_, ?_⟩
    · have h1 := set_after_prefix E init (x % 256) (by omega)
      rw [hE] at h1
      rw [h1]
      have h2 := set_after_prefix (E ++ [x % 256]) init (x / 256 % 256) (by simp; omega)
      simp only [List.length_append, List.length_singleton, hE] at h2
      rw [h2]
      have h3 := set_after_prefix (E ++ [x % 256] ++ [x / 256 % 256]) init (x / 65536 % 256)
        (by simp; omega)
      simp only [List.length_append, List.length_singleton, hE] at h3
      rw [h3]
      simp only [List.append_assoc, List.cons_append, List.nil_append,
        show 3 * t + 1 + 1 + 1 = 3 * (t + 1) by ring]
    · intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with h | h | h | h
      · exact hlt y h
      all_goals (subst h; exact Nat.mod_lt _ (by norm_num))
    · rw [Nat.ofDigits_append, hval, three_bytes _ hx24, show 2 * (t + 1) = 2 * t + 2 by ring,
        ofDigits_4096_pair, hE, hbg, hag, ← hxg]

/-- `encode_12 f` is the 12-bit regrouping of `f`. -/
theorem encode12_regroup {f init : List ℕ} (hflen : f.length = 256) (hf : ∀ x ∈ f, x < 2 ^ 12)
    (hinit : init.length = 384) : Regroup 12 8 f (encode12 init f) := by
  obtain ⟨E, hE, hout, hlt, hval⟩ := encode12_loop hf hinit 128 le_rfl
  have : encode12 init f = E := by
    rw [encode12, hout, show 3 * 128 = init.length by omega, List.drop_length, List.append_nil]
  rw [this]
  refine ⟨by rw [hflen, hE], hf, by simpa using hlt, ?_⟩
  rw [show (2 : ℕ) ^ 12 = 4096 by norm_num, show (2 : ℕ) ^ 8 = 256 by norm_num, hval,
    show 2 * 128 = f.length by omega, map_getD_range]

/-- **`encode_12 = ByteEncode_12`** on polynomials with 12-bit coefficients. -/
theorem encode12_eq_byteEncode {f init : List ℕ} (hflen : f.length = 256)
    (hf : ∀ x ∈ f, x < 2 ^ 12) (hinit : init.length = 384) :
    encode12 init f = Spec.byteEncode 12 f :=
  Regroup.right_unique (by norm_num) (encode12_regroup hflen hf hinit)
    (Spec.byteEncode_regroup hflen hf)

theorem length_encode12 {f init : List ℕ} (hinit : init.length = 384) :
    (encode12 init f).length = 384 := by
  have : ∀ t (out : List ℕ), ((List.range t).foldl (encode12Body f) out).length = out.length := by
    intro t
    induction t with
    | zero => intro out; rfl
    | succ t ih => intro out; rw [List.range_succ, List.foldl_append]; simp [encode12Body, ih]
  rw [encode12, this, hinit]

/-- The intermediate `x = a lor (b lsl 12)` of `encode_12` is below `2 ^ 24`
(so `Portable`). -/
theorem encode12_values_lt {f : List ℕ} (hf : ∀ x ∈ f, x < 2 ^ 12) (i : ℕ) :
    f.getD (2 * i) 0 ||| (f.getD (2 * i + 1) 0 <<< 12) < 2 ^ 24 := by
  have hget : ∀ i, f.getD i 0 < 2 ^ 12 := by
    intro i
    by_cases h : i < f.length
    · rw [List.getD_eq_getElem _ _ h]; exact hf _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)]; norm_num
  have := Nat.shiftLeft_lt (m := 12) (hget (2 * i + 1))
  exact Nat.or_lt_two_pow (lt_trans (hget _) (by norm_num)) (by simpa using this)

/-! ## `decode_12` -/

/-- The loop body of `decode_12` (`lib/mlkem_engine.ml` lines 246–251):
```
let p = off + (3 * i) in
let x = get_u8 s p lor (get_u8 s (p + 1) lsl 8) lor (get_u8 s (p + 2) lsl 16) in
let a = x land 0xfff and b = x lsr 12 in
valid := !valid && a < q && b < q;
Array.unsafe_set out (2 * i) a;
Array.unsafe_set out ((2 * i) + 1) b
``` -/
def decode12Body (s : List ℕ) (off : ℕ) (st : List ℕ × Bool) (i : ℕ) : List ℕ × Bool :=
  let p := off + 3 * i
  let x := s.getD p 0 ||| (s.getD (p + 1) 0 <<< 8) ||| (s.getD (p + 2) 0 <<< 16)
  let a := x &&& 0xfff
  let b := x >>> 12
  ((st.1.set (2 * i) a).set (2 * i + 1) b, st.2 && decide (a < q) && decide (b < q))

/-- `decode_12 ~what s off` (`lib/mlkem_engine.ml` lines 242–253); `none` is
the `Error (Invalid_encoding _)` result. -/
def decode12 (s : List ℕ) (off : ℕ) : Option (List ℕ) :=
  let st := (List.range 128).foldl (decode12Body s off) (List.replicate 256 0, true)
  if st.2 then some st.1 else none

theorem three_bytes_or (b0 b1 b2 : ℕ) (h0 : b0 < 256) (h1 : b1 < 256) :
    b0 ||| (b1 <<< 8) ||| (b2 <<< 16) = b0 + 256 * b1 + 65536 * b2 := by
  rw [or_shiftLeft_eq_add (show b0 < 2 ^ 8 by simpa using h0)]
  rw [or_shiftLeft_eq_add (show b0 + b1 * 2 ^ 8 < 2 ^ 16 by omega)]
  ring

/-- The loop body of `decode_12` in arithmetic form. -/
theorem decode12Body_eq (s : List ℕ) (off : ℕ) (st : List ℕ × Bool) (i : ℕ)
    (h0 : s.getD (off + 3 * i) 0 < 256) (h1 : s.getD (off + 3 * i + 1) 0 < 256) :
    decode12Body s off st i =
      let x := s.getD (off + 3 * i) 0 + 256 * s.getD (off + 3 * i + 1) 0 +
        65536 * s.getD (off + 3 * i + 2) 0
      ((st.1.set (2 * i) (x % 4096)).set (2 * i + 1) (x / 4096),
        st.2 && decide (x % 4096 < q) && decide (x / 4096 < q)) := by
  unfold decode12Body
  simp only [three_bytes_or _ _ _ h0 h1]
  have hmask : ∀ x : ℕ, x &&& 0xfff = x % 4096 := by
    intro x; have := Nat.and_two_pow_sub_one_eq_mod x 12; simpa using this
  simp only [hmask, Nat.shiftRight_eq_div_pow]

theorem decide_all_append_pair (V : List ℕ) (a b : ℕ) :
    (decide (∀ v ∈ V, v < q) && decide (a < q) && decide (b < q)) =
      decide (∀ v ∈ V ++ [a, b], v < q) := by
  rw [Bool.and_assoc]
  simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, Bool.decide_and]

/-- The state of `decode_12` after `t` iterations. -/
theorem decode12_loop {s : List ℕ} {off : ℕ} (hs : ∀ x ∈ s, x < 256) (t : ℕ) (ht : t ≤ 128) :
    ∃ V, V.length = 2 * t ∧
      (List.range t).foldl (decode12Body s off) (List.replicate 256 0, true) =
        (V ++ (List.replicate 256 0).drop (2 * t), decide (∀ v ∈ V, v < q)) ∧
      (∀ x ∈ V, x < 2 ^ 12) ∧
      ofDigits 4096 V = ofDigits 256 (Packer.slice s off (3 * t)) := by
  induction t with
  | zero =>
    refine ⟨[], rfl, ?_, by simp, by simp [Packer.slice]⟩
    simp only [List.range_zero, List.foldl_nil, List.nil_append, Nat.mul_zero, List.drop_zero,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, decide_true]
  | succ t ih =>
    obtain ⟨V, hV, hst, hlt, hval⟩ := ih (by omega)
    have hget := getD_lt_of_all (by norm_num) hs
    have h0 := hget (off + 3 * t)
    have h1 := hget (off + 3 * t + 1)
    have h2 := hget (off + 3 * t + 2)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hst,
      decode12Body_eq _ _ _ _ h0 h1]
    simp only
    rw [decide_all_append_pair]
    have hsl : Packer.slice s off (3 * (t + 1)) = Packer.slice s off (3 * t) ++
        [s.getD (off + 3 * t) 0, s.getD (off + 3 * t + 1) 0, s.getD (off + 3 * t + 2) 0] := by
      rw [show 3 * (t + 1) = 3 * t + 1 + 1 + 1 by ring, Packer.slice_succ, Packer.slice_succ,
        Packer.slice_succ]
      simp only [List.append_assoc, List.singleton_append]
      congr 3
    rw [hsl]
    have hslen : (Packer.slice s off (3 * t)).length = 3 * t := by simp [Packer.slice]
    generalize s.getD (off + 3 * t) 0 = b0 at h0 ⊢
    generalize s.getD (off + 3 * t + 1) 0 = b1 at h1 ⊢
    generalize s.getD (off + 3 * t + 2) 0 = b2 at h2 ⊢
    have hx24 : b0 + 256 * b1 + 65536 * b2 < 2 ^ 24 := by omega
    have hvalx : ofDigits 256 [b0, b1, b2] = b0 + 256 * b1 + 65536 * b2 := by
      simp [Nat.ofDigits_cons]; ring
    generalize hxg : b0 + 256 * b1 + 65536 * b2 = x at hx24 hvalx
    refine ⟨V ++ [x % 4096, x / 4096], ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil, hV]; ring
    · have hr : (List.replicate 256 0).length = 256 := List.length_replicate
      have e1 := set_after_prefix V (List.replicate 256 0) (x % 4096) (by rw [hV, hr]; omega)
      rw [hV] at e1
      rw [e1]
      have e2 := set_after_prefix (V ++ [x % 4096]) (List.replicate 256 0) (x / 4096)
        (by simp only [List.length_append, List.length_singleton, hV, hr]; omega)
      simp only [List.length_append, List.length_singleton, hV] at e2
      rw [e2]
      simp only [List.append_assoc, List.cons_append, List.nil_append,
        show 2 * t + 1 + 1 = 2 * (t + 1) by ring]
    · intro v hv'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv'
      rcases hv' with h | h | h
      · exact hlt v h
      · subst h; exact Nat.mod_lt _ (by norm_num)
      · subst h; show x / 4096 < 4096; omega
    · rw [Nat.ofDigits_append, Nat.ofDigits_append, hval, hslen, hV, hvalx]
      rw [show (4096 : ℕ) ^ (2 * t) = 256 ^ (3 * t) by
        rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul,
          ← pow_mul]; ring_nf]
      simp [Nat.ofDigits_cons]
      omega

/-- The unreduced 12-bit values that `decode_12 s off` reads. -/
theorem decode12_raw {s : List ℕ} {off : ℕ} (hs : ∀ x ∈ s, x < 256) :
    ∃ V, V = Spec.byteDecodeRaw 12 (Packer.slice s off 384) ∧
      decode12 s off = if ∀ v ∈ V, v < q then some V else none := by
  obtain ⟨V, hV, hst, hlt, hval⟩ := decode12_loop (s := s) (off := off) hs 128 le_rfl
  have hreg : Regroup 12 8 V (Packer.slice s off 384) :=
    ⟨by rw [hV]; simp [Packer.slice], hlt, Packer.slice_lt hs off 384, by simpa using hval⟩
  have hraw := Spec.byteDecodeRaw_regroup (d := 12) (B := Packer.slice s off 384)
    (by simp [Packer.slice]) (Packer.slice_lt hs off 384)
  have hVeq : V = Spec.byteDecodeRaw 12 (Packer.slice s off 384) :=
    Regroup.left_unique (by norm_num) hreg hraw
  refine ⟨V, hVeq, ?_⟩
  unfold decode12
  simp only [hst, show 2 * 128 = 256 by rfl, List.drop_replicate, Nat.sub_self,
    List.replicate_zero, List.append_nil]
  by_cases h : ∀ v ∈ V, v < q <;> simp [h]

/-- `decode_12` returns `Ok` exactly when every 12-bit value is below `q`,
and then returns those values. -/
theorem decode12_eq_raw {s : List ℕ} {off : ℕ} (hs : ∀ x ∈ s, x < 256) :
    decode12 s off =
      if ∀ v ∈ Spec.byteDecodeRaw 12 (Packer.slice s off 384), v < q
      then some (Spec.byteDecodeRaw 12 (Packer.slice s off 384)) else none := by
  obtain ⟨V, rfl, h⟩ := decode12_raw (s := s) (off := off) hs
  exact h

/-- **The FIPS 203 §7.2 modulus check.** For a 384-byte string `B`,
`ByteEncode_12(ByteDecode_12(B)) = B` iff every unreduced 12-bit value of `B`
is below `q`. -/
theorem modulus_check_iff {B : List ℕ} (hB : B.length = 384) (hb : ∀ x ∈ B, x < 256) :
    Spec.byteEncode 12 (Spec.byteDecode 12 B) = B ↔ ∀ v ∈ Spec.byteDecodeRaw 12 B, v < q := by
  have hraw := Spec.byteDecodeRaw_regroup (d := 12) (B := B) (by rw [hB]) hb
  have hlen : (Spec.byteDecodeRaw 12 B).length = 256 := by simp [Spec.byteDecodeRaw]
  have hdec := Spec.byteDecode_eq_map 12 B
  have hmod : Spec.byteDecodeModulus 12 = q := rfl
  rw [hmod] at hdec
  constructor
  · intro h
    have hD : ∀ x ∈ Spec.byteDecode 12 B, x < 2 ^ 12 := by
      intro x hx
      rw [hdec] at hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    have hDlen : (Spec.byteDecode 12 B).length = 256 := by rw [hdec]; simp [hlen]
    have h1 := Spec.byteEncode_regroup hDlen hD
    rw [h] at h1
    have heq : Spec.byteDecode 12 B = Spec.byteDecodeRaw 12 B := Regroup.left_unique (by norm_num) h1 hraw
    intro v hv
    have : v % q ∈ Spec.byteDecode 12 B := by rw [hdec]; exact List.mem_map_of_mem hv
    rw [heq] at this
    -- `v % q` and `v` are both in the list; compare positions
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have e : (Spec.byteDecode 12 B)[i]'(by rw [hDlen]; rw [hlen] at hi; exact hi) =
        (Spec.byteDecodeRaw 12 B)[i] := by simp only [heq]
    rw [List.getElem_of_eq hdec] at e
    simp only [List.getElem_map] at e
    rw [← e]; exact Nat.mod_lt _ (by decide)
  · intro h
    have heq : Spec.byteDecode 12 B = Spec.byteDecodeRaw 12 B := by
      rw [hdec]
      conv_rhs => rw [← List.map_id (Spec.byteDecodeRaw 12 B)]
      exact List.map_congr_left (fun v hv => Nat.mod_eq_of_lt (h v hv))
    rw [heq]
    have hraw' : ∀ x ∈ Spec.byteDecodeRaw 12 B, x < 2 ^ 12 := hraw.left_lt
    exact Regroup.right_unique (by norm_num) (Spec.byteEncode_regroup hlen hraw') hraw

/-- **`decode_12` is `ByteDecode_12` guarded by the FIPS 203 modulus check.**
For `off + 384 ≤ |s|` (checked by every caller), with `B` the 384 bytes at
`off`: `decode_12` returns `Ok F` iff `ByteEncode_12(ByteDecode_12(B)) = B`
and `F = ByteDecode_12(B)`. -/
theorem decode12_eq_some_iff {s : List ℕ} {off : ℕ} (hs : ∀ x ∈ s, x < 256)
    (hoff : off + 384 ≤ s.length) (F : List ℕ) :
    decode12 s off = some F ↔
      Spec.byteEncode 12 (Spec.byteDecode 12 (sub s off 384)) = sub s off 384 ∧
      F = Spec.byteDecode 12 (sub s off 384) := by
  have hsl : Packer.slice s off 384 = sub s off 384 := Packer.slice_eq_take_drop s off 384 hoff
  rw [decode12_eq_raw hs, hsl]
  have hB : (sub s off 384).length = 384 := length_sub s off 384 hoff
  have hiff := modulus_check_iff hB (sub_lt hs off 384)
  rw [hiff]
  by_cases h : ∀ v ∈ Spec.byteDecodeRaw 12 (sub s off 384), v < q
  · have hdec : Spec.byteDecode 12 (sub s off 384) = Spec.byteDecodeRaw 12 (sub s off 384) := by
      rw [Spec.byteDecode_eq_map]
      conv_rhs => rw [← List.map_id (Spec.byteDecodeRaw 12 (sub s off 384))]
      exact List.map_congr_left (fun v hv => Nat.mod_eq_of_lt (h v hv))
    rw [ite_eq_left h, hdec]
    constructor
    · intro hF; exact ⟨h, (Option.some.inj hF).symm⟩
    · rintro ⟨-, rfl⟩; rfl
  · rw [ite_eq_right h]
    constructor
    · intro hF; cases hF
    · rintro ⟨h', -⟩; exact absurd h' h

/-- `decode_12` returns `Error` iff the FIPS 203 modulus check fails. -/
theorem decode12_eq_none_iff {s : List ℕ} {off : ℕ} (hs : ∀ x ∈ s, x < 256)
    (hoff : off + 384 ≤ s.length) :
    decode12 s off = none ↔
      Spec.byteEncode 12 (Spec.byteDecode 12 (sub s off 384)) ≠ sub s off 384 := by
  constructor
  · intro hn heq
    have := (decode12_eq_some_iff hs hoff (Spec.byteDecode 12 (sub s off 384))).mpr ⟨heq, rfl⟩
    rw [hn] at this; cases this
  · intro hne
    cases hd : decode12 s off with
    | none => rfl
    | some F => exact absurd ((decode12_eq_some_iff hs hoff F).mp hd).1 hne

/-- **Round trip.** `decode_12 (encode_12 f) 0 = Ok f` for every canonical
polynomial (coefficients below `q`). -/
theorem decode12_encode12 {f init : List ℕ} (hflen : f.length = 256) (hf : ∀ x ∈ f, x < q)
    (hinit : init.length = 384) : decode12 (encode12 init f) 0 = some f := by
  have hf12 : ∀ x ∈ f, x < 2 ^ 12 := fun x hx => lt_trans (hf x hx) (by decide)
  have hreg := encode12_regroup hflen hf12 hinit
  have hlen : (encode12 init f).length = 384 := length_encode12 hinit
  have hsl : Packer.slice (encode12 init f) 0 384 = encode12 init f := by
    rw [← hlen]; exact Packer.slice_zero_length _
  have hraw := Spec.byteDecodeRaw_regroup (d := 12) (B := encode12 init f) hlen hreg.right_lt
  have heq : Spec.byteDecodeRaw 12 (encode12 init f) = f :=
    Regroup.left_unique (by norm_num) hraw hreg
  rw [decode12_eq_raw hreg.right_lt, hsl, heq, ite_eq_left hf]

/-- The intermediate `x` of `decode_12` is below `2 ^ 24` (so `Portable`), and
every byte read lies in `[off, off + 384)`. -/
theorem decode12_values_lt {s : List ℕ} (hs : ∀ x ∈ s, x < 256) (p : ℕ) :
    s.getD p 0 ||| (s.getD (p + 1) 0 <<< 8) ||| (s.getD (p + 2) 0 <<< 16) < 2 ^ 24 := by
  have hget : ∀ i, s.getD i 0 < 256 := by
    intro i
    by_cases h : i < s.length
    · rw [List.getD_eq_getElem _ _ h]; exact hs _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)]; norm_num
  rw [three_bytes_or _ _ _ (hget p) (hget (p + 1))]
  have := hget p; have := hget (p + 1); have := hget (p + 2)
  omega

theorem decode12_reads_in_bounds {s : List ℕ} {off : ℕ} (hoff : off + 384 ≤ s.length)
    (i : ℕ) (hi : i < 128) (k : ℕ) (hk : k < 3) : off + 3 * i + k < s.length := by omega

end OcamlPq.Encoding.Mlkem
