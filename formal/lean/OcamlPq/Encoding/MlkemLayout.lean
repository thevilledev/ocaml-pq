import OcamlPq.Encoding.Mlkem12
import OcamlPq.Encoding.MlkemCompressed

/-!
# ML-KEM key and ciphertext layouts

Models of the byte layouts in `lib/mlkem_engine.ml`:

* `encode_ek` / `parse_ek` (lines 338–361): `ek = ByteEncode_12(t̂) ‖ ρ`
  (FIPS 203 Algorithm 13, line 19) and the §7.2 encapsulation-key check;
* `decapsulation_key_to_expanded` / `decapsulation_key_of_expanded`
  (lines 401–443): `dk = ByteEncode_12(ŝ) ‖ ek ‖ H(ek) ‖ z` (Algorithm 16);
* the ciphertext layout of `pke_encrypt` / `pke_decrypt` (lines 453–506):
  `c = ByteEncode_du(Compress_du(u)) ‖ ByteEncode_dv(Compress_dv(v))`
  (Algorithms 14 and 15).

`encode_12`'s scratch buffer is taken to be zeros: by
`encode12_eq_byteEncode` its content does not matter.

**Deviation from FIPS 203 (stricter).** `decapsulation_key_of_expanded` runs
`decode_12` on the `ŝ` part and `parse_ek` on the embedded `ek`, so it rejects
expanded keys whose `ŝ` or `t̂` contain unreduced 12-bit values. FIPS 203 §7.3
only requires the length check and the hash check `H(ek) = h` for `dk`.
Honestly generated keys always pass, so this only rejects keys that no
conforming key generator produces.
-/

namespace OcamlPq.Encoding.Mlkem

open Nat (ofDigits)
open OcamlPq.Encoding

/-! ## Sizes -/

/-- `encapsulation_key_size = k * encoding_size_12 + 32`. -/
def ekSize (k : ℕ) : ℕ := k * 384 + 32

/-- `expanded_decapsulation_key_size = k * encoding_size_12 + encapsulation_key_size + 64`. -/
def dkSize (k : ℕ) : ℕ := k * 384 + ekSize k + 64

/-- `ciphertext_size = k * encoding_size_u + encoding_size_v`, with
`encoding_size_d = n * d / 8`. -/
def ctSize (k du dv : ℕ) : ℕ := k * (256 * du / 8) + 256 * dv / 8

/-- Sizes for ML-KEM-512, -768, -1024 (`Mlkem512`, `Mlkem768`, `Mlkem1024`,
lines 527–549): FIPS 203 Table 3. -/
theorem sizes :
    (ekSize 2, dkSize 2, ctSize 2 10 4) = (800, 1632, 768) ∧
    (ekSize 3, dkSize 3, ctSize 3 10 4) = (1184, 2400, 1088) ∧
    (ekSize 4, dkSize 4, ctSize 4 11 5) = (1568, 3168, 1568) := by
  decide

/-! ## Writing blocks with `Bytes.blit_string` -/

/-- Blitting equal-length blocks at offsets `i * len` into a buffer. -/
theorem blit_blocks (blocks : List (List ℕ)) (len : ℕ) (hlen : ∀ b ∈ blocks, b.length = len)
    (init : List ℕ) (m : ℕ) (hm : m ≤ blocks.length) :
    (List.range m).foldl (fun out i => blit (blocks.getD i []) 0 out (i * len) len) init =
      (blocks.take m).flatten ++ init.drop (m * len) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
    have hb : blocks.getD m [] = blocks[m] := List.getD_eq_getElem _ _ (by omega)
    have hbl : blocks[m].length = len := hlen _ (List.getElem_mem _)
    have htl : ((blocks.take m).flatten).length = m * len := by
      rw [length_flatten_blocks _ len (fun b hb => hlen b (List.mem_of_mem_take hb))]
      simp; omega
    rw [hb, ← htl, ← hbl, blit_after_prefix, htl, hbl, List.drop_drop,
      List.take_succ_eq_append_getElem (by omega), List.flatten_append]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
    congr 2
    ring_nf

/-! ## `encode_ek` / `parse_ek` -/

/-- `encode_ek t rho` (lines 338–344). `init` is the `Bytes.create`
buffer of `encode_ek` and `scratch` the one of each `encode_12` call (their
contents do not matter, see `encodeEk_eq`). -/
def encodeEk (k : ℕ) (scratch init : List ℕ) (t : List (List ℕ)) (rho : List ℕ) : List ℕ :=
  let out := (List.range k).foldl
    (fun out i => blit (encode12 scratch (t.getD i [])) 0 out (i * 384) 384) init
  blit rho 0 out (k * 384) 32

/-- A canonical polynomial: 256 coefficients below `q`. -/
def Canonical (f : List ℕ) : Prop := f.length = 256 ∧ ∀ x ∈ f, x < q

/-- Writing `encode_12` of each polynomial at offset `i * 384`. -/
theorem blit_encode12_blocks (k : ℕ) (scratch init : List ℕ) (t : List (List ℕ))
    (ht : t.length = k) (hcan : ∀ f ∈ t, Canonical f) (hscratch : scratch.length = 384) :
    (List.range k).foldl
      (fun out i => blit (encode12 scratch (t.getD i [])) 0 out (i * 384) 384) init =
      (t.map (Spec.byteEncode 12)).flatten ++ init.drop (k * 384) := by
  have hq : ∀ f ∈ t, ∀ x ∈ f, x < 2 ^ 12 :=
    fun f hf x hx => lt_trans ((hcan f hf).2 x hx) (by decide)
  have hblocks : ∀ b ∈ t.map (Spec.byteEncode 12), b.length = 384 := by
    intro b hb
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
    exact Spec.length_byteEncode (hcan f hf).1 (hq f hf)
  have hfold : (List.range k).foldl
      (fun out i => blit (encode12 scratch (t.getD i [])) 0 out (i * 384) 384) init =
      (List.range k).foldl
      (fun out i => blit ((t.map (Spec.byteEncode 12)).getD i []) 0 out (i * 384) 384) init := by
    apply List.foldl_ext
    intro out i hi
    rw [List.mem_range] at hi
    have hi' : i < t.length := by omega
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ (by simpa using hi'),
      List.getElem_map, encode12_eq_byteEncode (hcan _ (List.getElem_mem hi')).1
        (hq _ (List.getElem_mem hi')) hscratch]
  rw [hfold, blit_blocks _ 384 hblocks init k (by simp [ht]),
    List.take_of_length_le (by simp [ht])]

theorem encodeEk_eq (k : ℕ) (scratch init : List ℕ) (t : List (List ℕ)) (rho : List ℕ)
    (ht : t.length = k) (hcan : ∀ f ∈ t, Canonical f) (hrho : rho.length = 32)
    (hscratch : scratch.length = 384) (hinit : init.length = ekSize k) :
    encodeEk k scratch init t rho = (t.map (Spec.byteEncode 12)).flatten ++ rho := by
  have hq : ∀ f ∈ t, ∀ x ∈ f, x < 2 ^ 12 :=
    fun f hf x hx => lt_trans ((hcan f hf).2 x hx) (by decide)
  have hblocks : ∀ b ∈ t.map (Spec.byteEncode 12), b.length = 384 := by
    intro b hb
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
    exact Spec.length_byteEncode (hcan f hf).1 (hq f hf)
  have hfl := length_flatten_blocks _ 384 hblocks
  simp only [List.length_map, ht] at hfl
  unfold encodeEk
  simp only
  rw [blit_encode12_blocks k scratch init t ht hcan hscratch, ← hfl, ← hrho, blit_after_prefix,
    List.drop_drop, List.drop_eq_nil_of_le (by rw [hinit, ekSize, hfl, hrho]), List.append_nil]

/-- The recursive loop `parse` of `parse_ek` (lines 350–355), for a block
decoder `dec` (`decode_12`):
```
let rec parse acc i =
  if i = k then Ok (Array.of_list (List.rev acc))
  else match decode_12 ~what:"encapsulation key" encoded (i * encoding_size_12) with
    | Error _ as e -> e
    | Ok p -> parse (p :: acc) (i + 1)
```
The loop starts at `i = 0 ≤ k`, so `i = k` is the same test as `¬ i < k`. -/
def parseLoopWith (dec : List ℕ → ℕ → Option (List ℕ)) (k : ℕ) (encoded : List ℕ)
    (acc : List (List ℕ)) (i : ℕ) : Option (List (List ℕ)) :=
  if i < k then
    match dec encoded (i * 384) with
    | none => none
    | some p => parseLoopWith dec k encoded (p :: acc) (i + 1)
  else some acc.reverse
termination_by k - i
decreasing_by omega

/-- `parse` / `parse_s` with `decode_12`. -/
def parseLoop (k : ℕ) (encoded : List ℕ) (acc : List (List ℕ)) (i : ℕ) : Option (List (List ℕ)) :=
  parseLoopWith decode12 k encoded acc i

theorem parseLoop_eq (k : ℕ) (encoded : List ℕ) :
    ∀ n i (acc : List (List ℕ)), k - i = n →
      parseLoopWith decode12 k encoded acc i =
        if ∀ j, i ≤ j → j < k → (decode12 encoded (j * 384)).isSome
        then some (acc.reverse ++ (List.range' i (k - i)).map
          (fun j => (decode12 encoded (j * 384)).getD []))
        else none := by
  intro n
  induction n with
  | zero =>
    intro i acc hn
    rw [parseLoopWith, ite_eq_right (by omega), ite_eq_left (fun j h1 h2 => absurd h2 (by omega))]
    simp [show k - i = 0 by omega]
  | succ n ih =>
    intro i acc hn
    rw [parseLoopWith, ite_eq_left (by omega)]
    cases hd : decode12 encoded (i * 384) with
    | none =>
      simp only
      rw [ite_eq_right]
      intro h
      have := h i le_rfl (by omega)
      rw [hd] at this; simp at this
    | some p =>
      simp only
      rw [ih (i + 1) (p :: acc) (by omega)]
      by_cases hall : ∀ j, i + 1 ≤ j → j < k → (decode12 encoded (j * 384)).isSome
      · have hall' : ∀ j, i ≤ j → j < k → (decode12 encoded (j * 384)).isSome := by
          intro j h1 h2
          rcases Nat.eq_or_lt_of_le h1 with h | h
          · subst h; rw [hd]; rfl
          · exact hall j h h2
        rw [ite_eq_left hall, ite_eq_left hall']
        apply congrArg some
        rw [show k - i = (k - (i + 1)) + 1 by omega, List.range'_succ, List.map_cons, hd]
        simp
      · have hall' : ¬ ∀ j, i ≤ j → j < k → (decode12 encoded (j * 384)).isSome :=
          fun h => hall (fun j h1 h2 => h j (by omega) h2)
        rw [ite_eq_right hall, ite_eq_right hall']

/-- `parse_ek encoded` (lines 346–361), keeping the byte-level outputs `t̂`
and `ρ` (the matrix `Â` and `H(ek)` are computed from them). -/
def parseEk (k : ℕ) (encoded : List ℕ) : Option (List (List ℕ) × List ℕ) :=
  if encoded.length ≠ ekSize k then none
  else match parseLoop k encoded [] 0 with
    | none => none
    | some t => some (t, sub encoded (k * 384) 32)

/-- **`parse_ek` is FIPS 203 §7.2 input checking.** On a string of the right
length, `parse_ek` succeeds iff every 384-byte block passes the modulus check
`ByteEncode_12(ByteDecode_12(B)) = B` (equivalently, the check on the whole
`ek[0 : 384k]`, since `ByteEncode_12`/`ByteDecode_12` act blockwise), and then
returns `ByteDecode_12` of the blocks and `ρ = ek[384k : 384k + 32]`. -/
theorem parseEk_eq {k : ℕ} {encoded : List ℕ} (hb : ∀ x ∈ encoded, x < 256)
    (hlen : encoded.length = ekSize k) :
    parseEk k encoded =
      if ∀ j < k, Spec.byteEncode 12 (Spec.byteDecode 12 (sub encoded (j * 384) 384)) =
          sub encoded (j * 384) 384
      then some ((List.range k).map (fun j => Spec.byteDecode 12 (sub encoded (j * 384) 384)),
        sub encoded (k * 384) 32)
      else none := by
  unfold parseEk parseLoop
  rw [ite_eq_right (by simp [hlen]), parseLoop_eq k encoded _ 0 [] rfl]
  have hoff : ∀ j < k, j * 384 + 384 ≤ encoded.length := by
    intro j hj; rw [hlen, ekSize]; nlinarith
  have hiff : (∀ j, 0 ≤ j → j < k → (decode12 encoded (j * 384)).isSome) ↔
      ∀ j < k, Spec.byteEncode 12 (Spec.byteDecode 12 (sub encoded (j * 384) 384)) =
        sub encoded (j * 384) 384 := by
    constructor
    · intro h j hj
      have := h j (by omega) hj
      cases hd : decode12 encoded (j * 384) with
      | none => rw [hd] at this; simp at this
      | some F => exact ((decode12_eq_some_iff hb (hoff j hj) F).mp hd).1
    · intro h j _ hj
      rw [(decode12_eq_some_iff hb (hoff j hj) _).mpr ⟨h j hj, rfl⟩]; rfl
  by_cases hall : ∀ j < k, Spec.byteEncode 12 (Spec.byteDecode 12 (sub encoded (j * 384) 384)) =
      sub encoded (j * 384) 384
  · rw [ite_eq_left (hiff.mpr hall), ite_eq_left hall]
    simp only [List.reverse_nil, List.nil_append, Nat.sub_zero, List.range'_eq_map_range,
      zero_add, List.map_map, Option.some.injEq, Prod.mk.injEq, and_true]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    simp only [Function.comp_apply]
    rw [(decode12_eq_some_iff hb (hoff j hj) _).mpr ⟨hall j hj, rfl⟩]
    rfl
  · rw [ite_eq_right (fun h => hall (hiff.mp h)), ite_eq_right hall]

theorem length_encodeEk_blocks (t : List (List ℕ)) (hcan : ∀ f ∈ t, Canonical f) :
    ∀ b ∈ t.map (Spec.byteEncode 12), b.length = 384 := by
  intro b hb
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
  exact Spec.length_byteEncode (hcan f hf).1
    (fun x hx => lt_trans ((hcan f hf).2 x hx) (by decide))

theorem byteEncode12_lt {f : List ℕ} (hf : Canonical f) : ∀ x ∈ Spec.byteEncode 12 f, x < 256 :=
  (Spec.byteEncode_regroup hf.1 (fun x hx => lt_trans (hf.2 x hx) (by decide))).right_lt

theorem flatten_byteEncode12_lt {t : List (List ℕ)} (hcan : ∀ f ∈ t, Canonical f) :
    ∀ x ∈ (t.map (Spec.byteEncode 12)).flatten, x < 256 := by
  intro x h
  obtain ⟨b, hb, hxb⟩ := List.mem_flatten.mp h
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
  exact byteEncode12_lt (hcan f hf) x hxb

/-- `ByteDecode_12(ByteEncode_12(f)) = f` for canonical `f`. -/
theorem byteDecode_byteEncode_12 {f : List ℕ} (hf : Canonical f) :
    Spec.byteDecode 12 (Spec.byteEncode 12 f) = f := by
  have hq : ∀ x ∈ f, x < 2 ^ 12 := fun x hx => lt_trans (hf.2 x hx) (by decide)
  have h1 := Spec.byteEncode_regroup hf.1 hq
  have h2 := Spec.byteDecodeRaw_regroup (d := 12) (B := Spec.byteEncode 12 f)
    (by rw [Spec.length_byteEncode hf.1 hq]) h1.right_lt
  have hraw := Regroup.left_unique (by norm_num) h2 h1
  rw [Spec.byteDecode_eq_map, hraw]
  conv_rhs => rw [← List.map_id f]
  exact List.map_congr_left (fun x hx => Nat.mod_eq_of_lt (hf.2 x hx))

/-- `decode_12` of block `j` of a concatenation of `ByteEncode_12` blocks. -/
theorem decode12_flatten {t : List (List ℕ)} (hcan : ∀ f ∈ t, Canonical f) (R : List ℕ)
    (hR : ∀ x ∈ R, x < 256) (j : ℕ) (hj : j < t.length) :
    decode12 ((t.map (Spec.byteEncode 12)).flatten ++ R) (j * 384) = some t[j] := by
  have hbl := length_encodeEk_blocks t hcan
  have hfl := length_flatten_blocks _ 384 hbl
  simp only [List.length_map] at hfl
  have hb : ∀ x ∈ (t.map (Spec.byteEncode 12)).flatten ++ R, x < 256 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact flatten_byteEncode12_lt hcan x h
    · exact hR x h
  have hsub : sub ((t.map (Spec.byteEncode 12)).flatten ++ R) (j * 384) 384 =
      Spec.byteEncode 12 t[j] := by
    rw [sub_flatten_blocks _ 384 hbl R j (by simpa using hj)]
    simp
  have hmem : t[j] ∈ t := List.getElem_mem _
  rw [(decode12_eq_some_iff hb (by simp [hfl]; nlinarith) t[j]).mpr]
  rw [hsub, byteDecode_byteEncode_12 (hcan _ hmem)]
  exact ⟨rfl, rfl⟩

/-- `parse` (and `parse_s`) on a concatenation of `ByteEncode_12` blocks. -/
theorem parseLoop_flatten {k : ℕ} {t : List (List ℕ)} (ht : t.length = k)
    (hcan : ∀ f ∈ t, Canonical f) (R : List ℕ) (hR : ∀ x ∈ R, x < 256) :
    parseLoop k ((t.map (Spec.byteEncode 12)).flatten ++ R) [] 0 = some t := by
  unfold parseLoop
  rw [parseLoop_eq k _ _ 0 [] rfl]
  have hdec := decode12_flatten hcan R hR
  rw [ite_eq_left (fun j _ hj => by rw [hdec j (by omega)]; rfl)]
  simp only [List.reverse_nil, List.nil_append, Nat.sub_zero, Option.some.injEq]
  apply List.ext_getElem
  · simp [ht]
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range', zero_add, one_mul]
    rw [hdec j h2]; rfl

/-- **Round trip.** `parse_ek (encode_ek t ρ) = Ok (t, ρ)` for canonical `t̂`. -/
theorem parseEk_encodeEk (k : ℕ) (scratch init : List ℕ) (t : List (List ℕ)) (rho : List ℕ)
    (ht : t.length = k) (hcan : ∀ f ∈ t, Canonical f) (hrho : rho.length = 32)
    (hrhob : ∀ x ∈ rho, x < 256) (hscratch : scratch.length = 384)
    (hinit : init.length = ekSize k) :
    parseEk k (encodeEk k scratch init t rho) = some (t, rho) := by
  rw [encodeEk_eq k scratch init t rho ht hcan hrho hscratch hinit]
  have hbl := length_encodeEk_blocks t hcan
  have hfl := length_flatten_blocks _ 384 hbl
  simp only [List.length_map] at hfl
  unfold parseEk
  rw [ite_eq_right (by simp [hfl, hrho, ekSize, ht]), parseLoop_flatten ht hcan rho hrhob]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  exact sub_prefix_end _ rho _ 32 (by rw [hfl, ht]) hrho.symm

theorem length_encodeEk (k : ℕ) (scratch init : List ℕ) (t : List (List ℕ)) (rho : List ℕ)
    (ht : t.length = k) (hcan : ∀ f ∈ t, Canonical f) (hrho : rho.length = 32)
    (hscratch : scratch.length = 384) (hinit : init.length = ekSize k) :
    (encodeEk k scratch init t rho).length = ekSize k := by
  rw [encodeEk_eq k scratch init t rho ht hcan hrho hscratch hinit]
  have hfl := length_flatten_blocks _ 384 (length_encodeEk_blocks t hcan)
  simp only [List.length_map] at hfl
  simp [hfl, hrho, ekSize, ht]

theorem encodeEk_lt (k : ℕ) (scratch init : List ℕ) (t : List (List ℕ)) (rho : List ℕ)
    (ht : t.length = k) (hcan : ∀ f ∈ t, Canonical f) (hrho : rho.length = 32)
    (hrhob : ∀ x ∈ rho, x < 256) (hscratch : scratch.length = 384)
    (hinit : init.length = ekSize k) :
    ∀ x ∈ encodeEk k scratch init t rho, x < 256 := by
  rw [encodeEk_eq k scratch init t rho ht hcan hrho hscratch hinit]
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact flatten_byteEncode12_lt hcan x h
  · exact hrhob x h

/-! ## Expanded decapsulation keys -/

/-- `decapsulation_key_to_expanded dk` (lines 401–409), for `ŝ = s`,
`ek.encoded = ek`, `ek.h = h` and the implicit-rejection seed `z`. -/
def dkToExpanded (k : ℕ) (scratch init : List ℕ) (s : List (List ℕ)) (ek h z : List ℕ) :
    List ℕ :=
  let out := (List.range k).foldl
    (fun out i => blit (encode12 scratch (s.getD i [])) 0 out (i * 384) 384) init
  let out := blit ek 0 out (k * 384) (ekSize k)
  let out := blit h 0 out (k * 384 + ekSize k) 32
  blit z 0 out (dkSize k - 32) 32

theorem dkToExpanded_eq (k : ℕ) (scratch init : List ℕ) (s : List (List ℕ)) (ek h z : List ℕ)
    (hs : s.length = k) (hcan : ∀ f ∈ s, Canonical f) (hek : ek.length = ekSize k)
    (hh : h.length = 32) (hz : z.length = 32) (hscratch : scratch.length = 384)
    (hinit : init.length = dkSize k) :
    dkToExpanded k scratch init s ek h z = (s.map (Spec.byteEncode 12)).flatten ++ ek ++ h ++ z := by
  have hfl := length_flatten_blocks _ 384 (length_encodeEk_blocks s hcan)
  simp only [List.length_map, hs] at hfl
  unfold dkToExpanded
  simp only
  rw [blit_encode12_blocks k scratch init s hs hcan hscratch]
  generalize (s.map (Spec.byteEncode 12)).flatten = P at hfl ⊢
  rw [← hfl, show ekSize k = ek.length from hek.symm, blit_after_prefix, List.drop_drop]
  rw [show P.length + ek.length = (P ++ ek).length by simp, show (32 : ℕ) = h.length from hh.symm,
    blit_after_prefix, List.drop_drop]
  rw [show dkSize k - h.length = (P ++ ek ++ h).length by simp [dkSize, hfl, hek, hh]; omega,
    show h.length = z.length by rw [hh, hz], blit_after_prefix, List.drop_drop,
    List.drop_eq_nil_of_le (by simp [hinit, hz, hek, hfl, dkSize]), List.append_nil]

/-- `decapsulation_key_of_expanded encoded` (lines 419–443), keeping the
byte-level outputs `(ŝ, (t̂, ρ), z)`. `parse_s` is the same loop as `parse` in
`parse_ek`. `H` is SHA3-256 (abstract here); the OCaml comparison
`ct_equal h ek.h <> 1` is modelled as `h ≠ H(ek)`. -/
def dkOfExpanded (k : ℕ) (H : List ℕ → List ℕ) (encoded : List ℕ) :
    Option (List (List ℕ) × (List (List ℕ) × List ℕ) × List ℕ) :=
  if encoded.length ≠ dkSize k then none
  else match parseLoop k encoded [] 0 with
    | none => none
    | some s =>
      let ekOffset := k * 384
      let ekBytes := sub encoded ekOffset (ekSize k)
      match parseEk k ekBytes with
      | none => none
      | some ek =>
        let hOffset := ekOffset + ekSize k
        let h := sub encoded hOffset 32
        if h ≠ H ekBytes then none
        else some (s, ek, sub encoded (hOffset + 32) 32)

/-- **The expanded-key regions tile the key.** `decapsulation_key_of_expanded`
reads `ŝ` from `[0, 384k)`, `ek` from `[384k, 768k + 32)`, `H(ek)` from
`[768k + 32, 768k + 64)` and `z` from `[768k + 64, 768k + 96)`: exactly the
regions `decapsulation_key_to_expanded` writes. -/
theorem dk_regions (k : ℕ) (P ek h z : List ℕ) (hP : P.length = k * 384)
    (hek : ek.length = ekSize k) (hh : h.length = 32) (hz : z.length = 32) :
    sub (P ++ ek ++ h ++ z) (k * 384) (ekSize k) = ek ∧
    sub (P ++ ek ++ h ++ z) (k * 384 + ekSize k) 32 = h ∧
    sub (P ++ ek ++ h ++ z) (k * 384 + ekSize k + 32) 32 = z ∧
    (P ++ ek ++ h ++ z).length = dkSize k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.append_assoc (P ++ ek) h z]
    exact sub_prefix' P ek (h ++ z) (k * 384) (ekSize k) hP.symm hek.symm
  · exact sub_prefix' (P ++ ek) h z (k * 384 + ekSize k) 32 (by simp [hP, hek]) hh.symm
  · exact sub_prefix_end (P ++ ek ++ h) z (k * 384 + ekSize k + 32) 32
      (by simp [hP, hek, hh]; ring) hz.symm
  · simp [hP, hek, hh, hz, dkSize]; ring

/-- **Round trip for expanded decapsulation keys.** -/
theorem dkOfExpanded_dkToExpanded (k : ℕ) (H : List ℕ → List ℕ) (scratch init initEk : List ℕ)
    (s t : List (List ℕ)) (rho z : List ℕ)
    (hs : s.length = k) (hcans : ∀ f ∈ s, Canonical f) (ht : t.length = k)
    (hcant : ∀ f ∈ t, Canonical f) (hrho : rho.length = 32) (hrhob : ∀ x ∈ rho, x < 256)
    (hz : z.length = 32) (hzb : ∀ x ∈ z, x < 256) (hHlen : ∀ x, (H x).length = 32)
    (hHb : ∀ x, ∀ y ∈ H x, y < 256) (hscratch : scratch.length = 384)
    (hinit : init.length = dkSize k) (hinitEk : initEk.length = ekSize k) :
    dkOfExpanded k H
        (dkToExpanded k scratch init s (encodeEk k scratch initEk t rho)
          (H (encodeEk k scratch initEk t rho)) z) =
      some (s, (t, rho), z) := by
  have hek := length_encodeEk k scratch initEk t rho ht hcant hrho hscratch hinitEk
  have hekb := encodeEk_lt k scratch initEk t rho ht hcant hrho hrhob hscratch hinitEk
  have hpe := parseEk_encodeEk k scratch initEk t rho ht hcant hrho hrhob hscratch hinitEk
  generalize encodeEk k scratch initEk t rho = ek at hek hekb hpe
  rw [dkToExpanded_eq k scratch init s ek (H ek) z hs hcans hek (hHlen ek) hz hscratch hinit]
  have hfls := length_flatten_blocks _ 384 (length_encodeEk_blocks s hcans)
  simp only [List.length_map] at hfls
  obtain ⟨r1, r2, r3, r4⟩ := dk_regions k ((s.map (Spec.byteEncode 12)).flatten) ek (H ek) z
    (by rw [hfls, hs]) hek (hHlen ek) hz
  have hR : ∀ x ∈ ek ++ H ek ++ z, x < 256 := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (h | h) | h
    · exact hekb x h
    · exact hHb ek x h
    · exact hzb x h
  have hloop := parseLoop_flatten hs hcans (ek ++ H ek ++ z) hR
  simp only [List.append_assoc] at hloop r1 r2 r3 r4 ⊢
  unfold dkOfExpanded
  rw [ite_eq_right (by rw [r4]; simp), hloop]
  simp only
  rw [r1, hpe]
  simp only
  rw [r2, ite_eq_right (by simp), r3]

/-! ## Ciphertexts -/

/-- The ciphertext written by `pke_encrypt` (lines 483–489):
```
for i = 0 to k - 1 do
  Bytes.blit_string (encode_compressed du (Array.unsafe_get u i)) 0 out
    (i * encoding_size_u) encoding_size_u
done;
Bytes.blit_string (encode_compressed dv v) 0 out (k * encoding_size_u) encoding_size_v
``` -/
def ctLayout (k du dv : ℕ) (compress : ℕ → ℕ → ℕ) (init : List ℕ) (u : List (List ℕ))
    (v : List ℕ) : List ℕ :=
  let out := (List.range k).foldl (fun out i =>
    blit (encodeCompressed compress du (u.getD i [])) 0 out (i * (256 * du / 8)) (256 * du / 8)) init
  blit (encodeCompressed compress dv v) 0 out (k * (256 * du / 8)) (256 * dv / 8)

/-- The ciphertext parsing of `pke_decrypt` (lines 500–501). -/
def ctParse (k du dv : ℕ) (decompress : ℕ → ℕ → ℕ) (c : List ℕ) : List (List ℕ) × List ℕ :=
  ((List.range k).map (fun i => decodeCompressed decompress du c (i * (256 * du / 8))),
    decodeCompressed decompress dv c (k * (256 * du / 8)))

/-- **The ciphertext is `c₁ ‖ c₂`** with `c₁ = ByteEncode_du(Compress_du(u))`
and `c₂ = ByteEncode_dv(Compress_dv(v))` (FIPS 203 Algorithm 14, lines
22–24). -/
theorem ctLayout_eq (k du dv : ℕ) (compress : ℕ → ℕ → ℕ) (init : List ℕ) (u : List (List ℕ))
    (v : List ℕ) (hu : u.length = k) (hul : ∀ f ∈ u, f.length = 256) (hv : v.length = 256)
    (hdu : du ≤ 56) (hdv : dv ≤ 56) (hcu : ∀ x, compress x du < 2 ^ du)
    (hcv : ∀ x, compress x dv < 2 ^ dv) (hinit : init.length = ctSize k du dv) :
    ctLayout k du dv compress init u v =
      (u.map (fun f => Spec.byteEncode du (f.map (fun x => compress x du)))).flatten ++
        Spec.byteEncode dv (v.map (fun x => compress x dv)) := by
  have hmap : ∀ i, encodeCompressed compress du (u.getD i []) =
      (u.map (encodeCompressed compress du)).getD i (encodeCompressed compress du []) := by
    intro i; rw [List.getD_map]
  have hblocks : ∀ b ∈ u.map (encodeCompressed compress du), b.length = 256 * du / 8 := by
    intro b hb
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
    rw [length_encodeCompressed compress du f (hul f hf) hdu hcu]; omega
  have hgetD : ∀ i < k, (u.map (encodeCompressed compress du)).getD i
      (encodeCompressed compress du []) = (u.map (encodeCompressed compress du)).getD i [] := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simp [hu, hi]), List.getD_eq_getElem _ _ (by simp [hu, hi])]
  unfold ctLayout
  have hfold : (List.range k).foldl (fun out i =>
      blit (encodeCompressed compress du (u.getD i [])) 0 out (i * (256 * du / 8)) (256 * du / 8))
      init = (List.range k).foldl (fun out i => blit ((u.map (encodeCompressed compress du)).getD i [])
        0 out (i * (256 * du / 8)) (256 * du / 8)) init := by
    apply List.foldl_ext
    intro out i hi
    rw [List.mem_range] at hi
    rw [hmap, hgetD i hi]
  rw [hfold, show k = (u.map (encodeCompressed compress du)).length by simp [hu],
    blit_blocks _ _ hblocks init _ le_rfl, List.take_length]
  have hfl := length_flatten_blocks _ _ hblocks
  simp only [List.length_map] at hfl ⊢
  have hvlen : (encodeCompressed compress dv v).length = 256 * dv / 8 := by
    rw [length_encodeCompressed compress dv v hv hdv hcv]; omega
  rw [show u.length * (256 * du / 8) = (u.map (encodeCompressed compress du)).flatten.length by
    rw [hfl], ← hvlen, blit_after_prefix, List.drop_drop,
    List.drop_eq_nil_of_le (by rw [hinit, hvlen, hfl, ctSize, hu]), List.append_nil,
    encodeCompressed_eq compress dv v hv hdv hcv]
  congr 2
  exact List.map_congr_left (fun f hf => encodeCompressed_eq compress du f (hul f hf) hdu hcu)

/-- **`pke_decrypt` parses `c₁ ‖ c₂` as FIPS 203 Algorithm 15 lines 1–4:**
`u' = Decompress_du(ByteDecode_du(c₁))`, `v' = Decompress_dv(ByteDecode_dv(c₂))`,
for a ciphertext of the length `ciphertext_of_octets` checks. -/
theorem ctParse_eq (k du dv : ℕ) (decompress : ℕ → ℕ → ℕ) (c : List ℕ)
    (hc : c.length = ctSize k du dv) (hb : ∀ x ∈ c, x < 256)
    (hdu1 : 1 ≤ du) (hdu : du < 12) (hdv1 : 1 ≤ dv) (hdv : dv < 12) :
    ctParse k du dv decompress c =
      ((List.range k).map (fun i =>
          (Spec.byteDecode du (sub c (i * (32 * du)) (32 * du))).map (fun x => decompress x du)),
        (Spec.byteDecode dv (sub c (k * (32 * du)) (32 * dv))).map (fun x => decompress x dv)) := by
  have e1 : 256 * du / 8 = 32 * du := by omega
  have e2 : 256 * dv / 8 = 32 * dv := by omega
  unfold ctParse
  rw [e1]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    apply decodeCompressed_eq decompress du c _ hdu1 hdu _ hb
    rw [hc, ctSize, e1, e2]; nlinarith
  · apply decodeCompressed_eq decompress dv c _ hdv1 hdv _ hb
    rw [hc, ctSize, e1, e2]

/-- `ByteDecode_d(encode_compressed d f) = Compress_d(f)`. -/
theorem byteDecode_encodeCompressed (compress : ℕ → ℕ → ℕ) (d : ℕ) (f : List ℕ)
    (hf : f.length = 256) (hd1 : 1 ≤ d) (hd : d < 12) (hc : ∀ x, compress x d < 2 ^ d) :
    Spec.byteDecode d (encodeCompressed compress d f) = f.map (fun x => compress x d) := by
  have henc := encodeCompressed_eq_packCodes compress d f hf (by omega) hc
  have hcodes : ∀ v ∈ f.map (fun x => compress x d), v < 2 ^ d := by simp [hc]
  have hlen : (f.map (fun x => compress x d)).length = 256 := by simp [hf]
  have hreg := Packer.packCodes_regroup hcodes (by rw [hlen]; exact ⟨32 * d, by ring⟩)
  rw [← henc] at hreg
  have hplen : (encodeCompressed compress d f).length = 32 * d :=
    length_encodeCompressed compress d f hf (by omega) hc
  have hspec := Spec.byteDecode_regroup (d := d) hd (B := encodeCompressed compress d f) hplen
    hreg.right_lt
  exact Regroup.left_unique hd1 hspec hreg

/-- **Ciphertext round trip.** `pke_decrypt`'s parsing of the ciphertext
written by `pke_encrypt` recovers `Decompress(Compress(·))` of `u` and `v`:
the compressed codes are transmitted exactly. -/
theorem ctParse_ctLayout (k du dv : ℕ) (compress decompress : ℕ → ℕ → ℕ) (init : List ℕ)
    (u : List (List ℕ)) (v : List ℕ) (hu : u.length = k) (hul : ∀ f ∈ u, f.length = 256)
    (hv : v.length = 256) (hdu1 : 1 ≤ du) (hdu : du < 12) (hdv1 : 1 ≤ dv) (hdv : dv < 12)
    (hcu : ∀ x, compress x du < 2 ^ du) (hcv : ∀ x, compress x dv < 2 ^ dv)
    (hinit : init.length = ctSize k du dv) :
    ctParse k du dv decompress (ctLayout k du dv compress init u v) =
      (u.map (fun f => f.map (fun x => decompress (compress x du) du)),
        v.map (fun x => decompress (compress x dv) dv)) := by
  rw [ctLayout_eq k du dv compress init u v hu hul hv (by omega) (by omega) hcu hcv hinit]
  have hblk : ∀ f ∈ u, (Spec.byteEncode du (f.map (fun x => compress x du))).length = 32 * du :=
    fun f hf => Spec.length_byteEncode (by simp [hul f hf]) (by simp [hcu])
  have hblocks : ∀ b ∈ u.map (fun f => Spec.byteEncode du (f.map (fun x => compress x du))),
      b.length = 32 * du := by
    intro b hb
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
    exact hblk f hf
  have hfl := length_flatten_blocks _ _ hblocks
  simp only [List.length_map] at hfl
  have hvl : (Spec.byteEncode dv (v.map (fun x => compress x dv))).length = 32 * dv :=
    Spec.length_byteEncode (by simp [hv]) (by simp [hcv])
  have hb : ∀ x ∈ (u.map (fun f => Spec.byteEncode du (f.map (fun x => compress x du)))).flatten ++
      Spec.byteEncode dv (v.map (fun x => compress x dv)), x < 256 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨b, hb, hxb⟩ := List.mem_flatten.mp h
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
      exact (Spec.byteEncode_regroup (by simp [hul f hf]) (by simp [hcu])).right_lt x hxb
    · exact (Spec.byteEncode_regroup (by simp [hv]) (by simp [hcv])).right_lt x h
  rw [ctParse_eq k du dv decompress _ (by
    rw [List.length_append, hfl, hvl, ctSize, hu, show 256 * du / 8 = 32 * du by omega,
      show 256 * dv / 8 = 32 * dv by omega]) hb hdu1 hdu hdv1 hdv]
  have hdecode : ∀ (d : ℕ) (g : List ℕ), 1 ≤ d → d < 12 → g.length = 256 →
      (∀ x, compress x d < 2 ^ d) →
      Spec.byteDecode d (Spec.byteEncode d (g.map (fun x => compress x d))) =
        g.map (fun x => compress x d) := by
    intro d g hd1 hd hg hc
    have hcodes : ∀ y ∈ g.map (fun x => compress x d), y < 2 ^ d := by simp [hc]
    have hl : (g.map (fun x => compress x d)).length = 256 := by simp [hg]
    have h1 := Spec.byteEncode_regroup hl hcodes
    have h2 := Spec.byteDecode_regroup hd (Spec.length_byteEncode hl hcodes) h1.right_lt
    exact Regroup.left_unique hd1 h2 h1
  congr 1
  · apply List.ext_getElem
    · simp [hu]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [sub_flatten_blocks _ _ hblocks _ i (by simpa using h2)]
      simp only [List.getElem_map]
      rw [hdecode du _ hdu1 hdu (hul _ (List.getElem_mem _)) hcu, List.map_map]
      rfl
  · rw [show k * (32 * du) = ((u.map (fun f => Spec.byteEncode du
        (f.map (fun x => compress x du)))).flatten).length by rw [hfl, hu]]
    rw [sub_prefix_end _ _ _ _ rfl hvl.symm, hdecode dv v hdv1 hdv hv hcv, List.map_map]
    rfl

end OcamlPq.Encoding.Mlkem
