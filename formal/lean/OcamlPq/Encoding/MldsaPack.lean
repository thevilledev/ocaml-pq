import OcamlPq.Encoding.Packer

/-!
# ML-DSA polynomial packings

Models of the ML-DSA packing functions in `mldsa/mldsa_engine.ml`
(lines 302–326), all thin wrappers around `pack_codes`/`unpack_codes`, and of
`u16_le` (lines 165–169).

The code computes the codes `b − w_i` with OCaml `int` subtraction; the models
convert them to `ℕ` with `Int.toNat`, which is exact on the stated input
ranges (the codes are then in `[0, 2^bits)`).

Results (all for polynomials of 256 coefficients):

* `packT1_eq`, `unpackT1_eq`: `pack_t1 = SimpleBitPack(·, 2^10 − 1)` and
  `unpack_t1 = SimpleBitUnpack(·, 2^10 − 1)`; `packT1_unpackT1`,
  `unpackT1_packT1`: inverse bijections between `[0, 2^10)^256` and
  `𝔹^320`.
* `packT0_eq`, `unpackT0_eq`: `pack_t0 = BitPack(·, 2^12 − 1, 2^12)`,
  `unpack_t0 = BitUnpack(·, 2^12 − 1, 2^12)`, and the bijection between
  `(−2^12, 2^12]^256` and `𝔹^416` (`unpackT0_packT0`, `packT0_unpackT0`,
  `unpackT0_range`).
* `packZ_eq`, `unpackZ_eq`: `pack_z = BitPack(·, γ₁ − 1, γ₁)` and
  `unpack_z = BitUnpack(·, γ₁ − 1, γ₁)` for `γ₁ = 2^17` (18 bits) and
  `γ₁ = 2^19` (20 bits), with the bijection between `(−γ₁, γ₁]^256` and
  `𝔹^{32·bits}`.
* `packW1_eq`: `pack_w1 = SimpleBitPack(·, (q − 1)/(2γ₂) − 1)` with 6 bits
  (`γ₂ = (q − 1)/88`) or 4 bits (`γ₂ = (q − 1)/32`).
* `packEta_eq`, `unpackEta_eq`: `pack_eta = BitPack(·, η, η)` for `η = 2`
  (3 bits) and `η = 4` (4 bits); `unpack_eta` returns `Ok` exactly on the
  images of `pack_eta` over `[−η, η]^256` (`unpackEta_eq_some_iff`), and then
  returns `BitUnpack(·, η, η)`.

**Deviation from FIPS 204 (stricter).** FIPS 204 `skDecode` (Algorithm 25)
applies `BitUnpack(·, η, η)` without a range check, so a code above `2η`
decodes to a coefficient below `−η` (e.g. code 7 with `η = 2` gives `−5`).
`unpack_eta` rejects such codes (`unpackEta_eq_none_iff`). FIPS 204 notes
that `skDecode` is only meant for keys produced by `skEncode`, and every
such key passes; the extra check only rejects malformed keys.
-/

namespace OcamlPq.Encoding.Mldsa

open Nat (ofDigits)
open OcamlPq.Encoding
open OcamlPq.Encoding.Packer

/-- The ML-DSA modulus `q`. -/
def q : ℕ := 8380417

/-! ## Generic offset packing -/

theorem bitlen_pow_sub_one (c : ℕ) (hc : 1 ≤ c) : Spec.bitlen (2 ^ c - 1) = c := by
  apply Spec.bitlen_eq _ _ hc
  · have : 2 ^ (c - 1) * 2 = 2 ^ c := by rw [← pow_succ]; congr 1; omega
    have : 1 ≤ 2 ^ (c - 1) := Nat.one_le_two_pow
    omega
  · have : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    omega

/-- `pack_codes` of the codes `b − w_i` is `BitPack(w, a, b)` when
`bitlen(a + b) = bits` and every coefficient is in `[−a, b]`. -/
theorem packCodes_offset_eq_bitPack (a b bits : ℕ) (hbits : Spec.bitlen (a + b) = bits)
    (hab : a + b < 2 ^ bits) (w : List ℤ) (hw : w.length = 256)
    (hrange : ∀ v ∈ w, -(a : ℤ) ≤ v ∧ v ≤ b) :
    packCodes bits (w.map fun v => ((b : ℤ) - v).toNat) = Spec.bitPack w a b := by
  have hcodes : ∀ x ∈ w.map (fun v => ((b : ℤ) - v).toNat), x < 2 ^ bits := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2⟩ := hrange v hv
    have : ((b : ℤ) - v).toNat ≤ a + b := by omega
    omega
  have hlen : (w.map fun v => ((b : ℤ) - v).toNat).length = 256 := by simp [hw]
  have h1 := packCodes_regroup hcodes (by rw [hlen]; exact ⟨32 * bits, by ring⟩)
  have h2 := Spec.bitPack_regroup (a := a) (b := b) hw (by rw [hbits]; simpa using hcodes)
  rw [hbits] at h2
  exact Regroup.right_unique (by norm_num) h1 h2

/-- `unpack_codes` followed by `b − ·` is `BitUnpack(·, a, b)`. -/
theorem unpackCodes_offset_eq_bitUnpack (a b bits : ℕ) (hbits : Spec.bitlen (a + b) = bits)
    (h1 : 1 ≤ bits) (v : List ℕ) (hv : v.length = 32 * bits) (hb : ∀ x ∈ v, x < 256) :
    (unpackCodes bits v).map (fun c : ℕ => (b : ℤ) - (c : ℤ)) = Spec.bitUnpack v a b := by
  rw [Spec.bitUnpack_eq, hbits]
  congr 1
  have hdiv : bits ∣ v.length * 8 := ⟨256, by rw [hv]; ring⟩
  exact Regroup.left_unique h1 (unpackCodes_regroup h1 hdiv hb)
    (Spec.unpackCodesSpec_regroup hv hb)

/-- `pack_codes` is `SimpleBitPack(w, b)` when `bitlen b = bits`. -/
theorem packCodes_eq_simpleBitPack (b bits : ℕ) (hbits : Spec.bitlen b = bits) (w : List ℕ)
    (hw : w.length = 256) (hlt : ∀ x ∈ w, x < 2 ^ bits) :
    packCodes bits w = Spec.simpleBitPack w b := by
  have h1 := packCodes_regroup hlt (by rw [hw]; exact ⟨32 * bits, by ring⟩)
  have h2 := Spec.simpleBitPack_regroup (b := b) hw (by rw [hbits]; exact hlt)
  rw [hbits] at h2
  exact Regroup.right_unique (by norm_num) h1 h2

/-- `unpack_codes` is `SimpleBitUnpack(v, b)` when `bitlen b = bits`. -/
theorem unpackCodes_eq_simpleBitUnpack (b bits : ℕ) (hbits : Spec.bitlen b = bits)
    (h1 : 1 ≤ bits) (v : List ℕ) (hv : v.length = 32 * bits) (hb : ∀ x ∈ v, x < 256) :
    unpackCodes bits v = Spec.simpleBitUnpack v b := by
  rw [Spec.simpleBitUnpack_eq, hbits]
  have hdiv : bits ∣ v.length * 8 := ⟨256, by rw [hv]; ring⟩
  exact Regroup.left_unique h1 (unpackCodes_regroup h1 hdiv hb)
    (Spec.unpackCodesSpec_regroup hv hb)

/-- Offset packing round trip: unpacking what was packed gives the
coefficients back. -/
theorem unpack_pack_offset (b bits : ℕ) (h1 : 1 ≤ bits) (w : List ℤ) (hw : w.length = 256)
    (hrange : ∀ v ∈ w, 0 ≤ (b : ℤ) - v ∧ (b : ℤ) - v < 2 ^ bits) :
    (unpackCodes bits (packCodes bits (w.map fun v => ((b : ℤ) - v).toNat))).map
      (fun c : ℕ => (b : ℤ) - (c : ℤ)) = w := by
  have hcodes : ∀ x ∈ w.map (fun v => ((b : ℤ) - v).toNat), x < 2 ^ bits := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2⟩ := hrange v hv
    have : (((b : ℤ) - v).toNat : ℤ) < 2 ^ bits := by rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast this
  rw [unpackCodes_packCodes h1 hcodes (by simp [hw]; exact ⟨32 * bits, by ring⟩), List.map_map]
  conv_rhs => rw [← List.map_id w]
  apply List.map_congr_left
  intro v hv
  simp only [Function.comp_apply, id]
  rw [Int.toNat_of_nonneg (hrange v hv).1]; ring

/-- Offset packing round trip in the other direction: every byte string of
length `32 · bits` is the packing of the coefficients it unpacks to. -/
theorem pack_unpack_offset (b bits : ℕ) (h1 : 1 ≤ bits) (v : List ℕ) (hv : v.length = 32 * bits)
    (hb : ∀ x ∈ v, x < 256) :
    packCodes bits (((unpackCodes bits v).map (fun c : ℕ => (b : ℤ) - (c : ℤ))).map
      fun w => ((b : ℤ) - w).toNat) = v := by
  rw [List.map_map]
  have : ((fun w => ((b : ℤ) - w).toNat) ∘ fun c : ℕ => (b : ℤ) - (c : ℤ)) = id := by
    funext c; simp
  rw [this, List.map_id]
  exact packCodes_unpackCodes h1 ⟨256, by rw [hv]; ring⟩ hb

/-! ## `pack_t1` / `unpack_t1` -/

/-- `pack_t1 polynomial = pack_codes ~bits:10 polynomial` (line 317). -/
def packT1 (p : List ℕ) : List ℕ := packCodes 10 p

/-- `unpack_t1 input = unpack_codes ~bits:10 input` (line 318). -/
def unpackT1 (input : List ℕ) : List ℕ := unpackCodes 10 input

theorem bitlen_t1 : Spec.bitlen (2 ^ 10 - 1) = 10 := bitlen_pow_sub_one 10 (by norm_num)

/-- `bitlen(q − 1) − d = 10`: the `t1` width of FIPS 204 `pkEncode`. -/
theorem bitlen_q_sub_one : Spec.bitlen (q - 1) = 23 := by
  apply Spec.bitlen_eq <;> norm_num [q]

theorem packT1_eq (p : List ℕ) (hp : p.length = 256) (hlt : ∀ x ∈ p, x < 2 ^ 10) :
    packT1 p = Spec.simpleBitPack p (2 ^ 10 - 1) :=
  packCodes_eq_simpleBitPack _ 10 bitlen_t1 p hp hlt

theorem unpackT1_eq (v : List ℕ) (hv : v.length = 320) (hb : ∀ x ∈ v, x < 256) :
    unpackT1 v = Spec.simpleBitUnpack v (2 ^ 10 - 1) :=
  unpackCodes_eq_simpleBitUnpack _ 10 bitlen_t1 (by norm_num) v (by rw [hv]) hb

theorem unpackT1_packT1 (p : List ℕ) (hp : p.length = 256) (hlt : ∀ x ∈ p, x < 2 ^ 10) :
    unpackT1 (packT1 p) = p :=
  unpackCodes_packCodes (by norm_num) hlt (by rw [hp]; norm_num)

theorem packT1_unpackT1 (v : List ℕ) (hv : v.length = 320) (hb : ∀ x ∈ v, x < 256) :
    packT1 (unpackT1 v) = v :=
  packCodes_unpackCodes (by norm_num) (by rw [hv]; norm_num) hb

/-! ## `pack_t0` / `unpack_t0` -/

/-- `pack_t0` (lines 311–312):
`pack_codes ~bits:13 (Array.map (fun value -> (1 lsl 12) - value) polynomial)`. -/
def packT0 (p : List ℤ) : List ℕ := packCodes 13 (p.map fun v => ((2 ^ 12 : ℕ) - v : ℤ).toNat)

/-- `unpack_t0` (lines 314–315):
`Array.map (fun value -> (1 lsl 12) - value) (unpack_codes ~bits:13 input)`. -/
def unpackT0 (input : List ℕ) : List ℤ :=
  (unpackCodes 13 input).map fun c : ℕ => ((2 ^ 12 : ℕ) : ℤ) - (c : ℤ)

theorem bitlen_t0 : Spec.bitlen (2 ^ 12 - 1 + 2 ^ 12) = 13 := by
  rw [show 2 ^ 12 - 1 + 2 ^ 12 = 2 ^ 13 - 1 by norm_num]; exact bitlen_pow_sub_one 13 (by norm_num)

/-- `t₀` coefficients: `(−2^12, 2^12]`. -/
def T0Range (v : ℤ) : Prop := -(2 ^ 12 : ℤ) < v ∧ v ≤ 2 ^ 12

theorem packT0_eq (p : List ℤ) (hp : p.length = 256) (hr : ∀ v ∈ p, T0Range v) :
    packT0 p = Spec.bitPack p (2 ^ 12 - 1) (2 ^ 12) := by
  unfold packT0
  apply packCodes_offset_eq_bitPack _ _ 13 bitlen_t0 (by norm_num) p hp
  intro v hv
  obtain ⟨h1, h2⟩ := hr v hv
  constructor <;> push_cast <;> omega

theorem unpackT0_eq (v : List ℕ) (hv : v.length = 416) (hb : ∀ x ∈ v, x < 256) :
    unpackT0 v = Spec.bitUnpack v (2 ^ 12 - 1) (2 ^ 12) :=
  unpackCodes_offset_eq_bitUnpack _ _ 13 bitlen_t0 (by norm_num) v (by rw [hv]) hb

theorem unpackT0_packT0 (p : List ℤ) (hp : p.length = 256) (hr : ∀ v ∈ p, T0Range v) :
    unpackT0 (packT0 p) = p :=
  unpack_pack_offset (2 ^ 12) 13 (by norm_num) p hp
    (fun v hv => by obtain ⟨h1, h2⟩ := hr v hv; push_cast; constructor <;> omega)

theorem packT0_unpackT0 (v : List ℕ) (hv : v.length = 416) (hb : ∀ x ∈ v, x < 256) :
    packT0 (unpackT0 v) = v :=
  pack_unpack_offset (2 ^ 12) 13 (by norm_num) v (by rw [hv]) hb

/-- Every decoded `t₀` coefficient lies in `(−2^12, 2^12]`. -/
theorem unpackT0_range (v : List ℕ) (hv : v.length = 416) (hb : ∀ x ∈ v, x < 256) :
    ∀ w ∈ unpackT0 v, T0Range w := by
  intro w hw
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
  have := (unpackCodes_regroup (bits := 13) (by norm_num) ⟨256, by rw [hv]⟩ hb).left_lt c hc
  unfold T0Range
  push_cast
  constructor <;> omega

/-! ## `pack_z` / `unpack_z` -/

/-- `pack_z` (lines 320–321) with `P.gamma1 = γ₁` and `z_bits = bits`. -/
def packZ (γ1 bits : ℕ) (p : List ℤ) : List ℕ := packCodes bits (p.map fun v => ((γ1 : ℤ) - v).toNat)

/-- `unpack_z` (lines 323–324). -/
def unpackZ (γ1 bits : ℕ) (input : List ℕ) : List ℤ :=
  (unpackCodes bits input).map fun c : ℕ => (γ1 : ℤ) - (c : ℤ)

/-- `z_bits = if P.gamma1 = 1 lsl 17 then 18 else 20` (line 121). -/
def zBits (γ1 : ℕ) : ℕ := if γ1 = 2 ^ 17 then 18 else 20

/-- The two `γ₁` of ML-DSA: `2^17` (ML-DSA-44) and `2^19` (ML-DSA-65/87);
both are `2^(bits − 1)` with `bits = zBits γ₁`. -/
theorem gamma1_cases (γ1 : ℕ) (h : γ1 = 2 ^ 17 ∨ γ1 = 2 ^ 19) :
    γ1 = 2 ^ (zBits γ1 - 1) ∧ Spec.bitlen (γ1 - 1 + γ1) = zBits γ1 ∧ 1 ≤ zBits γ1 := by
  rcases h with rfl | rfl
  · refine ⟨by decide, ?_, by decide⟩
    rw [show zBits (2 ^ 17) = 18 by decide, show 2 ^ 17 - 1 + 2 ^ 17 = 2 ^ 18 - 1 by norm_num]
    exact bitlen_pow_sub_one 18 (by norm_num)
  · refine ⟨by decide, ?_, by decide⟩
    rw [show zBits (2 ^ 19) = 20 by decide, show 2 ^ 19 - 1 + 2 ^ 19 = 2 ^ 20 - 1 by norm_num]
    exact bitlen_pow_sub_one 20 (by norm_num)

theorem gamma1_double (γ1 : ℕ) (h : γ1 = 2 ^ 17 ∨ γ1 = 2 ^ 19) :
    (γ1 : ℤ) * 2 = 2 ^ zBits γ1 := by
  rcases h with rfl | rfl <;> norm_num [zBits]

/-- `z` coefficients: `(−γ₁, γ₁]`. -/
def ZRange (γ1 : ℕ) (v : ℤ) : Prop := -(γ1 : ℤ) < v ∧ v ≤ γ1

theorem packZ_eq (γ1 : ℕ) (hγ : γ1 = 2 ^ 17 ∨ γ1 = 2 ^ 19) (p : List ℤ) (hp : p.length = 256)
    (hr : ∀ v ∈ p, ZRange γ1 v) :
    packZ γ1 (zBits γ1) p = Spec.bitPack p (γ1 - 1) γ1 := by
  obtain ⟨hpow, hbl, -⟩ := gamma1_cases γ1 hγ
  have hpos : 1 ≤ γ1 := by rcases hγ with rfl | rfl <;> norm_num
  apply packCodes_offset_eq_bitPack _ _ _ hbl _ p hp
  · intro v hv
    obtain ⟨h1, h2⟩ := hr v hv
    constructor
    · push_cast [Nat.cast_sub hpos]; omega
    · exact h2
  · rcases hγ with rfl | rfl <;> decide

theorem unpackZ_eq (γ1 : ℕ) (hγ : γ1 = 2 ^ 17 ∨ γ1 = 2 ^ 19) (v : List ℕ)
    (hv : v.length = 32 * zBits γ1) (hb : ∀ x ∈ v, x < 256) :
    unpackZ γ1 (zBits γ1) v = Spec.bitUnpack v (γ1 - 1) γ1 := by
  obtain ⟨-, hbl, h1⟩ := gamma1_cases γ1 hγ
  exact unpackCodes_offset_eq_bitUnpack _ _ _ hbl h1 v hv hb

theorem unpackZ_packZ (γ1 : ℕ) (hγ : γ1 = 2 ^ 17 ∨ γ1 = 2 ^ 19) (p : List ℤ)
    (hp : p.length = 256) (hr : ∀ v ∈ p, ZRange γ1 v) :
    unpackZ γ1 (zBits γ1) (packZ γ1 (zBits γ1) p) = p := by
  obtain ⟨hpow, -, h1⟩ := gamma1_cases γ1 hγ
  apply unpack_pack_offset γ1 _ h1 p hp
  intro v hv
  obtain ⟨ha, hb⟩ := hr v hv
  have := gamma1_double γ1 hγ
  constructor <;> omega

theorem packZ_unpackZ (γ1 : ℕ) (hγ : γ1 = 2 ^ 17 ∨ γ1 = 2 ^ 19) (v : List ℕ)
    (hv : v.length = 32 * zBits γ1) (hb : ∀ x ∈ v, x < 256) :
    packZ γ1 (zBits γ1) (unpackZ γ1 (zBits γ1) v) = v := by
  obtain ⟨-, -, h1⟩ := gamma1_cases γ1 hγ
  exact pack_unpack_offset γ1 _ h1 v hv hb

theorem unpackZ_range (γ1 : ℕ) (hγ : γ1 = 2 ^ 17 ∨ γ1 = 2 ^ 19) (v : List ℕ)
    (hv : v.length = 32 * zBits γ1) (hb : ∀ x ∈ v, x < 256) :
    ∀ w ∈ unpackZ γ1 (zBits γ1) v, ZRange γ1 w := by
  obtain ⟨hpow, -, h1⟩ := gamma1_cases γ1 hγ
  intro w hw
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
  have := (unpackCodes_regroup (bits := zBits γ1) h1 ⟨256, by rw [hv]; ring⟩ hb).left_lt c hc
  have h2 := gamma1_double γ1 hγ
  have : (c : ℤ) < 2 ^ zBits γ1 := by exact_mod_cast this
  unfold ZRange
  constructor <;> omega

/-! ## `pack_w1` -/

/-- `pack_w1 polynomial = pack_codes ~bits:w1_bits polynomial` (line 326). -/
def packW1 (bits : ℕ) (p : List ℕ) : List ℕ := packCodes bits p

/-- `w1_bits = if P.gamma2 = (q - 1) / 88 then 6 else 4` (line 123). -/
def w1Bits (γ2 : ℕ) : ℕ := if γ2 = (q - 1) / 88 then 6 else 4

/-- The FIPS 204 `w1Encode` bound `(q − 1)/(2γ₂) − 1` has bit length
`w1_bits` for both `γ₂` (Algorithm 28). -/
theorem bitlen_w1 (γ2 : ℕ) (h : γ2 = (q - 1) / 88 ∨ γ2 = (q - 1) / 32) :
    Spec.bitlen ((q - 1) / (2 * γ2) - 1) = w1Bits γ2 := by
  rcases h with rfl | rfl
  · rw [show w1Bits ((q - 1) / 88) = 6 by decide]
    apply Spec.bitlen_eq <;> norm_num [q]
  · rw [show w1Bits ((q - 1) / 32) = 4 by decide]
    apply Spec.bitlen_eq <;> norm_num [q]

theorem packW1_eq (γ2 : ℕ) (hγ : γ2 = (q - 1) / 88 ∨ γ2 = (q - 1) / 32) (p : List ℕ)
    (hp : p.length = 256) (hlt : ∀ x ∈ p, x < 2 ^ w1Bits γ2) :
    packW1 (w1Bits γ2) p = Spec.simpleBitPack p ((q - 1) / (2 * γ2) - 1) :=
  packCodes_eq_simpleBitPack _ _ (bitlen_w1 γ2 hγ) p hp hlt

/-! ## `pack_eta` / `unpack_eta` -/

/-- `eta_bits = if P.eta = 2 then 3 else 4` (line 117). -/
def etaBits (η : ℕ) : ℕ := if η = 2 then 3 else 4

/-- `pack_eta` (lines 302–303). -/
def packEta (η : ℕ) (p : List ℤ) : List ℕ :=
  packCodes (etaBits η) (p.map fun v => ((η : ℤ) - v).toNat)

/-- `unpack_eta` (lines 305–309):
```
let codes = unpack_codes ~bits:eta_bits input in
if Array.exists (fun value -> value > 2 * P.eta) codes then Error _
else Ok (Array.map (fun value -> P.eta - value) codes)
``` -/
def unpackEta (η : ℕ) (input : List ℕ) : Option (List ℤ) :=
  let codes := unpackCodes (etaBits η) input
  if codes.any (fun value => value > 2 * η) then none
  else some (codes.map fun c : ℕ => (η : ℤ) - (c : ℤ))

theorem eta_cases (η : ℕ) (h : η = 2 ∨ η = 4) :
    Spec.bitlen (η + η) = etaBits η ∧ 1 ≤ etaBits η ∧ 2 * η < 2 ^ etaBits η := by
  rcases h with rfl | rfl
  · refine ⟨?_, by decide, by decide⟩
    rw [show etaBits 2 = 3 by decide]; apply Spec.bitlen_eq <;> norm_num
  · refine ⟨?_, by decide, by decide⟩
    rw [show etaBits 4 = 4 by decide]; apply Spec.bitlen_eq <;> norm_num

/-- Secret coefficients: `[−η, η]`. -/
def EtaRange (η : ℕ) (v : ℤ) : Prop := -(η : ℤ) ≤ v ∧ v ≤ η

theorem packEta_eq (η : ℕ) (hη : η = 2 ∨ η = 4) (p : List ℤ) (hp : p.length = 256)
    (hr : ∀ v ∈ p, EtaRange η v) : packEta η p = Spec.bitPack p η η := by
  obtain ⟨hbl, -, hlt⟩ := eta_cases η hη
  exact packCodes_offset_eq_bitPack _ _ _ hbl (by omega) p hp hr

/-- **`unpack_eta` is `BitUnpack(·, η, η)` guarded by the range check.** -/
theorem unpackEta_eq (η : ℕ) (hη : η = 2 ∨ η = 4) (v : List ℕ)
    (hv : v.length = 32 * etaBits η) (hb : ∀ x ∈ v, x < 256) :
    unpackEta η v =
      if (unpackCodes (etaBits η) v).any (fun value => value > 2 * η) then none
      else some (Spec.bitUnpack v η η) := by
  obtain ⟨hbl, h1, -⟩ := eta_cases η hη
  unfold unpackEta
  simp only
  rw [unpackCodes_offset_eq_bitUnpack _ _ _ hbl h1 v hv hb]

/-- **Strictness of `unpack_eta`.** On byte strings of the right length,
`unpack_eta` returns `Ok s` exactly when `s ∈ [−η, η]^256` and
`pack_eta s` is the input. -/
theorem unpackEta_eq_some_iff (η : ℕ) (hη : η = 2 ∨ η = 4) (v : List ℕ)
    (hv : v.length = 32 * etaBits η) (hb : ∀ x ∈ v, x < 256) (s : List ℤ) :
    unpackEta η v = some s ↔
      s.length = 256 ∧ (∀ w ∈ s, EtaRange η w) ∧ packEta η s = v := by
  obtain ⟨hbl, h1, hlt⟩ := eta_cases η hη
  have hdiv : etaBits η ∣ v.length * 8 := ⟨256, by rw [hv]; ring⟩
  have hreg := unpackCodes_regroup h1 hdiv hb
  have hlen : (unpackCodes (etaBits η) v).length = 256 := by
    have := hreg.length; rw [hv] at this
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < etaBits η) (by rw [this]; ring)
  unfold unpackEta
  simp only
  constructor
  · intro h
    split_ifs at h with hany
    cases h
    simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and, not_lt] at hany
    refine ⟨by simp [hlen], ?_, ?_⟩
    · intro w hw
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
      have := hany c hc
      unfold EtaRange; constructor <;> omega
    · unfold packEta
      exact pack_unpack_offset η _ h1 v hv hb
  · rintro ⟨hs, hr, hpack⟩
    have hcodes : ∀ c ∈ s.map (fun v => ((η : ℤ) - v).toNat), c ≤ 2 * η := by
      intro c hc
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
      obtain ⟨ha, hb'⟩ := hr w hw
      omega
    have hback : unpackCodes (etaBits η) v = s.map (fun v => ((η : ℤ) - v).toNat) := by
      rw [← hpack]
      apply unpackCodes_packCodes h1
      · intro c hc; exact lt_of_le_of_lt (hcodes c hc) hlt
      · simp [hs]; exact ⟨32 * etaBits η, by ring⟩
    rw [hback]
    have hnone : ¬ (s.map (fun v => ((η : ℤ) - v).toNat)).any (fun value => value > 2 * η) := by
      simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and, not_lt]
      exact hcodes
    rw [ite_eq_right hnone, List.map_map]
    congr 1
    conv_rhs => rw [← List.map_id s]
    apply List.map_congr_left
    intro w hw
    obtain ⟨ha, hb'⟩ := hr w hw
    simp only [Function.comp_apply, id]
    rw [Int.toNat_of_nonneg (by omega)]; ring

/-- `unpack_eta` rejects exactly the strings whose FIPS 204 `BitUnpack(·, η, η)`
has a coefficient below `−η` (where FIPS 204 `skDecode` would accept). -/
theorem unpackEta_eq_none_iff (η : ℕ) (hη : η = 2 ∨ η = 4) (v : List ℕ)
    (hv : v.length = 32 * etaBits η) (hb : ∀ x ∈ v, x < 256) :
    unpackEta η v = none ↔ ∃ w ∈ Spec.bitUnpack v η η, w < -(η : ℤ) := by
  obtain ⟨hbl, h1, -⟩ := eta_cases η hη
  rw [unpackEta_eq η hη v hv hb, ← unpackCodes_offset_eq_bitUnpack _ _ _ hbl h1 v hv hb]
  constructor
  · intro h
    split_ifs at h with hany
    simp only [List.any_eq_true, decide_eq_true_eq] at hany
    obtain ⟨c, hc, hgt⟩ := hany
    exact ⟨_, List.mem_map_of_mem hc, by omega⟩
  · rintro ⟨w, hw, hlt⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
    have : (unpackCodes (etaBits η) v).any (fun value => value > 2 * η) := by
      simp only [List.any_eq_true, decide_eq_true_eq]
      exact ⟨c, hc, by omega⟩
    rw [ite_eq_left this]

theorem ofDigits_replicate_max (w n : ℕ) :
    ofDigits (2 ^ w) (List.replicate n (2 ^ w - 1)) + 1 = 2 ^ (w * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, show w * (n + 1) = w + w * n by ring, pow_add,
      ← ih]
    obtain ⟨P, hP⟩ : ∃ P, 2 ^ w = P + 1 := ⟨2 ^ w - 1, by have := Nat.one_le_two_pow (n := w); omega⟩
    rw [hP, Nat.add_sub_cancel]
    ring

/-- All-`0xff` input unpacks to all-ones codes. -/
theorem unpackCodes_ff (bits n : ℕ) (h1 : 1 ≤ bits) :
    unpackCodes bits (List.replicate (bits * n) 255) = List.replicate (8 * n) (2 ^ bits - 1) := by
  have hreg := unpackCodes_regroup (bits := bits) (input := List.replicate (bits * n) 255) h1
    ⟨8 * n, by rw [List.length_replicate]; ring⟩ (fun x hx => by
      rw [List.eq_of_mem_replicate hx]; norm_num)
  apply Regroup.left_unique h1 hreg
  refine ⟨by rw [List.length_replicate, List.length_replicate]; ring, ?_, ?_, ?_⟩
  · intro x hx; rw [List.eq_of_mem_replicate hx]; have := Nat.one_le_two_pow (n := bits); omega
  · intro x hx; rw [List.eq_of_mem_replicate hx]; norm_num
  · have e1 := ofDigits_replicate_max bits (8 * n)
    have e2 := ofDigits_replicate_max 8 (bits * n)
    rw [show 8 * (bits * n) = bits * (8 * n) by ring] at e2
    rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num]
    omega

/-- **A non-canonical `η = 2` block.** The 96 bytes `0xff…` unpack to codes 7,
which FIPS 204 `BitUnpack(·, 2, 2)` (and hence `skDecode`) turns into the
coefficient `2 − 7 = −5 ∉ [−2, 2]`; `unpack_eta` rejects the block. -/
theorem unpackEta_rejects_ff :
    unpackEta 2 (List.replicate 96 255) = none ∧
    (-5 : ℤ) ∈ Spec.bitUnpack (List.replicate 96 255) 2 2 := by
  have hcodes : unpackCodes 3 (List.replicate 96 255) = List.replicate 256 7 := by
    have := unpackCodes_ff 3 32 (by norm_num)
    rwa [show (3 : ℕ) * 32 = 96 from rfl, show (8 : ℕ) * 32 = 256 from rfl,
      show (2 : ℕ) ^ 3 - 1 = 7 from rfl] at this
  have h7 : (7 : ℕ) ∈ List.replicate 256 7 := List.mem_replicate.mpr ⟨by norm_num, rfl⟩
  constructor
  · unfold unpackEta
    rw [show etaBits 2 = 3 from rfl, hcodes, ite_eq_left]
    exact List.any_eq_true.mpr ⟨7, h7, by decide⟩
  · rw [← unpackCodes_offset_eq_bitUnpack 2 2 3 (Spec.bitlen_eq (by norm_num) (by norm_num)
      (by norm_num)) (by norm_num) _ (List.length_replicate) (fun x hx => by
        rw [List.eq_of_mem_replicate hx]; norm_num), hcodes]
    exact List.mem_map.mpr ⟨7, h7, by norm_num⟩

/-! ## `u16_le` -/

/-- `u16_le value` (lines 165–169): the bytes `value land 0xff` and
`(value lsr 8) land 0xff`. -/
def u16Le (value : ℕ) : List ℕ := [value &&& 0xff, (value >>> 8) &&& 0xff]

/-- **`u16_le` is `IntegerToBytes(x, 2)`** (FIPS 204 Algorithm 11) for
`0 ≤ x < 2^16`. -/
theorem u16Le_eq (x : ℕ) : u16Le x = Spec.integerToBytes x 2 := by
  rw [Spec.integerToBytes_eq]
  simp [u16Le, and_ff_eq, shiftRight_eight, List.range_succ]

end OcamlPq.Encoding.Mldsa
