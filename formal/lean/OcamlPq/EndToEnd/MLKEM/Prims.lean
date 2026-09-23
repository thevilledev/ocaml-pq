import OcamlPq.EndToEnd.MLKEM.Adapters

/-!
# The concrete building blocks and their refinement

* `I₀ g₁₂ : ImplPrims`: the models of `lib/mlkem_engine.ml` verified by the
  arithmetic area (`MLKEM.ntt`, `inverseNtt`, `nttMul`, `polyAdd`, `polySub`)
  and the encoding area (`Encoding.Mlkem.encode12`, `decode12`,
  `encodeCompressed`, `decodeCompressed`), with the arithmetic area's models of
  `compress`/`decompress` plugged into the packers. `g₁₂` is the content of
  the uninitialised `Bytes.create encoding_size_12` buffer of `encode_12`
  (every theorem holds for all of them).
* `S₀ : SpecPrims`: the FIPS 203 transcriptions of those two areas:
  Algorithms 9, 10, 11 (`MLKEM.fipsNtt`, `fipsNttInv`, `fipsMultiplyNTTs`),
  Algorithms 5 and 6 (`Encoding.Spec.byteEncode`, `byteDecode`) and
  eq. (4.7)/(4.8) (`MLKEM.compressSpec`, `decompressSpec`, written with ℚ
  rounding). None of them mentions the implementation.
* `refines : Refines (I₀ g₁₂) S₀`, `laws : S₀.Laws`, `algLaws : S₀.AlgLaws`,
  and `compressEncode_one`, `decodeDecompress_one`: the hypotheses of the
  `MLKEMAlg` theorems, discharged from `ntt_refines`, `inverseNtt_refines`,
  `nttMul_refines`, `polyAdd_refines`, `polySub_refines`,
  `encode12_eq_byteEncode`, `decode12_eq_some_iff`, `encodeCompressed_eq`,
  `decodeCompressed_eq`, `compress_eq_spec`, `decompress_eq_spec`,
  `decompress_lt_q`, `fipsNtt_add`, `fipsNtt_fipsNttInv`,
  `fipsNttInv_fipsNtt`, `fipsMultiplyNTTs_pair`, `byteDecode_byteEncode_12`.
-/

namespace OcamlPq.EndToEnd.MLKEM

open OcamlPq.MLKEMAlg

/-! ## `compress` as the packer's parameter -/

/-- `compress x d` (arithmetic area model of lib/mlkem_engine.ml:125-133) as
    the `ℕ → ℕ → ℕ` parameter of the encoding area's `encode_compressed`
    model. OCaml passes it the `int` coefficient `x ≥ 0` and stores its `int`
    result, which the final `land ((1 lsl d) - 1)` makes non-negative. -/
def compressNat (x d : ℕ) : ℕ := (OcamlPq.MLKEM.compress (x : ℤ) d).toNat

/-- `s land ((1 lsl d) - 1)` lies in `[0, 2^d)` for every `int` `s`. -/
theorem land_mask_bounds (s : ℤ) (d : ℕ) :
    0 ≤ Int.land s ((1 : ℤ) <<< d - 1) ∧ Int.land s ((1 : ℤ) <<< d - 1) < 2 ^ d := by
  have hm : (1 : ℤ) <<< d - 1 = ((2 ^ d - 1 : ℕ) : ℤ) := by
    rw [Int.shiftLeft_eq, one_mul, Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  rw [hm]
  have hlt : ∀ x : ℕ, (∀ i ≥ d, x.testBit i = false) → ((x : ℤ) < 2 ^ d) := fun x hx => by
    exact_mod_cast Nat.lt_pow_two_of_testBit x hx
  cases s with
  | ofNat m =>
    show 0 ≤ Int.land (Int.ofNat m) (Int.ofNat (2 ^ d - 1)) ∧
      Int.land (Int.ofNat m) (Int.ofNat (2 ^ d - 1)) < 2 ^ d
    simp only [Int.land]
    refine ⟨by positivity, hlt _ fun i hi => ?_⟩
    simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Bool.and_eq_false_iff,
      decide_eq_false_iff_not, not_lt]
    exact Or.inr hi
  | negSucc m =>
    show 0 ≤ Int.land (Int.negSucc m) (Int.ofNat (2 ^ d - 1)) ∧
      Int.land (Int.negSucc m) (Int.ofNat (2 ^ d - 1)) < 2 ^ d
    simp only [Int.land]
    refine ⟨by positivity, hlt _ fun i hi => ?_⟩
    simp only [Nat.testBit_ldiff, Nat.testBit_two_pow_sub_one, Bool.and_eq_false_iff,
      decide_eq_false_iff_not, not_lt]
    exact Or.inl hi

theorem compressNat_lt (x d : ℕ) : compressNat x d < 2 ^ d := by
  have key : ∀ s : ℤ, (Int.land s ((1 : ℤ) <<< d - 1)).toNat < 2 ^ d := fun s => by
    obtain ⟨h0, h1⟩ := land_mask_bounds s d
    have : ((Int.land s ((1 : ℤ) <<< d - 1)).toNat : ℤ) < ((2 ^ d : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0]; exact_mod_cast h1
    exact_mod_cast this
  exact key _

/-! ## The two instances -/

/-- The OCaml building blocks, as modelled by the arithmetic and encoding
    areas. `g₁₂` is the uninitialised buffer of `encode_12`. -/
def I₀ (g₁₂ : ℕ → Byte) : ImplPrims where
  ntt p := liftArr (OcamlPq.MLKEM.ntt (ipolyToArray p))
  inverseNtt p := liftArr (OcamlPq.MLKEM.inverseNtt (ipolyToArray p))
  nttMul p r := liftArr (OcamlPq.MLKEM.nttMul (ipolyToArray p) (ipolyToArray r))
  polyAdd p r := liftArr (OcamlPq.MLKEM.polyAdd (ipolyToArray p) (ipolyToArray r))
  polySub p r := liftArr (OcamlPq.MLKEM.polySub (ipolyToArray p) (ipolyToArray r))
  encode12 p :=
    natToBytes (Encoding.Mlkem.encode12 (bytesToNat (bufToList g₁₂ 0 384)) (ipolyToList p))
  decode12 s off := (Encoding.Mlkem.decode12 (bytesToNat s) off).map listToIPoly
  encodeCompressed d p := natToBytes (Encoding.Mlkem.encodeCompressed compressNat d (ipolyToList p))
  decodeCompressed d s off :=
    listToIPoly (Encoding.Mlkem.decodeCompressed OcamlPq.MLKEM.decompress d (bytesToNat s) off)

/-- The FIPS 203 building blocks, from the transcriptions of the arithmetic
    and encoding areas. -/
def S₀ : SpecPrims where
  NTT f := restrictPoly (OcamlPq.MLKEM.fipsNtt (extendPoly f))
  invNTT f := restrictPoly (OcamlPq.MLKEM.fipsNttInv (extendPoly f))
  multiplyNTTs f g := restrictPoly (OcamlPq.MLKEM.fipsMultiplyNTTs (extendPoly f) (extendPoly g))
  byteEncode12 f := natToBytes (Encoding.Spec.byteEncode 12 (polyToList f))
  byteDecode12 B := listToPoly (Encoding.Spec.byteDecode 12 (bytesToNat B))
  compressEncode d f :=
    natToBytes (Encoding.Spec.byteEncode d
      (List.ofFn fun i => (OcamlPq.MLKEM.compressSpec d (f i)).toNat))
  decodeDecompress d B := fun i =>
    ((OcamlPq.MLKEM.decompressSpec d
      (((Encoding.Spec.byteDecode d (bytesToNat B)).getD i.val 0 : ℕ) : ℤ) : ℤ) : ZMod q)

/-! ### Unfolding the fields

Stated with `dsimp` rather than `rfl`: a bare `rfl` makes the unifier evaluate
the models on symbolic 256-entry arrays. -/

section Fields

variable (g : ℕ → Byte)

theorem I₀_ntt (p : IPoly) : (I₀ g).ntt p = liftArr (OcamlPq.MLKEM.ntt (ipolyToArray p)) := by
  unfold I₀; dsimp only

theorem I₀_inverseNtt (p : IPoly) :
    (I₀ g).inverseNtt p = liftArr (OcamlPq.MLKEM.inverseNtt (ipolyToArray p)) := by
  unfold I₀; dsimp only

theorem I₀_nttMul (p r : IPoly) :
    (I₀ g).nttMul p r = liftArr (OcamlPq.MLKEM.nttMul (ipolyToArray p) (ipolyToArray r)) := by
  unfold I₀; dsimp only

theorem I₀_polyAdd (p r : IPoly) :
    (I₀ g).polyAdd p r = liftArr (OcamlPq.MLKEM.polyAdd (ipolyToArray p) (ipolyToArray r)) := by
  unfold I₀; dsimp only

theorem I₀_polySub (p r : IPoly) :
    (I₀ g).polySub p r = liftArr (OcamlPq.MLKEM.polySub (ipolyToArray p) (ipolyToArray r)) := by
  unfold I₀; dsimp only

theorem I₀_encode12 (p : IPoly) :
    (I₀ g).encode12 p =
      natToBytes (Encoding.Mlkem.encode12 (bytesToNat (bufToList g 0 384)) (ipolyToList p)) := by
  unfold I₀; dsimp only

theorem I₀_decode12 (s : Bytes) (off : ℕ) :
    (I₀ g).decode12 s off = (Encoding.Mlkem.decode12 (bytesToNat s) off).map listToIPoly := by
  unfold I₀; dsimp only

theorem I₀_encodeCompressed (d : ℕ) (p : IPoly) :
    (I₀ g).encodeCompressed d p =
      natToBytes (Encoding.Mlkem.encodeCompressed compressNat d (ipolyToList p)) := by
  unfold I₀; dsimp only

theorem I₀_decodeCompressed (d : ℕ) (s : Bytes) (off : ℕ) :
    (I₀ g).decodeCompressed d s off =
      listToIPoly (Encoding.Mlkem.decodeCompressed OcamlPq.MLKEM.decompress d (bytesToNat s) off) := by
  unfold I₀; dsimp only

theorem S₀_NTT (f : Poly) : S₀.NTT f = restrictPoly (OcamlPq.MLKEM.fipsNtt (extendPoly f)) := by
  unfold S₀; dsimp only

theorem S₀_invNTT (f : Poly) :
    S₀.invNTT f = restrictPoly (OcamlPq.MLKEM.fipsNttInv (extendPoly f)) := by
  unfold S₀; dsimp only

theorem S₀_multiplyNTTs (f h : Poly) :
    S₀.multiplyNTTs f h =
      restrictPoly (OcamlPq.MLKEM.fipsMultiplyNTTs (extendPoly f) (extendPoly h)) := by
  unfold S₀; dsimp only

theorem S₀_byteEncode12 (f : Poly) :
    S₀.byteEncode12 f = natToBytes (Encoding.Spec.byteEncode 12 (polyToList f)) := by
  unfold S₀; dsimp only

theorem S₀_byteDecode12 (B : Bytes) :
    S₀.byteDecode12 B = listToPoly (Encoding.Spec.byteDecode 12 (bytesToNat B)) := by
  unfold S₀; dsimp only

theorem S₀_compressEncode (d : ℕ) (f : Poly) :
    S₀.compressEncode d f = natToBytes (Encoding.Spec.byteEncode d
      (List.ofFn fun i => (OcamlPq.MLKEM.compressSpec d (f i)).toNat)) := by
  unfold S₀; dsimp only

theorem S₀_decodeDecompress (d : ℕ) (B : Bytes) (i : Fin 256) :
    S₀.decodeDecompress d B i = ((OcamlPq.MLKEM.decompressSpec d
      (((Encoding.Spec.byteDecode d (bytesToNat B)).getD i.val 0 : ℕ) : ℤ) : ℤ) : ZMod q) := by
  unfold S₀; dsimp only

end Fields

/-! ## Facts about `ByteDecode` -/

theorem byteDecode_length (d : ℕ) (B : List ℕ) : (Encoding.Spec.byteDecode d B).length = 256 := by
  simp [Encoding.Spec.byteDecode]

theorem byteDecode_lt (d : ℕ) (B : List ℕ) :
    ∀ x ∈ Encoding.Spec.byteDecode d B, x < Encoding.Spec.byteDecodeModulus d := by
  intro x hx
  rw [Encoding.Spec.byteDecode_eq_map] at hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  apply Nat.mod_lt
  unfold Encoding.Spec.byteDecodeModulus Encoding.Spec.q
  split_ifs <;> positivity

theorem getD_lt_of_forall {l : List ℕ} {m : ℕ} (hm : 0 < m) (h : ∀ x ∈ l, x < m) (i : ℕ) :
    l.getD i 0 < m := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; exact hm

theorem widths_bounds {d : ℕ} (hd : d ∈ Widths) : 1 ≤ d ∧ d ≤ 11 := by
  simp only [Widths, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  omega

/-! ## `Refines (I₀ g₁₂) S₀` -/

section Refines

variable (g₁₂ : ℕ → Byte)

theorem refines_ntt (p : IPoly) (hp : Canonical p) :
    Canonical ((I₀ g₁₂).ntt p) ∧ toSpec ((I₀ g₁₂).ntt p) = S₀.NTT (toSpec p) := by
  obtain ⟨out, e, h⟩ := OcamlPq.MLKEM.ntt_refines (rep_ipolyToArray hp)
  rw [I₀_ntt, S₀_NTT, e]; exact rep_arrayToIPoly h

theorem refines_inverseNtt (p : IPoly) (hp : Canonical p) :
    Canonical ((I₀ g₁₂).inverseNtt p) ∧ toSpec ((I₀ g₁₂).inverseNtt p) = S₀.invNTT (toSpec p) := by
  obtain ⟨out, e, h⟩ := OcamlPq.MLKEM.inverseNtt_refines (rep_ipolyToArray hp)
  rw [I₀_inverseNtt, S₀_invNTT, e]; exact rep_arrayToIPoly h

theorem refines_nttMul (p r : IPoly) (hp : Canonical p) (hr : Canonical r) :
    Canonical ((I₀ g₁₂).nttMul p r) ∧
      toSpec ((I₀ g₁₂).nttMul p r) = S₀.multiplyNTTs (toSpec p) (toSpec r) := by
  obtain ⟨out, e, h⟩ := OcamlPq.MLKEM.nttMul_refines (rep_ipolyToArray hp) (rep_ipolyToArray hr)
  rw [I₀_nttMul, S₀_multiplyNTTs, e]; exact rep_arrayToIPoly h

theorem refines_polyAdd (p r : IPoly) (hp : Canonical p) (hr : Canonical r) :
    Canonical ((I₀ g₁₂).polyAdd p r) ∧ toSpec ((I₀ g₁₂).polyAdd p r) = toSpec p + toSpec r := by
  obtain ⟨out, e, h⟩ := OcamlPq.MLKEM.polyAdd_refines (rep_ipolyToArray hp) (rep_ipolyToArray hr)
  rw [I₀_polyAdd, e, liftArr_some]
  obtain ⟨h1, h2⟩ := rep_arrayToIPoly h
  exact ⟨h1, by rw [h2, restrictPoly_add, restrictPoly_extendPoly, restrictPoly_extendPoly]⟩

theorem refines_polySub (p r : IPoly) (hp : Canonical p) (hr : Canonical r) :
    Canonical ((I₀ g₁₂).polySub p r) ∧ toSpec ((I₀ g₁₂).polySub p r) = toSpec p - toSpec r := by
  obtain ⟨out, e, h⟩ := OcamlPq.MLKEM.polySub_refines (rep_ipolyToArray hp) (rep_ipolyToArray hr)
  rw [I₀_polySub, e, liftArr_some]
  obtain ⟨h1, h2⟩ := rep_arrayToIPoly h
  exact ⟨h1, by rw [h2, restrictPoly_sub, restrictPoly_extendPoly, restrictPoly_extendPoly]⟩

theorem refines_encode12 (p : IPoly) (hp : Canonical p) :
    (I₀ g₁₂).encode12 p = S₀.byteEncode12 (toSpec p) ∧ ((I₀ g₁₂).encode12 p).length = 384 := by
  have hlt : ∀ x ∈ ipolyToList p, x < 2 ^ 12 := fun x hx =>
    lt_trans (ipolyToList_lt hp x hx) (by norm_num)
  have hinit : (bytesToNat (bufToList g₁₂ 0 384)).length = 384 := by simp
  have he := Encoding.Mlkem.encode12_eq_byteEncode (length_ipolyToList p) hlt hinit
  have hl := Encoding.Mlkem.length_encode12 (f := ipolyToList p) hinit
  rw [I₀_encode12, S₀_byteEncode12]
  refine ⟨?_, ?_⟩
  · rw [he, ipolyToList_eq_polyToList hp]
  · rw [length_natToBytes, hl]

theorem refines_decode12 (s : Bytes) (off : ℕ) (hoff : off + 384 ≤ s.length) :
    (∀ p, (I₀ g₁₂).decode12 s off = some p →
      Canonical p ∧ toSpec p = S₀.byteDecode12 (stringSub s off 384)) ∧
    (((I₀ g₁₂).decode12 s off).isSome ↔
      S₀.byteEncode12 (S₀.byteDecode12 (stringSub s off 384)) = stringSub s off 384) := by
  have hoff' : off + 384 ≤ (bytesToNat s).length := by simpa using hoff
  have hiff := Encoding.Mlkem.decode12_eq_some_iff (bytesToNat_lt s) hoff'
  rw [← bytesToNat_stringSub] at hiff
  set B := stringSub s off 384 with hB
  set D := Encoding.Spec.byteDecode 12 (bytesToNat B) with hD
  have hDlen : D.length = 256 := byteDecode_length _ _
  have hDlt : ∀ x ∈ D, x < 3329 := byteDecode_lt 12 _
  have hSE : S₀.byteEncode12 (S₀.byteDecode12 B) = natToBytes (Encoding.Spec.byteEncode 12 D) := by
    rw [S₀_byteDecode12, S₀_byteEncode12, ← hD, polyToList_listToPoly hDlen hDlt]
  have hElt : ∀ x ∈ Encoding.Spec.byteEncode 12 D, x < 256 :=
    (Encoding.Spec.byteEncode_regroup hDlen
      (fun x hx => lt_trans (hDlt x hx) (by norm_num))).right_lt
  have hmod : S₀.byteEncode12 (S₀.byteDecode12 B) = B ↔
      Encoding.Spec.byteEncode 12 D = bytesToNat B := by
    rw [hSE, natToBytes_eq_iff hElt]
  rw [I₀_decode12]
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.1 hp
    obtain ⟨-, rfl⟩ := (hiff F).1 hF
    exact ⟨listToIPoly_canonical hDlt, by rw [toSpec_listToIPoly, S₀_byteDecode12]⟩
  · rw [hmod, Option.isSome_map]
    constructor
    · intro h
      obtain ⟨F, hF⟩ := Option.isSome_iff_exists.1 h
      exact ((hiff F).1 hF).1
    · intro h
      rw [(hiff D).2 ⟨h, rfl⟩]; rfl

theorem refines_encodeCompressed (d : ℕ) (hd : d ∈ Widths) (p : IPoly) (hp : Canonical p) :
    (I₀ g₁₂).encodeCompressed d p = S₀.compressEncode d (toSpec p) ∧
      ((I₀ g₁₂).encodeCompressed d p).length = 32 * d := by
  have hd' := widths_bounds hd
  have he := Encoding.Mlkem.encodeCompressed_eq compressNat d (ipolyToList p) (length_ipolyToList p)
    (by omega) (compressNat_lt · d)
  have hl := Encoding.Mlkem.length_encodeCompressed compressNat d (ipolyToList p)
    (length_ipolyToList p) (by omega) (compressNat_lt · d)
  have hmap : (ipolyToList p).map (fun x => compressNat x d) =
      List.ofFn fun i => (OcamlPq.MLKEM.compressSpec d (toSpec p i)).toNat := by
    simp only [ipolyToList, List.map_ofFn]
    congr 1; funext i
    simp only [Function.comp, compressNat, toSpec]
    rw [Int.toNat_of_nonneg (hp i).1,
      OcamlPq.MLKEM.compress_eq_spec (canon_of_canonical hp i) (by omega)]
  rw [I₀_encodeCompressed, S₀_compressEncode]
  refine ⟨?_, ?_⟩
  · rw [he, hmap]
  · rw [length_natToBytes, hl]

theorem refines_decodeCompressed (d : ℕ) (hd : d ∈ Widths) (s : Bytes) (off : ℕ)
    (hoff : off + 32 * d ≤ s.length) :
    Canonical ((I₀ g₁₂).decodeCompressed d s off) ∧
      toSpec ((I₀ g₁₂).decodeCompressed d s off) =
        S₀.decodeDecompress d (stringSub s off (32 * d)) := by
  have hd' := widths_bounds hd
  have hin : off + 32 * d ≤ (bytesToNat s).length := by simpa using hoff
  have he := Encoding.Mlkem.decodeCompressed_eq OcamlPq.MLKEM.decompress d (bytesToNat s) off
    hd'.1 (by omega) hin (bytesToNat_lt s)
  rw [← bytesToNat_stringSub] at he
  set D := Encoding.Spec.byteDecode d (bytesToNat (stringSub s off (32 * d))) with hD
  have hDlen : D.length = 256 := byteDecode_length _ _
  have hmodd : Encoding.Spec.byteDecodeModulus d = 2 ^ d := by
    simp [Encoding.Spec.byteDecodeModulus, show d < 12 by omega]
  have hDlt : ∀ i, D.getD i 0 < 2 ^ d := fun i =>
    getD_lt_of_forall (by positivity) (by rw [← hmodd]; exact byteDecode_lt d _) i
  have hval : ∀ i : Fin 256, (I₀ g₁₂).decodeCompressed d s off i =
      ((OcamlPq.MLKEM.decompress (D.getD i.val 0) d : ℕ) : ℤ) := by
    intro i
    rw [I₀_decodeCompressed, he]
    simp only [listToIPoly]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hDlen]; exact i.isLt), List.getElem_map,
      List.getD_eq_getElem _ _ (by rw [hDlen]; exact i.isLt)]
  refine ⟨fun i => ?_, funext fun i => ?_⟩
  · rw [hval]
    have := OcamlPq.MLKEM.decompress_lt_q (D.getD i.val 0) d hd'.1 (by omega) (hDlt _)
    exact ⟨by positivity, by show _ < ((3329 : ℕ) : ℤ); exact_mod_cast this⟩
  · simp only [toSpec]
    rw [hval, S₀_decodeDecompress, ← hD, OcamlPq.MLKEM.decompress_eq_spec _ _ hd'.1]

/-- **The building blocks refine FIPS 203.** The arithmetic and encoding
    models of lib/mlkem_engine.ml satisfy every refinement fact that the
    composition proofs of `MLKEMAlg` assume, for every content of the
    uninitialised buffer of `encode_12`. -/
theorem refines : Refines (I₀ g₁₂) S₀ where
  ntt := refines_ntt g₁₂
  inverseNtt := refines_inverseNtt g₁₂
  nttMul := refines_nttMul g₁₂
  polyAdd := refines_polyAdd g₁₂
  polySub := refines_polySub g₁₂
  encode12 := refines_encode12 g₁₂
  decode12 := refines_decode12 g₁₂
  encodeCompressed := refines_encodeCompressed g₁₂
  decodeCompressed := refines_decodeCompressed g₁₂

/-- The result of `encode_12` does not depend on its uninitialised buffer
    (on canonical inputs, the only ones the code passes). -/
theorem I₀_encode12_indep (g g' : ℕ → Byte) (p : IPoly) (hp : Canonical p) :
    (I₀ g).encode12 p = (I₀ g').encode12 p := by
  rw [(refines_encode12 g p hp).1, (refines_encode12 g' p hp).1]

end Refines

/-! ## `S₀.Laws` -/

open OcamlPq.MLKEM (EqOn256 fipsNtt fipsNttInv fipsMultiplyNTTs fipsNtt_add fipsNtt_fipsNttInv
  fipsNttInv_fipsNtt fipsNtt_congr fipsNttInv_congr fipsMultiplyNTTs_pair)

theorem invNTT_add (f g : Poly) : S₀.invNTT (f + g) = S₀.invNTT f + S₀.invNTT g := by
  rw [S₀_invNTT, S₀_invNTT, S₀_invNTT, ← restrictPoly_add]
  apply restrictPoly_congr
  set a := fipsNttInv (extendPoly f)
  set b := fipsNttInv (extendPoly g)
  have h1 : EqOn256 (extendPoly (f + g)) (fipsNtt (a + b)) := by
    intro p hp
    rw [fipsNtt_add a b p hp, extendPoly_add, Pi.add_apply, Pi.add_apply,
      fipsNtt_fipsNttInv _ p hp, fipsNtt_fipsNttInv _ p hp]
  intro p hp
  rw [fipsNttInv_congr h1 p hp, fipsNttInv_fipsNtt _ p hp]

theorem byteDecode12_byteEncode12 (f : Poly) : S₀.byteDecode12 (S₀.byteEncode12 f) = f := by
  rw [S₀_byteEncode12, S₀_byteDecode12]
  have hc : Encoding.Mlkem.Canonical (polyToList f) := ⟨length_polyToList f, polyToList_lt f⟩
  rw [bytesToNat_natToBytes (Encoding.Mlkem.byteEncode12_lt hc),
    Encoding.Mlkem.byteDecode_byteEncode_12 hc, listToPoly_polyToList]

/-- NTT⁻¹ is additive and ByteDecode₁₂ ∘ ByteEncode₁₂ = id. -/
theorem laws : S₀.Laws := ⟨invNTT_add, byteDecode12_byteEncode12⟩

/-! ## `S₀.AlgLaws` -/

theorem NTT_add (f g : Poly) : S₀.NTT (f + g) = S₀.NTT f + S₀.NTT g := by
  rw [S₀_NTT, S₀_NTT, S₀_NTT, extendPoly_add, ← restrictPoly_add]
  exact restrictPoly_congr (fipsNtt_add _ _)

theorem NTT_invNTT (f : Poly) : S₀.NTT (S₀.invNTT f) = f := by
  rw [S₀_invNTT, S₀_NTT]
  conv_rhs => rw [← restrictPoly_extendPoly f]
  apply restrictPoly_congr
  intro p hp
  rw [fipsNtt_congr (extendPoly_restrictPoly _) p hp, fipsNtt_fipsNttInv _ p hp]

/-- Pair `i` of `MultiplyNTTs`, as the two coefficients of the product in
    `ℤ_q[X]/(X² − γ_i)`. -/
theorem mul_pair (F G : OcamlPq.MLKEM.Poly) {i : ℕ} (hi : i < 128) :
    fipsMultiplyNTTs F G (2 * i) =
        F (2 * i) * G (2 * i) + F (2 * i + 1) * G (2 * i + 1) * OcamlPq.MLKEM.gamma i ∧
      fipsMultiplyNTTs F G (2 * i + 1) = F (2 * i) * G (2 * i + 1) + F (2 * i + 1) * G (2 * i) :=
  fipsMultiplyNTTs_pair F G hi

theorem mul_comm' (a b : Poly) : S₀.multiplyNTTs a b = S₀.multiplyNTTs b a := by
  rw [S₀_multiplyNTTs, S₀_multiplyNTTs]
  apply restrictPoly_congr
  intro p hp
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' p
  · have hi : i < 128 := by omega
    rw [(mul_pair _ _ hi).1, (mul_pair _ _ hi).1]; ring
  · have hi : i < 128 := by omega
    rw [(mul_pair _ _ hi).2, (mul_pair _ _ hi).2]; ring

theorem mul_assoc' (a b c : Poly) :
    S₀.multiplyNTTs (S₀.multiplyNTTs a b) c = S₀.multiplyNTTs a (S₀.multiplyNTTs b c) := by
  simp only [S₀_multiplyNTTs]
  apply restrictPoly_congr
  set A := extendPoly a
  set B := extendPoly b
  set C := extendPoly c
  have hX := extendPoly_restrictPoly (fipsMultiplyNTTs A B)
  have hY := extendPoly_restrictPoly (fipsMultiplyNTTs B C)
  intro p hp
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' p
  · have hi : i < 128 := by omega
    rw [(mul_pair _ _ hi).1, (mul_pair _ _ hi).1, hX _ (by omega), hX _ (by omega),
      hY _ (by omega), hY _ (by omega), (mul_pair _ _ hi).1, (mul_pair _ _ hi).2,
      (mul_pair B C hi).1, (mul_pair B C hi).2]
    ring
  · have hi : i < 128 := by omega
    rw [(mul_pair _ _ hi).2, (mul_pair _ _ hi).2, hX _ (by omega), hX _ (by omega),
      hY _ (by omega), hY _ (by omega), (mul_pair _ _ hi).1, (mul_pair _ _ hi).2,
      (mul_pair B C hi).1, (mul_pair B C hi).2]
    ring

theorem mul_add' (a b c : Poly) :
    S₀.multiplyNTTs a (b + c) = S₀.multiplyNTTs a b + S₀.multiplyNTTs a c := by
  simp only [S₀_multiplyNTTs]
  rw [extendPoly_add, ← restrictPoly_add]
  apply restrictPoly_congr
  intro p hp
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' p
  · have hi : i < 128 := by omega
    rw [Pi.add_apply, (mul_pair _ _ hi).1, (mul_pair _ _ hi).1, (mul_pair _ _ hi).1]
    simp only [Pi.add_apply]; ring
  · have hi : i < 128 := by omega
    rw [Pi.add_apply, (mul_pair _ _ hi).2, (mul_pair _ _ hi).2, (mul_pair _ _ hi).2]
    simp only [Pi.add_apply]; ring

/-- NTT is an additive bijection with inverse NTT⁻¹, and `MultiplyNTTs` makes
    `T_q` a commutative ring. -/
theorem algLaws : S₀.AlgLaws := ⟨NTT_add, NTT_invNTT, mul_comm', mul_assoc', mul_add'⟩

/-! ## `d = 1`: the two FIPS 203 transcriptions agree

`MLKEMAlg.Correctness` states its final decoding step with its own
transcription of `ByteEncode₁ ∘ Compress₁` and `Decompress₁ ∘ ByteDecode₁`.
These are the same functions as `S₀.compressEncode 1` and
`S₀.decodeDecompress 1`, which are built from the encoding and arithmetic
areas' transcriptions. -/

theorem bitsOfByte_eq (c m : ℕ) :
    Spec.bitsOfByte c m = (List.range m).map (fun i => c / 2 ^ i % 2) := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih =>
    rw [Spec.bitsOfByte, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp, Nat.succ_eq_add_one, pow_succ', Nat.div_div_eq_div_mul]

/-- The two transcriptions of FIPS 203 Algorithm 4 (`BytesToBits`) agree. -/
theorem bytesToBits_eq (m : Bytes) :
    Encoding.Spec.bytesToBits (bytesToNat m) = Spec.bytesToBits m := by
  rw [Encoding.Spec.bytesToBits_eq, Spec.bytesToBits, bytesToNat, List.flatMap_map]
  congr 1; funext c
  rw [bitsOfByte_eq]

theorem decompressD_eq (d y : ℕ) :
    Spec.decompressD d y = ((OcamlPq.MLKEM.decompressSpec d (y : ℤ) : ℤ) : ZMod q) := by
  rw [OcamlPq.MLKEM.decompressSpec_eq_int]
  simp only [Spec.decompressD]
  have : (((2 * q * y + 2 ^ d) / 2 ^ (d + 1) : ℕ) : ℤ) = (2 * (3329 * (y : ℤ)) + 2 ^ d) / (2 * 2 ^ d) := by
    rw [Int.natCast_div]; push_cast
    congr 1 <;> ring
  rw [← this, Int.cast_natCast]

theorem compressD_eq (d : ℕ) (x : ZMod q) :
    Spec.compressD d x = (OcamlPq.MLKEM.compressSpec d x).toNat := by
  rw [OcamlPq.MLKEM.compressSpec_eq_int]
  simp only [Spec.compressD]
  have : (((2 ^ (d + 1) * x.val + q) / (2 * q) % 2 ^ d : ℕ) : ℤ) =
      (2 * (2 ^ d * (x.val : ℤ)) + 3329) / 6658 % 2 ^ d := by
    rw [Int.natCast_mod, Int.natCast_div]; push_cast
    congr 2
    ring
  rw [← this, Int.toNat_natCast]

theorem compressSpec_bounds (d : ℕ) (x : ZMod q) :
    0 ≤ OcamlPq.MLKEM.compressSpec d x ∧ OcamlPq.MLKEM.compressSpec d x < 2 ^ d := by
  unfold OcamlPq.MLKEM.compressSpec
  exact ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩

/-- `S₀.decodeDecompress 1` is `Decompress₁ ∘ ByteDecode₁` as transcribed in
    `MLKEMAlg.Correctness`. -/
theorem decodeDecompress_one : S₀.decodeDecompress 1 = Spec.decodeDecompress1 := by
  funext m i
  rw [S₀_decodeDecompress, Spec.decodeDecompress1, decompressD_eq]
  congr 3
  simp only [Spec.byteDecode1, Encoding.Spec.byteDecode]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  simp only [Finset.range_one, Finset.sum_singleton, mul_one, add_zero, pow_zero,
    Encoding.Spec.byteDecodeModulus, bytesToBits_eq]
  have hb : ∀ x ∈ Spec.bytesToBits m, x < 2 := by
    intro x hx
    rw [Spec.bytesToBits, List.mem_flatMap] at hx
    obtain ⟨c, -, hc⟩ := hx
    rw [bitsOfByte_eq, List.mem_map] at hc
    obtain ⟨j, -, rfl⟩ := hc
    exact Nat.mod_lt _ (by norm_num)
  have := getD_lt_of_forall (by norm_num) hb i.val
  rw [List.getD_eq_getElem?_getD] at this
  norm_num
  omega

/-- `S₀.compressEncode 1` is `ByteEncode₁ ∘ Compress₁` as transcribed in
    `MLKEMAlg.Correctness`. -/
theorem compressEncode_one : S₀.compressEncode 1 = Spec.compressEncode1 := by
  funext w
  set F' : List ℕ := List.ofFn fun i => (OcamlPq.MLKEM.compressSpec 1 (w i)).toNat with hF'
  have hF'len : F'.length = 256 := by rw [hF', List.length_ofFn]
  have hF'lt : ∀ x ∈ F', x < 2 := by
    intro x hx
    rw [hF', List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    have := compressSpec_bounds 1 (w i)
    omega
  have hreg := Encoding.Spec.byteEncode_regroup (d := 1) hF'len (by simpa using hF'lt)
  rw [S₀_compressEncode, ← hF', natToBytes_eq_iff hreg.right_lt]
  have hchunk := (Encoding.regroup_chunks (c := 8) (N := 32) hF'lt (by rw [hF'len])).symm
  refine Encoding.Regroup.right_unique (by norm_num) hreg ?_
  convert hchunk using 1
  -- the bytes of the `MLKEMAlg` transcription are the 8-bit chunks
  apply List.ext_getElem (by simp [bytesToNat, Spec.compressEncode1, Spec.byteEncode1])
  intro k h1 h2
  have hk : k < 32 := by simpa using h2
  simp only [bytesToNat, Spec.compressEncode1, Spec.byteEncode1, List.getElem_map,
    List.getElem_ofFn, List.getElem_range]
  rw [Encoding.Spec.sum_bits_eq_ofDigits]
  have hbits : (List.range 8).map (fun j =>
      (if h : 8 * k + j < 256 then Spec.compressD 1 (w ⟨8 * k + j, h⟩) else 0) % 2) =
      (List.range 8).map (fun t => F'.getD (k * 8 + t) 0) := by
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    have hi : 8 * k + j < 256 := by omega
    rw [show k * 8 + j = 8 * k + j by ring]
    simp only [hi, ↓reduceDIte]
    rw [compressD_eq, hF', List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega),
      List.getElem_ofFn]
    have := compressSpec_bounds 1 (w ⟨8 * k + j, hi⟩)
    omega
  rw [hbits]
  apply Nat.mod_eq_of_lt
  have := Encoding.ofDigits_two_lt (l := (List.range 8).map (fun t => F'.getD (k * 8 + t) 0))
    (by
      intro x hx
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
      exact getD_lt_of_forall (by norm_num) hF'lt _)
  simpa using this

end OcamlPq.EndToEnd.MLKEM
