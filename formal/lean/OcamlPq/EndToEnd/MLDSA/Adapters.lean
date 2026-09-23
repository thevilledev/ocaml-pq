import OcamlPq.MLDSAAlg
import OcamlPq.MLDSA
import OcamlPq.Encoding
import OcamlPq.Hash

/-!
# Representation adapters between the ML-DSA areas

The four areas that verify ML-DSA model the same OCaml values with different
Lean types. This file defines the conversions used to plug them into each
other. Each adapter only re-indexes, re-types or truncates a value; none
computes anything the OCaml code computes.

| OCaml value | `MLDSAAlg` | `MLDSA` (arithmetic) | `Encoding` | `Hash` |
|---|---|---|---|---|
| `poly = int array` (256 entries) | `Poly = ℕ → ℤ` | `ℕ → ℤ` | `List ℤ` / `List ℕ` | – |
| spec polynomial in `R_q` | `Poly` (see below) | `ℕ → ZMod q` | – | – |
| `polyvec = poly array` | `PolyVec = ℕ → Poly` | – | `List (List ℤ)` | – |
| hint vector | `PolyVec` | – | `HintVec = ℕ → ℕ → ℕ` | – |
| `string` of bytes | `Bytes = List (Fin 256)` | – | `List ℕ` | `List UInt8` |

Adapters (all documented at their definitions):

* `trunc p` zeroes the indices `≥ 256` of an index function. An OCaml `poly`
  has exactly 256 entries, so two index functions that agree below 256 model
  the same array; `trunc` picks the representative that is `0` elsewhere. It
  is applied to the outputs of the functions whose models leave arbitrary
  values at indices `≥ 256` (`inverse_ntt`, and the FIPS `NTT⁻¹`).
* `toZq p i = (p i : ℤ_q)` (the arithmetic area's `castArr`) and
  `ofZq w i = (w i).val` (the representative in `[0, q)`). A FIPS 204
  polynomial in `R_q` is represented in `MLDSAAlg`'s `Poly = ℕ → ℤ` by its
  canonical representatives; `ofZq ∘ toZq` is reduction modulo `q`.
* `polyToList p = [p 0, …, p 255]`, `polyToNatList p` the same read in `ℕ`
  (`Int.toNat`, exact on the non-negative arrays where it is used),
  `listToPoly l i = l[i]` (0 out of range), `natListToPoly`, and the vector
  versions `vecToLists`, `listsToVec`.
* `natToBytes l = l.map byteOfNat` (`byteOfNat x = x mod 256`, the identity on
  the byte values `< 256` the Encoding area produces) and
  `bytesToNat s = s.map Fin.val`.
* `byteToU8`, `u8ToByte`: `Fin 256` versus `UInt8`.
-/

namespace OcamlPq.EndToEnd.MLDSA

open OcamlPq.MLDSAAlg

/-! ## Bytes -/

/-- An Encoding-area byte string (`List ℕ`, entries `< 256`) as `MLDSAAlg.Bytes`. -/
def natToBytes (l : List ℕ) : Bytes := l.map byteOfNat

/-- An `MLDSAAlg.Bytes` string as an Encoding-area byte string. -/
def bytesToNat (s : Bytes) : List ℕ := s.map Fin.val

@[simp] theorem natToBytes_bytesToNat (s : Bytes) : natToBytes (bytesToNat s) = s := by
  unfold natToBytes bytesToNat
  rw [List.map_map]
  conv_rhs => rw [← List.map_id s]
  apply List.map_congr_left
  intro x _
  exact Fin.ext (byteOfNat_val_of_lt x.isLt)

theorem bytesToNat_natToBytes {l : List ℕ} (h : ∀ x ∈ l, x < 256) :
    bytesToNat (natToBytes l) = l := by
  unfold natToBytes bytesToNat
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  exact byteOfNat_val_of_lt (h x hx)

@[simp] theorem length_natToBytes (l : List ℕ) : (natToBytes l).length = l.length := by
  simp [natToBytes]

@[simp] theorem length_bytesToNat (s : Bytes) : (bytesToNat s).length = s.length := by
  simp [bytesToNat]

theorem bytesToNat_lt (s : Bytes) : ∀ x ∈ bytesToNat s, x < 256 := by
  intro x hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  exact b.isLt

@[simp] theorem natToBytes_append (a b : List ℕ) :
    natToBytes (a ++ b) = natToBytes a ++ natToBytes b := by simp [natToBytes]

@[simp] theorem bytesToNat_append (a b : Bytes) :
    bytesToNat (a ++ b) = bytesToNat a ++ bytesToNat b := by simp [bytesToNat]

theorem natToBytes_flatten (L : List (List ℕ)) :
    natToBytes L.flatten = (L.map natToBytes).flatten := by
  simp only [natToBytes, List.map_flatten]; rfl

theorem bytesToNat_take (s : Bytes) (m : ℕ) : bytesToNat (s.take m) = (bytesToNat s).take m := by
  simp [bytesToNat, List.map_take]

theorem bytesToNat_drop (s : Bytes) (m : ℕ) : bytesToNat (s.drop m) = (bytesToNat s).drop m := by
  simp [bytesToNat, List.map_drop]

theorem natToBytes_take (s : List ℕ) (m : ℕ) : natToBytes (s.take m) = (natToBytes s).take m := by
  simp [natToBytes, List.map_take]

theorem natToBytes_drop (s : List ℕ) (m : ℕ) : natToBytes (s.drop m) = (natToBytes s).drop m := by
  simp [natToBytes, List.map_drop]

/-- `Fin 256` as the Hash area's `UInt8`. -/
def byteToU8 (x : Byte) : UInt8 := UInt8.ofNat x.val

/-- The Hash area's `UInt8` as a `Fin 256` byte. -/
def u8ToByte (x : UInt8) : Byte := byteOfNat x.toNat

/-- An `MLDSAAlg` byte string as the Hash area's `List UInt8`. -/
def bytesToU8 (s : Bytes) : List UInt8 := s.map byteToU8

/-- The Hash area's `List UInt8` as an `MLDSAAlg` byte string. -/
def u8ToBytes (s : List UInt8) : Bytes := s.map u8ToByte

@[simp] theorem u8ToByte_byteToU8 (x : Byte) : u8ToByte (byteToU8 x) = x := by
  apply Fin.ext
  simp only [u8ToByte, byteToU8, byteOfNat, UInt8.toNat_ofNat']
  have := x.isLt
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt this]

@[simp] theorem byteToU8_u8ToByte (x : UInt8) : byteToU8 (u8ToByte x) = x := by
  have h := x.toNat_lt
  simp only [byteToU8, u8ToByte, byteOfNat]
  rw [Nat.mod_eq_of_lt (by simpa using h)]
  exact UInt8.ofNat_toNat

@[simp] theorem bytesToU8_u8ToBytes (s : List UInt8) : bytesToU8 (u8ToBytes s) = s := by
  simp [bytesToU8, u8ToBytes, Function.comp_def]

@[simp] theorem u8ToBytes_bytesToU8 (s : Bytes) : u8ToBytes (bytesToU8 s) = s := by
  simp [bytesToU8, u8ToBytes, Function.comp_def]

/-! ## Polynomials -/

/-- **Adapter.** Zero the indices `≥ 256` (an OCaml `poly` has 256 entries). -/
def trunc (p : Poly) : Poly := fun i => if i < 256 then p i else 0

theorem trunc_of_lt {p : Poly} {i : ℕ} (h : i < 256) : trunc p i = p i := by simp [trunc, h]

theorem trunc_of_ge {p : Poly} {i : ℕ} (h : 256 ≤ i) : trunc p i = 0 := by
  simp [trunc, show ¬ i < 256 by omega]

/-- **Adapter.** Coefficients as residues (`MLDSA.castArr`). -/
def toZq (p : Poly) : ℕ → MLDSA.Zq := MLDSA.castArr p

/-- **Adapter.** A polynomial over `ℤ_q` by its canonical representatives in
    `[0, q)`. -/
def ofZq (w : ℕ → MLDSA.Zq) : Poly := fun i => ((w i).val : ℤ)

theorem ofZq_apply (w : ℕ → MLDSA.Zq) (i : ℕ) : ofZq w i = ((w i).val : ℤ) := rfl

/-- The representative of the residue of `x` is `x mod q`. -/
theorem val_cast (x : ℤ) : (((x : MLDSA.Zq)).val : ℤ) = x % MLDSA.q := by
  rw [ZMod.val_intCast]; rfl

/-- A canonical integer is its own representative. -/
theorem val_cast_of_canonical {x : ℤ} (h0 : 0 ≤ x) (h1 : x < MLDSA.q) :
    (((x : MLDSA.Zq)).val : ℤ) = x := by
  rw [val_cast, Int.emod_eq_of_lt h0 h1]

theorem ofZq_toZq (p : Poly) : ofZq (toZq p) = fun i => p i % MLDSA.q := by
  funext i; exact val_cast (p i)

theorem ofZq_nonneg (w : ℕ → MLDSA.Zq) (i : ℕ) : 0 ≤ ofZq w i := Int.natCast_nonneg _

theorem ofZq_lt (w : ℕ → MLDSA.Zq) (i : ℕ) : ofZq w i < MLDSA.q := by
  unfold ofZq; have := ZMod.val_lt (w i); simp only [MLDSA.q]; omega

/-- An integer array whose residues are `w` and whose entries are canonical is
    `ofZq w`. -/
theorem eq_ofZq {a : Poly} {w : ℕ → MLDSA.Zq} (hcan : ∀ i, 0 ≤ a i ∧ a i < MLDSA.q)
    (hcast : MLDSA.castArr a = w) : a = ofZq w := by
  funext i
  rw [ofZq, ← hcast]
  exact (val_cast_of_canonical (hcan i).1 (hcan i).2).symm

theorem toZq_ofZq (w : ℕ → MLDSA.Zq) : toZq (ofZq w) = w := by
  funext i; simp [toZq, MLDSA.castArr, ofZq]

/-- **Adapter.** The 256 coefficients of an OCaml `poly` as the Encoding
    area's `List ℤ`. -/
def polyToList (p : Poly) : List ℤ := (List.range 256).map p

/-- **Adapter.** The same, for a non-negative array modelled as `List ℕ`
    (`Int.toNat` is exact on the non-negative arrays where it is used). -/
def polyToNatList (p : Poly) : List ℕ := (List.range 256).map fun i => (p i).toNat

/-- **Adapter.** An Encoding-area coefficient list as an index function
    (0 out of range). -/
def listToPoly (l : List ℤ) : Poly := fun i => l.getD i 0

/-- **Adapter.** The same for `List ℕ`. -/
def natListToPoly (l : List ℕ) : Poly := fun i => ((l.getD i 0 : ℕ) : ℤ)

/-- **Adapter.** The first `len` rows of a `polyvec` as `List (List ℤ)`. -/
def vecToLists (len : ℕ) (v : PolyVec) : List (List ℤ) :=
  (List.range len).map fun r => polyToList (v r)

/-- **Adapter.** An Encoding-area `polyvec` as an index function. -/
def listsToVec (L : List (List ℤ)) : PolyVec := fun r => listToPoly (L.getD r [])

@[simp] theorem length_polyToList (p : Poly) : (polyToList p).length = 256 := by
  simp [polyToList]

@[simp] theorem length_polyToNatList (p : Poly) : (polyToNatList p).length = 256 := by
  simp [polyToNatList]

@[simp] theorem length_vecToLists (len : ℕ) (v : PolyVec) : (vecToLists len v).length = len := by
  simp [vecToLists]

theorem polyToList_congr {p p' : Poly} (h : ∀ i < 256, p i = p' i) :
    polyToList p = polyToList p' := by
  unfold polyToList
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

theorem polyToNatList_congr {p p' : Poly} (h : ∀ i < 256, p i = p' i) :
    polyToNatList p = polyToNatList p' := by
  unfold polyToNatList
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

theorem vecToLists_congr {len : ℕ} {v v' : PolyVec} (h : ∀ r < len, ∀ i < 256, v r i = v' r i) :
    vecToLists len v = vecToLists len v' := by
  unfold vecToLists
  apply List.map_congr_left
  intro r hr
  exact polyToList_congr (h r (List.mem_range.mp hr))

theorem listToPoly_polyToList (p : Poly) (i : ℕ) (hi : i < 256) :
    listToPoly (polyToList p) i = p i := by
  simp [listToPoly, polyToList, List.getD_eq_getElem?_getD, hi]

theorem listToPoly_polyToList_trunc (p : Poly) : listToPoly (polyToList p) = trunc p := by
  funext i
  by_cases hi : i < 256
  · rw [listToPoly_polyToList p i hi, trunc_of_lt hi]
  · simp [listToPoly, polyToList, List.getD_eq_getElem?_getD, trunc, hi]

theorem polyToList_listToPoly {l : List ℤ} (hl : l.length = 256) :
    polyToList (listToPoly l) = l := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp [polyToList, listToPoly, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem vecToLists_listsToVec {L : List (List ℤ)} {len : ℕ} (hL : L.length = len)
    (hp : ∀ p ∈ L, p.length = 256) : vecToLists len (listsToVec L) = L := by
  apply List.ext_getElem (by simp [hL])
  intro r h1 h2
  simp only [vecToLists, List.getElem_map, List.getElem_range, listsToVec]
  rw [List.getD_eq_getElem _ _ h2]
  exact polyToList_listToPoly (hp _ (List.getElem_mem h2))

theorem mem_polyToList {p : Poly} {x : ℤ} : x ∈ polyToList p ↔ ∃ i < 256, p i = x := by
  simp [polyToList]

theorem mem_vecToLists {len : ℕ} {v : PolyVec} {p : List ℤ} :
    p ∈ vecToLists len v ↔ ∃ r < len, polyToList (v r) = p := by
  simp [vecToLists]

end OcamlPq.EndToEnd.MLDSA
