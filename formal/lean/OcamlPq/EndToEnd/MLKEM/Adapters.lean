import OcamlPq.MLKEMAlg
import OcamlPq.MLKEM
import OcamlPq.Encoding
import OcamlPq.Hash

/-!
# Representation adapters between the ML-KEM areas

The four areas that verify ML-KEM chose different Lean representations of the
same OCaml values. This file defines the conversions used to plug them into
each other. Each adapter only re-indexes or re-types a value; none computes
anything. The lemmas below state the round trips on the values that actually
occur.

| OCaml value | `MLKEMAlg` | `MLKEM` (arithmetic) | `Encoding` | `Hash` |
|---|---|---|---|---|
| `poly = int array` | `IPoly = Fin 256 → ℤ` | `Array ℤ` | `List ℕ` | – |
| spec polynomial | `Poly = Fin 256 → ZMod q` | `MLKEM.Poly = ℕ → Zq` | `List ℕ` (values in `[0, m)`) | – |
| `string` of bytes | `Bytes = List (Fin 256)` | – | `List ℕ` | `List UInt8` |

Adapters:

* `ipolyToArray p = Array.ofFn p`, `arrayToIPoly a = fun i => a[i]` (with 0
  out of range; only arrays of size 256 occur).
* `ipolyToList p = [p 0, …, p 255]` read in `ℕ` (`Int.toNat`). The Encoding
  area models an `int array` of non-negative values as `List ℕ`; on the
  canonical arrays the code passes (`0 ≤ p i < q`) `Int.toNat` is the identity.
  `listToIPoly l = fun i => l[i]` (with 0 out of range).
* `extendPoly f` extends `f : Fin 256 → ZMod q` to `ℕ → ZMod q` by 0;
  `restrictPoly g` restricts to indices `< 256`. The FIPS transcriptions of
  the arithmetic area only read and write indices `< 256`.
* `polyToList f = [f 0, …, f 255]` as `ZMod.val`s (the representatives in
  `[0, q)` that FIPS 203 Algorithm 5 takes as input); `listToPoly l` casts the
  entries into `ZMod q`.
* `bytesToNat s = s.map Fin.val`; `natToBytes l = l.map Spec.byte`, where
  `Spec.byte x = x mod 256`. Every list of `ℕ` that the Encoding area returns as
  bytes has entries below 256 (`natToBytes_eq_iff`, `bytesToNat_natToBytes`),
  so `natToBytes` is the identity on it.
-/

namespace OcamlPq.EndToEnd.MLKEM

open OcamlPq.MLKEMAlg

/-! ## Bytes -/

/-- An `MLKEMAlg` byte string as an `Encoding` byte string. -/
def bytesToNat (s : Bytes) : List ℕ := s.map Fin.val

/-- An `Encoding` byte string (entries below 256) as an `MLKEMAlg` byte string. -/
def natToBytes (l : List ℕ) : Bytes := l.map Spec.byte

@[simp] theorem length_bytesToNat (s : Bytes) : (bytesToNat s).length = s.length := by
  simp [bytesToNat]

@[simp] theorem length_natToBytes (l : List ℕ) : (natToBytes l).length = l.length := by
  simp [natToBytes]

theorem bytesToNat_lt (s : Bytes) : ∀ x ∈ bytesToNat s, x < 256 := by
  intro x hx
  simp only [bytesToNat, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  exact b.isLt

theorem bytesToNat_natToBytes {l : List ℕ} (h : ∀ x ∈ l, x < 256) :
    bytesToNat (natToBytes l) = l := by
  simp only [bytesToNat, natToBytes, List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  simp [Spec.byte, Nat.mod_eq_of_lt (h x hx)]

@[simp] theorem natToBytes_bytesToNat (s : Bytes) : natToBytes (bytesToNat s) = s := by
  simp only [bytesToNat, natToBytes, List.map_map]
  conv_rhs => rw [← List.map_id s]
  apply List.map_congr_left
  intro x _
  ext; simp [Spec.byte, Nat.mod_eq_of_lt x.isLt]

theorem bytesToNat_injective : Function.Injective bytesToNat := by
  intro a b h
  rw [← natToBytes_bytesToNat a, h, natToBytes_bytesToNat]

theorem natToBytes_eq_iff {l : List ℕ} (h : ∀ x ∈ l, x < 256) (s : Bytes) :
    natToBytes l = s ↔ l = bytesToNat s := by
  constructor
  · rintro rfl; rw [bytesToNat_natToBytes h]
  · rintro rfl; exact natToBytes_bytesToNat s

theorem bytesToNat_stringSub (s : Bytes) (off len : ℕ) :
    bytesToNat (stringSub s off len) = Encoding.sub (bytesToNat s) off len := by
  simp [bytesToNat, stringSub, Encoding.sub, List.map_drop, List.map_take]

/-! ## Implementation polynomials -/

/-- `IPoly` as the `Array ℤ` of the arithmetic area. -/
def ipolyToArray (p : IPoly) : Array ℤ := Array.ofFn p

/-- An `Array ℤ` of the arithmetic area as an `IPoly` (entry `i`, 0 out of range). -/
def arrayToIPoly (a : Array ℤ) : IPoly := fun i => a[i.val]?.getD 0

/-- The result of an arithmetic-area model: `some a` if every array access was
    in bounds (which `ntt_refines` etc. prove for canonical inputs). The `none`
    branch is never taken on the inputs the refinement theorems are about. -/
def liftArr : Option (Array ℤ) → IPoly
  | some a => arrayToIPoly a
  | none => polyZero

@[simp] theorem liftArr_some (a : Array ℤ) : liftArr (some a) = arrayToIPoly a := rfl

/-- `IPoly` as the `List ℕ` of the Encoding area. -/
def ipolyToList (p : IPoly) : List ℕ := List.ofFn fun i => (p i).toNat

/-- A `List ℕ` of the Encoding area as an `IPoly` (entry `i`, 0 out of range). -/
def listToIPoly (l : List ℕ) : IPoly := fun i => ((l.getD i.val 0 : ℕ) : ℤ)

@[simp] theorem length_ipolyToList (p : IPoly) : (ipolyToList p).length = 256 := by
  simp only [ipolyToList, List.length_ofFn]

/-! ## Spec polynomials -/

/-- A spec polynomial as the `ℕ → ℤ_q` of the arithmetic area (0 beyond 255). -/
def extendPoly (f : Poly) : OcamlPq.MLKEM.Poly := fun n => if h : n < 256 then f ⟨n, h⟩ else 0

/-- The first 256 entries of an arithmetic-area polynomial. -/
def restrictPoly (g : OcamlPq.MLKEM.Poly) : Poly := fun i => g i.val

/-- The coefficients of a spec polynomial as their representatives in `[0, q)`. -/
def polyToList (f : Poly) : List ℕ := List.ofFn fun i => (f i).val

/-- A list of naturals as a spec polynomial (entry `i`, 0 out of range). -/
def listToPoly (l : List ℕ) : Poly := fun i => ((l.getD i.val 0 : ℕ) : ZMod q)

@[simp] theorem restrictPoly_extendPoly (f : Poly) : restrictPoly (extendPoly f) = f := by
  funext i; simp [restrictPoly, extendPoly, i.isLt]

theorem extendPoly_restrictPoly (g : OcamlPq.MLKEM.Poly) :
    OcamlPq.MLKEM.EqOn256 (extendPoly (restrictPoly g)) g := by
  intro p hp; simp [extendPoly, restrictPoly, hp]

theorem restrictPoly_congr {g h : OcamlPq.MLKEM.Poly} (hgh : OcamlPq.MLKEM.EqOn256 g h) :
    restrictPoly g = restrictPoly h := by
  funext i; exact hgh i.val i.isLt

theorem extendPoly_add (f g : Poly) : extendPoly (f + g) = extendPoly f + extendPoly g := by
  funext n; simp only [extendPoly, Pi.add_apply]; split_ifs <;> simp

@[simp] theorem restrictPoly_add (g h : OcamlPq.MLKEM.Poly) :
    restrictPoly (g + h) = restrictPoly g + restrictPoly h := rfl

@[simp] theorem restrictPoly_sub (g h : OcamlPq.MLKEM.Poly) :
    restrictPoly (g - h) = restrictPoly g - restrictPoly h := rfl

@[simp] theorem length_polyToList (f : Poly) : (polyToList f).length = 256 := by
  simp only [polyToList, List.length_ofFn]

theorem polyToList_lt (f : Poly) : ∀ x ∈ polyToList f, x < 3329 := by
  intro x hx
  simp only [polyToList, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact ZMod.val_lt (f i)

@[simp] theorem listToPoly_polyToList (f : Poly) : listToPoly (polyToList f) = f := by
  funext i
  simp only [listToPoly, polyToList]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  exact ZMod.natCast_zmod_val (f i)

theorem polyToList_listToPoly {l : List ℕ} (hl : l.length = 256) (h : ∀ x ∈ l, x < 3329) :
    polyToList (listToPoly l) = l := by
  apply List.ext_getElem (by rw [length_polyToList, hl])
  intro i h1 h2
  simp only [polyToList, listToPoly, List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ h2, ZMod.val_natCast, Nat.mod_eq_of_lt (h _ (List.getElem_mem h2))]

/-! ## Canonical coefficients -/

theorem canon_of_canonical {p : IPoly} (hp : Canonical p) (i : Fin 256) :
    OcamlPq.MLKEM.Canon (p i) := by
  have := hp i
  unfold OcamlPq.MLKEM.Canon OcamlPq.MLKEM.q
  exact ⟨this.1, by simpa using this.2⟩

theorem canonical_of_canon {p : IPoly} (h : ∀ i, OcamlPq.MLKEM.Canon (p i)) : Canonical p := by
  intro i
  have := h i
  unfold OcamlPq.MLKEM.Canon OcamlPq.MLKEM.q at this
  exact ⟨this.1, by simpa using this.2⟩

/-- For a canonical coefficient, `ZMod.val` of its residue is the coefficient. -/
theorem val_intCast_of_canon {z : ℤ} (h0 : 0 ≤ z) (h1 : z < 3329) : ((z : ZMod q)).val = z.toNat := by
  have := ZMod.val_intCast (n := q) z
  rw [Int.emod_eq_of_lt h0 (by simpa using h1)] at this
  omega

theorem ipolyToList_eq_polyToList {p : IPoly} (hp : Canonical p) :
    ipolyToList p = polyToList (toSpec p) := by
  simp only [ipolyToList, polyToList, toSpec]
  congr 1; funext i
  have := hp i
  rw [val_intCast_of_canon this.1 (by simpa using this.2)]

theorem ipolyToList_lt {p : IPoly} (hp : Canonical p) : ∀ x ∈ ipolyToList p, x < 3329 := by
  rw [ipolyToList_eq_polyToList hp]; exact polyToList_lt _

theorem listToIPoly_canonical {l : List ℕ} (h : ∀ x ∈ l, x < 3329) : Canonical (listToIPoly l) := by
  intro i
  simp only [listToIPoly]
  have : l.getD i.val 0 < 3329 := by
    by_cases hi : i.val < l.length
    · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; norm_num
  constructor
  · positivity
  · show ((l.getD i.val 0 : ℕ) : ℤ) < ((3329 : ℕ) : ℤ); exact_mod_cast this

@[simp] theorem toSpec_listToIPoly (l : List ℕ) : toSpec (listToIPoly l) = listToPoly l := by
  funext i; simp [toSpec, listToIPoly, listToPoly]

/-- A canonical `IPoly` as an array represents its residues (`MLKEM.Rep`). -/
theorem rep_ipolyToArray {p : IPoly} (hp : Canonical p) :
    OcamlPq.MLKEM.Rep (ipolyToArray p) (extendPoly (toSpec p)) := by
  refine ⟨Array.size_ofFn, fun i hi => ⟨p ⟨i, hi⟩, ?_, canon_of_canonical hp _, ?_⟩⟩
  · simp [ipolyToArray, hi]
  · simp [extendPoly, hi, toSpec]

/-- An array that represents `G` (`MLKEM.Rep`) is a canonical `IPoly` whose
    residues are the first 256 entries of `G`. -/
theorem rep_arrayToIPoly {a : Array ℤ} {G : OcamlPq.MLKEM.Poly} (h : OcamlPq.MLKEM.Rep a G) :
    Canonical (arrayToIPoly a) ∧ toSpec (arrayToIPoly a) = restrictPoly G := by
  have key : ∀ i : Fin 256, OcamlPq.MLKEM.Canon (arrayToIPoly a i) ∧
      ((arrayToIPoly a i : ℤ) : ZMod q) = G i.val := by
    intro i
    obtain ⟨v, ev, cv, hv⟩ := h.2 i.val i.isLt
    simp only [arrayToIPoly, ev, Option.getD_some]
    exact ⟨cv, hv⟩
  exact ⟨canonical_of_canon fun i => (key i).1, funext fun i => (key i).2⟩

end OcamlPq.EndToEnd.MLKEM
