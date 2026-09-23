import OcamlPq.SLHDSA.Basic
import OcamlPq.SLHDSA.Base2b

/-!
# SLH-DSA: address serialisation and the FIPS 205 ADRS operations

* `address_full` (slhdsa_engine.ml 160–186) is the 32-byte ADRS layout of
  FIPS 205 §4.2 (layer: 4 bytes, tree address: 12 bytes, type: 4 bytes,
  then three 4-byte words).
* `address_compressed` (188–196) is the SHA2 compressed address
  `ADRS_c = ADRS[3] ‖ ADRS[8:16] ‖ ADRS[19] ‖ ADRS[20:32]` of §11.2,
  given `layer < 256` and `type < 256`.
* The ADRS member functions of FIPS 205 §4.3 (`setLayerAddress`,
  `setTreeAddress`, `setTypeAndClear`, `setKeyPairAddress`,
  `setChainAddress`, `setTreeHeight`, `setHashAddress`, `setTreeIndex`)
  are defined on the 32-byte string exactly as in the standard, and the
  corresponding record updates on the code's `address` are proved to
  commute with `address_full`. The specifications of the tree algorithms in
  the other files therefore use the record-level setters `Address.setX`,
  which by the lemmas below *are* the FIPS operations on the encoding.
* `keypair_address` / `subtree_address` / `with_type` are characterised as
  compositions of these setters (which fields they clear).
-/

namespace OcamlPq.SLHDSA

open Base2b

/-! ## Code model of the serialisation -/

namespace Code

/-- `set_u32_be bytes offset value` (lines 160–166): the four bytes written. -/
def setU32BE (value : ℕ) : List ℕ :=
  [(value >>> 24) &&& 0xff, (value >>> 16) &&& 0xff, (value >>> 8) &&& 0xff, value &&& 0xff]

/-- `set_u64_be bytes offset value` (lines 168–176): the eight bytes written,
    `Int64.to_int (Int64.logand (Int64.shift_right_logical value (8*(7-i))) 0xffL)`. -/
def setU64BE (value : BitVec 64) : List ℕ :=
  (List.range 8).map fun i => ((value >>> (8 * (7 - i))) &&& 0xff).toNat

/-- `address_full address` (lines 178–186): a zero-filled 32-byte buffer
    with the layer at 0, the tree at 8 (bytes 4–7 stay zero), and the type,
    keypair, `field1`, `field2` at 16, 20, 24, 28. Written as the
    concatenation of the eight 4-byte slots. -/
def addressFull (a : Address) : List ℕ :=
  setU32BE a.layer ++ [0, 0, 0, 0] ++ setU64BE a.tree ++ setU32BE a.typ ++ setU32BE a.keypair ++
    setU32BE a.field1 ++ setU32BE a.field2

/-- `address_compressed address` (lines 188–196): 22 bytes;
    `Char.unsafe_chr` of the layer and the type keeps their low 8 bits. -/
def addressCompressed (a : Address) : List ℕ :=
  [a.layer % 256] ++ setU64BE a.tree ++ [a.typ % 256] ++ setU32BE a.keypair ++
    setU32BE a.field1 ++ setU32BE a.field2

end Code

/-! ## FIPS 205 ADRS (§4.2, §4.3, §11.2) -/

namespace FipsADRS

/-- `ADRS ← toByte(0, 32)`. -/
def zero : List ℕ := fipsToByte 0 32

/-- `ADRS[off : off + |bs|] ← bs`. -/
def setBytes (adrs : List ℕ) (off : ℕ) (bs : List ℕ) : List ℕ :=
  adrs.take off ++ bs ++ adrs.drop (off + bs.length)

/-- `setLayerAddress(l)`: `ADRS[0:4] ← toByte(l, 4)`. -/
def setLayerAddress (adrs : List ℕ) (l : ℕ) : List ℕ := setBytes adrs 0 (fipsToByte l 4)
/-- `setTreeAddress(t)`: `ADRS[4:16] ← toByte(t, 12)`. -/
def setTreeAddress (adrs : List ℕ) (t : ℕ) : List ℕ := setBytes adrs 4 (fipsToByte t 12)
/-- `setTypeAndClear(Y)`: `ADRS[16:20] ← toByte(Y, 4); ADRS[20:32] ← toByte(0, 12)`. -/
def setTypeAndClear (adrs : List ℕ) (y : ℕ) : List ℕ :=
  setBytes (setBytes adrs 16 (fipsToByte y 4)) 20 (fipsToByte 0 12)
/-- `setKeyPairAddress(i)`: `ADRS[20:24] ← toByte(i, 4)`. -/
def setKeyPairAddress (adrs : List ℕ) (i : ℕ) : List ℕ := setBytes adrs 20 (fipsToByte i 4)
/-- `setChainAddress(i)` / `setTreeHeight(i)`: `ADRS[24:28] ← toByte(i, 4)`. -/
def setChainAddress (adrs : List ℕ) (i : ℕ) : List ℕ := setBytes adrs 24 (fipsToByte i 4)
/-- `setHashAddress(i)` / `setTreeIndex(i)`: `ADRS[28:32] ← toByte(i, 4)`. -/
def setHashAddress (adrs : List ℕ) (i : ℕ) : List ℕ := setBytes adrs 28 (fipsToByte i 4)

/-- §11.2: `ADRS_c = ADRS[3] ‖ ADRS[8:16] ‖ ADRS[19] ‖ ADRS[20:32]`. -/
def compress (adrs : List ℕ) : List ℕ :=
  [adrs.getD 3 0] ++ (adrs.drop 8).take 8 ++ [adrs.getD 19 0] ++ (adrs.drop 20).take 12

end FipsADRS

/-! ## Record-level ADRS operations -/

namespace Address

/-- `setLayerAddress`. -/
def setLayer (l : ℕ) (a : Address) : Address := { a with layer := l }
/-- `setTreeAddress`. -/
def setTree (t : BitVec 64) (a : Address) : Address := { a with tree := t }
/-- `setTypeAndClear`. -/
def setTypeAndClear (y : ℕ) (a : Address) : Address :=
  { a with typ := y, keypair := 0, field1 := 0, field2 := 0 }
/-- `setKeyPairAddress`. -/
def setKeyPair (i : ℕ) (a : Address) : Address := { a with keypair := i }
/-- `setChainAddress` = `setTreeHeight`. -/
def setWord2 (i : ℕ) (a : Address) : Address := { a with field1 := i }
/-- `setHashAddress` = `setTreeIndex`. -/
def setWord3 (i : ℕ) (a : Address) : Address := { a with field2 := i }

/-- All `int` fields fit the 4-byte words (`set_u32_be` writes the value
    exactly). -/
def WellFormed (a : Address) : Prop :=
  a.layer < 2 ^ 32 ∧ a.typ < 2 ^ 32 ∧ a.keypair < 2 ^ 32 ∧ a.field1 < 2 ^ 32 ∧ a.field2 < 2 ^ 32

/-- `with_type typ a` only sets the type (it does *not* clear). -/
theorem withType_eq (t : ℕ) (a : Address) : withType t a = { a with typ := t } := rfl

/-- `keypair_address typ a` = `setTypeAndClear(typ)` followed by
    `setKeyPairAddress(a.getKeyPairAddress())` (clears `field1`, `field2`,
    keeps the keypair). -/
theorem keypairAddress_eq (t : ℕ) (a : Address) :
    keypairAddress t a = setKeyPair a.keypair (setTypeAndClear t a) := rfl

/-- `subtree_address typ a` = `setTypeAndClear(typ)` (clears keypair,
    `field1`, `field2`). -/
theorem subtreeAddress_eq (t : ℕ) (a : Address) :
    subtreeAddress t a = setTypeAndClear t a := rfl

/-- `{ a with field1 = x; field2 = y }` = `setTreeHeight(x)` then
    `setTreeIndex(y)` (or `setChainAddress`/`setHashAddress`). -/
theorem setFields_eq (a : Address) (x y : ℕ) : a.setFields x y = setWord3 y (setWord2 x a) := rfl

end Address

/-! ## Correctness of the serialisation -/

theorem toByteRev_length (x n : ℕ) : (toByteRev x n).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [toByteRev, ih]

theorem toByteRev_getElem (x n i : ℕ) (hi : i < (toByteRev x n).length) :
    (toByteRev x n)[i] = (x >>> (8 * i)) % 256 := by
  induction n generalizing x i with
  | zero => simp [toByteRev] at hi
  | succ n ih =>
    cases i with
    | zero => simp [toByteRev]
    | succ i =>
      simp only [toByteRev, List.getElem_cons_succ]
      rw [ih _ _ (by simp [toByteRev, toByteRev_length] at hi ⊢; omega), ← Nat.shiftRight_add]
      congr 2; ring

theorem fipsToByte_length (x n : ℕ) : (fipsToByte x n).length = n := by
  simp [fipsToByte, toByteRev_length]

/-- `toByte(x, n)` is the big-endian `n`-byte encoding of `x mod 256^n`. -/
theorem fipsToByte_eq (x n : ℕ) :
    fipsToByte x n = (List.range n).map fun i => (x >>> (8 * (n - 1 - i))) % 256 := by
  apply List.ext_getElem
  · simp [fipsToByte, toByteRev_length]
  · intro i h1 h2
    simp only [fipsToByte, List.getElem_reverse, List.getElem_map, List.getElem_range]
    rw [toByteRev_getElem]
    congr 3; simp [toByteRev_length]

theorem land_ff (x : ℕ) : x &&& 0xff = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8

theorem setU32BE_eq (v : ℕ) : Code.setU32BE v = fipsToByte v 4 := by
  rw [fipsToByte_eq]
  simp only [Code.setU32BE, land_ff, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append]
  norm_num

theorem setU64BE_eq (t : BitVec 64) : Code.setU64BE t = fipsToByte t.toNat 8 := by
  rw [fipsToByte_eq]
  unfold Code.setU64BE
  apply List.map_congr_left
  intro i hi
  have h : (0xff : BitVec 64) = BitVec.ofNat 64 (2 ^ 8 - 1) := rfl
  rw [h, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    show (2 ^ 8 - 1) % 2 ^ 64 = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

/-- For a 64-bit tree address, `toByte(t, 12)` is four zero bytes followed
    by the 8-byte encoding written by `set_u64_be`. -/
theorem toByte12_tree (t : BitVec 64) :
    fipsToByte t.toNat 12 = [0, 0, 0, 0] ++ Code.setU64BE t := by
  rw [setU64BE_eq, fipsToByte_eq, fipsToByte_eq]
  have ht := t.isLt
  have hz : ∀ s, 64 ≤ s → t.toNat >>> s = 0 := by
    intro s hs
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) hs))
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  norm_num
  rw [hz 88 (by norm_num), hz 80 (by norm_num), hz 72 (by norm_num), hz 64 (by norm_num)]
  norm_num

/-- **`address_full` is the FIPS 205 §4.2 layout**: layer (4 bytes),
    tree address (12 bytes), type (4), keypair / word 1 (4), chain address
    or tree height / word 2 (4), hash address or tree index / word 3 (4),
    each `toByte`-encoded. -/
theorem addressFull_eq (a : Address) :
    Code.addressFull a =
      fipsToByte a.layer 4 ++ fipsToByte a.tree.toNat 12 ++ fipsToByte a.typ 4 ++
        fipsToByte a.keypair 4 ++ fipsToByte a.field1 4 ++ fipsToByte a.field2 4 := by
  rw [toByte12_tree]
  simp only [Code.addressFull, setU32BE_eq, List.append_assoc, List.cons_append,
    List.nil_append]

theorem addressFull_length (a : Address) : (Code.addressFull a).length = 32 := by
  simp [addressFull_eq, fipsToByte_length]

/-- `zero_address` encodes to `toByte(0, 32)`. -/
theorem addressFull_zero : Code.addressFull Address.zero = FipsADRS.zero := by decide

theorem setBytes_append (A B C B' : List ℕ) (off : ℕ) (hA : A.length = off)
    (hB : B'.length = B.length) :
    FipsADRS.setBytes (A ++ B ++ C) off B' = A ++ B' ++ C := by
  subst hA
  simp [FipsADRS.setBytes, List.drop_append, hB]

/-- `setLayerAddress` on the encoding = updating the record's `layer`. -/
theorem addressFull_setLayer (l : ℕ) (a : Address) :
    Code.addressFull (Address.setLayer l a) =
      FipsADRS.setLayerAddress (Code.addressFull a) l := by
  rw [addressFull_eq, addressFull_eq, FipsADRS.setLayerAddress]
  have := setBytes_append [] (fipsToByte a.layer 4)
    (fipsToByte a.tree.toNat 12 ++ fipsToByte a.typ 4 ++ fipsToByte a.keypair 4 ++
      fipsToByte a.field1 4 ++ fipsToByte a.field2 4) (fipsToByte l 4) 0 rfl
    (by simp [fipsToByte_length])
  simp only [List.append_assoc, List.nil_append] at this ⊢
  rw [this]; rfl

/-- `setTreeAddress` on the encoding = updating the record's `tree`. -/
theorem addressFull_setTree (t : BitVec 64) (a : Address) :
    Code.addressFull (Address.setTree t a) =
      FipsADRS.setTreeAddress (Code.addressFull a) t.toNat := by
  rw [addressFull_eq, addressFull_eq, FipsADRS.setTreeAddress]
  have := setBytes_append (fipsToByte a.layer 4) (fipsToByte a.tree.toNat 12)
    (fipsToByte a.typ 4 ++ fipsToByte a.keypair 4 ++
      fipsToByte a.field1 4 ++ fipsToByte a.field2 4) (fipsToByte t.toNat 12) 4
    (fipsToByte_length _ _) (by simp [fipsToByte_length])
  simp only [List.append_assoc] at this ⊢
  rw [this]; rfl

/-- `setTypeAndClear` on the encoding = setting the record's type and
    clearing keypair, `field1` and `field2`. -/
theorem addressFull_setTypeAndClear (y : ℕ) (a : Address) :
    Code.addressFull (Address.setTypeAndClear y a) =
      FipsADRS.setTypeAndClear (Code.addressFull a) y := by
  rw [addressFull_eq, addressFull_eq, FipsADRS.setTypeAndClear]
  have h1 := setBytes_append (fipsToByte a.layer 4 ++ fipsToByte a.tree.toNat 12)
    (fipsToByte a.typ 4)
    (fipsToByte a.keypair 4 ++ fipsToByte a.field1 4 ++ fipsToByte a.field2 4)
    (fipsToByte y 4) 16 (by simp [fipsToByte_length]) (by simp [fipsToByte_length])
  have h2 := setBytes_append (fipsToByte a.layer 4 ++ fipsToByte a.tree.toNat 12 ++
      fipsToByte y 4)
    (fipsToByte a.keypair 4 ++ fipsToByte a.field1 4 ++ fipsToByte a.field2 4) []
    (fipsToByte 0 12) 20 (by simp [fipsToByte_length]) (by simp [fipsToByte_length])
  simp only [List.append_assoc, List.append_nil] at h1 h2 ⊢
  rw [h1, h2]
  simp only [Address.setTypeAndClear]
  rfl

/-- `setKeyPairAddress` on the encoding = updating the record's keypair. -/
theorem addressFull_setKeyPair (i : ℕ) (a : Address) :
    Code.addressFull (Address.setKeyPair i a) =
      FipsADRS.setKeyPairAddress (Code.addressFull a) i := by
  rw [addressFull_eq, addressFull_eq, FipsADRS.setKeyPairAddress]
  have := setBytes_append (fipsToByte a.layer 4 ++ fipsToByte a.tree.toNat 12 ++
      fipsToByte a.typ 4) (fipsToByte a.keypair 4)
    (fipsToByte a.field1 4 ++ fipsToByte a.field2 4) (fipsToByte i 4) 20
    (by simp [fipsToByte_length]) (by simp [fipsToByte_length])
  simp only [List.append_assoc] at this ⊢
  rw [this]; rfl

/-- `setChainAddress` / `setTreeHeight` = updating the record's `field1`. -/
theorem addressFull_setWord2 (i : ℕ) (a : Address) :
    Code.addressFull (Address.setWord2 i a) =
      FipsADRS.setChainAddress (Code.addressFull a) i := by
  rw [addressFull_eq, addressFull_eq, FipsADRS.setChainAddress]
  have := setBytes_append (fipsToByte a.layer 4 ++ fipsToByte a.tree.toNat 12 ++
      fipsToByte a.typ 4 ++ fipsToByte a.keypair 4) (fipsToByte a.field1 4)
    (fipsToByte a.field2 4) (fipsToByte i 4) 24
    (by simp [fipsToByte_length]) (by simp [fipsToByte_length])
  simp only [List.append_assoc] at this ⊢
  rw [this]; rfl

/-- `setHashAddress` / `setTreeIndex` = updating the record's `field2`. -/
theorem addressFull_setWord3 (i : ℕ) (a : Address) :
    Code.addressFull (Address.setWord3 i a) =
      FipsADRS.setHashAddress (Code.addressFull a) i := by
  rw [addressFull_eq, addressFull_eq, FipsADRS.setHashAddress]
  have := setBytes_append (fipsToByte a.layer 4 ++ fipsToByte a.tree.toNat 12 ++
      fipsToByte a.typ 4 ++ fipsToByte a.keypair 4 ++ fipsToByte a.field1 4)
    (fipsToByte a.field2 4) [] (fipsToByte i 4) 28
    (by simp [fipsToByte_length]) (by simp [fipsToByte_length])
  simp only [List.append_assoc, List.append_nil] at this ⊢
  rw [this]; rfl

/-- **`address_compressed` = `ADRS_c`** (§11.2) whenever the layer and the
    type fit in one byte (in the code, `layer < d ≤ 22` and `type ≤ 6`). -/
theorem addressCompressed_eq (a : Address) (hl : a.layer < 256) (ht : a.typ < 256) :
    Code.addressCompressed a = FipsADRS.compress (Code.addressFull a) := by
  simp only [FipsADRS.compress, Code.addressCompressed, Code.addressFull, Code.setU32BE,
    Code.setU64BE, List.range_succ, List.range_zero, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, land_ff]
  simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt ht]

end OcamlPq.SLHDSA
