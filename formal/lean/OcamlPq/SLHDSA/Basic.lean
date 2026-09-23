import OcamlPq.SLHDSA.Params

/-!
# SLH-DSA: the code's address record

Models the `address` record of `slhdsa/slhdsa_engine.ml` (lines 135–150)
and the three helpers that derive one address from another (lines 198–211).

The OCaml `int` fields are modelled as `ℕ`: the code only ever stores
non-negative values in them (see `Portability.lean` for the bounds that make
this faithful on every platform). The `int64` field `tree` is `BitVec 64`.
-/

namespace OcamlPq.SLHDSA

/-- The OCaml record `address` (slhdsa_engine.ml 135–142). `field1` is the
    chain address / tree height, `field2` the hash address / tree index. -/
structure Address where
  layer : ℕ
  tree : BitVec 64
  typ : ℕ
  keypair : ℕ
  field1 : ℕ
  field2 : ℕ
  deriving DecidableEq, Repr

namespace Address

/-- `zero_address` (lines 149–150). -/
def zero : Address := ⟨0, 0, 0, 0, 0, 0⟩

/-- `with_type typ address = { address with typ }` (line 198). -/
def withType (typ : ℕ) (a : Address) : Address := { a with typ := typ }

/-- `keypair_address typ source` (lines 200–208): keeps layer, tree and
    keypair, sets the type, clears `field1`/`field2`. -/
def keypairAddress (typ : ℕ) (s : Address) : Address :=
  ⟨s.layer, s.tree, typ, s.keypair, 0, 0⟩

/-- `subtree_address typ source` (lines 210–211): keeps layer and tree, sets
    the type, clears keypair, `field1` and `field2`. -/
def subtreeAddress (typ : ℕ) (s : Address) : Address :=
  { zero with layer := s.layer, tree := s.tree, typ := typ }

/-- `{ a with field1 = x; field2 = y }` — the record update used for
    tree nodes (lines 351–356, 381–388) and WOTS+ chains (304, 314). -/
def setFields (a : Address) (f1 f2 : ℕ) : Address := { a with field1 := f1, field2 := f2 }

end Address

/-- The address types of FIPS 205 §4.2 (Table 1 of the ADRS types). -/
def WOTS_HASH : ℕ := 0
def WOTS_PK : ℕ := 1
def TREE : ℕ := 2
def FORS_TREE : ℕ := 3
def FORS_ROOTS : ℕ := 4
def WOTS_PRF : ℕ := 5
def FORS_PRF : ℕ := 6

end OcamlPq.SLHDSA
