import OcamlPq.SLHDSA.WOTS
import OcamlPq.SLHDSA.Treehash

/-!
# SLH-DSA: XMSS

FIPS 205 Algorithms 9 (`xmss_node`), 10 (`xmss_sign`) and 11
(`xmss_pkFromSig`), and the code that realises them:

* `merkle_sign` (slhdsa_engine.ml 463–475) = `xmss_sign` together with the
  root `xmss_node(0, h′)`;
* `merkle_root` (477–485) = `xmss_node(0, h′)` at layer `d − 1`, tree 0
  (the `PK.root` of Algorithm 18);
* the per-layer body of `verify_formatted` (700–716) = `xmss_pkFromSig`;
* XMSS correctness: `xmss_pkFromSig(idx, xmss_sign(M, idx), M) =
  xmss_node(0, h′)` for every message and every `idx < 2^h′`.

All statements hold for every tweakable hash (`thash`, `prf` arbitrary).
-/

namespace OcamlPq.SLHDSA.XMSS

open Address WOTS Treehash Base2b

/-! ## FIPS 205 Algorithms 9–11 -/

section Spec

variable (hs : Tweak) (n len h' : ℕ)

/-- `ADRS.setTypeAndClear(TREE); ADRS.setTreeHeight(z); ADRS.setTreeIndex(i)`
    followed by `H(PK.seed, ADRS, l ‖ r)`. -/
def treeH (adrs : Address) (z i : ℕ) (l r : Bytes) : Bytes :=
  hs.H (((adrs.setTypeAndClear TREE).setWord2 z).setWord3 i) l r

/-- FIPS 205 Algorithm 9 `xmss_node(SK.seed, i, z, PK.seed, ADRS)`. -/
def fipsXmssNode (adrs : Address) : ℕ → ℕ → Bytes
  | i, 0 => fipsWotsPkGen hs len (leafAdrs adrs i)
  | i, z + 1 =>
    let lnode := fipsXmssNode adrs (2 * i) z
    let rnode := fipsXmssNode adrs (2 * i + 1) z
    treeH hs adrs (z + 1) i lnode rnode

/-- FIPS 205 Algorithm 10 `xmss_sign(M, SK.seed, idx, PK.seed, ADRS)`,
    returning `(sig, AUTH)` (`SIG_XMSS = sig ‖ AUTH`). -/
def fipsXmssSign (M : Bytes) (idx : ℕ) (adrs : Address) : List Bytes × List Bytes :=
  let auth := (List.range h').map fun j => fipsXmssNode hs len adrs ((idx / 2 ^ j) ^^^ 1) j
  let sig := fipsWotsSign hs n len M (leafAdrs adrs idx)
  (sig, auth)

/-- FIPS 205 Algorithm 11 `xmss_pkFromSig(idx, SIG_XMSS, M, PK.seed, ADRS)`
    with `SIG_XMSS = sig ‖ AUTH`. Lines 1–3 compute the WOTS+ public key at
    `setKeyPairAddress(idx) ∘ setTypeAndClear(WOTS_HASH)`; lines 4–16 are
    the root loop with the tree-index register (`fipsRootLoop`). -/
def fipsXmssPkFromSig (idx : ℕ) (sig auth : List Bytes) (M : Bytes) (adrs : Address) : Bytes :=
  let node0 := fipsWotsPkFromSig hs n len sig M (leafAdrs adrs idx)
  fipsRootLoop (treeH hs adrs) h' idx idx (fun k => auth.getD k []) node0

end Spec

/-! ## Code models -/

section Code

variable (thash : Address → List Bytes → Bytes) (prf : Address → Bytes) (n len h' : ℕ)

/-- `merkle_sign context base_address leaf_index message` (lines 463–475),
    returning the WOTS+ signature strings, the `h′` authentication slots
    and the root (the signature string is their concatenation).

    `gen_leaf` returns `wots_leaf … index` whether or not it captures; the
    capture (writing `wots_signature`) happens in the single call with
    `index = leaf_index`, which `treehash` makes because it calls `gen_leaf`
    once for every `index < 2^h′`. The model therefore reads the captured
    array from `wots_leaf ~capture … leaf_index`. Unwritten authentication
    slots would be zero bytes; the theorems show there are none. -/
def merkleSign (base : Address) (leafIndex : ℕ) (message : Bytes) :
    Option (List Bytes × List Bytes × Bytes) :=
  let lengths := chainLengths (2 * n) message
  let treeAddress := subtreeAddress 2 base
  match treehash thash n h' (leafIndex : ℤ) 0 treeAddress
      (fun index => (wotsLeaf thash prf len none base index).1) [] with
  | none => none
  | some (root, authentication) =>
    let wotsSignature := ((wotsLeaf thash prf len (some lengths) base leafIndex).2).getD []
    some (wotsSignature, (List.range h').map fun j => (authentication j).getD (List.replicate n 0),
      root)

/-- `merkle_root context` (lines 477–485). -/
def merkleRoot (d : ℕ) : Option Bytes :=
  let base : Address := { Address.zero with layer := d - 1, typ := 0 }
  let treeAddress := subtreeAddress 2 base
  (treehash thash n h' (-1) 0 treeAddress (fun i => (wotsLeaf thash prf len none base i).1)
    []).map Prod.fst

/-- One iteration of the hypertree loop of `verify_formatted`
    (lines 700–716) after the signature has been split: recompute the WOTS+
    public key from the WOTS+ signature on `root`, hash it with
    `keypair_address 1`, and climb the authentication path with
    `compute_root`. `auth.getD j []` is `sub authentication (j * n) n`. -/
def verifyLayer (base : Address) (leaf : ℕ) (root : Bytes) (wotsSig auth : List Bytes) :
    Bytes :=
  let wotsPublicKey := wotsPublicKeyFromSignature thash len n base root wotsSig
  let wotsLeaf := thash (keypairAddress 1 base) wotsPublicKey
  computeRoot thash h' 0 (subtreeAddress 2 base) wotsLeaf leaf (fun j => auth.getD j [])

end Code

/-! ## Theorems -/

variable (thash : Address → List Bytes → Bytes) (prf : Address → Bytes)

theorem treeH_ofCode (adrs : Address) (z i : ℕ) (l r : Bytes) :
    treeH (Tweak.ofCode thash prf) adrs z i l r = nodeHash thash (subtreeAddress 2 adrs) z i l r :=
  rfl

/-- **`treehash`'s node = `xmss_node`** (Algorithm 9): with the WOTS+ leaf
    generator and tree address `subtree_address 2 base`, the recursive node
    of `Treehash` is FIPS 205's `xmss_node`, for all heights and indices. -/
theorem specNode_eq_xmssNode (len : ℕ) (base : Address) :
    ∀ z i, specNode thash (subtreeAddress 2 base) (fun i => (wotsLeaf thash prf len none base i).1)
      i z = fipsXmssNode (Tweak.ofCode thash prf) len base i z := by
  intro z
  induction z with
  | zero => intro i; simp [specNode, node, fipsXmssNode, wotsLeaf_pk]
  | succ z ih =>
    intro i
    simp only [specNode, node] at ih ⊢
    rw [ih, ih]
    rfl

/-- **`merkle_sign` = `xmss_sign` + root.** For every leaf index
    `< 2^h′` and every `n`-byte message (`n ≤ 136`), `merkle_sign` does not
    raise and returns FIPS 205's `xmss_sign` signature (WOTS+ part and
    authentication path) and `xmss_node(0, h′)`. -/
theorem merkleSign_eq (n len h' : ℕ) (base : Address) (L : ℕ) (hL : L < 2 ^ h') (M : Bytes)
    (hM : ∀ x ∈ M, x < 256) (hn : M.length = n) (hn' : n ≤ 136) :
    merkleSign thash prf n len h' base L M =
      some ((fipsXmssSign (Tweak.ofCode thash prf) n len h' M L base).1,
        (fipsXmssSign (Tweak.ofCode thash prf) n len h' M L base).2,
        fipsXmssNode (Tweak.ofCode thash prf) len base 0 h') := by
  unfold merkleSign
  dsimp only
  rw [treehash_spec thash n h' 0 (subtreeAddress 2 base) _ (dvd_zero _) (L : ℤ) (by omega)
    (by exact_mod_cast hL)]
  simp only [Nat.zero_shiftRight, zero_add, Int.toNat_natCast]
  subst hn
  rw [wotsLeaf_sig thash prf M hM hn']
  simp only [Option.getD_some, fipsXmssSign, specNode_eq_xmssNode, Option.some.injEq,
    Prod.mk.injEq, true_and]
  constructor
  · apply List.map_congr_left
    intro j hj
    have : j < h' := List.mem_range.mp hj
    simp [this, Nat.shiftRight_eq_div_pow]
  · trivial

/-- **`merkle_root` = FIPS 205's `PK.root`** (Algorithm 18 lines 1–3:
    `ADRS ← toByte(0, 32); ADRS.setLayerAddress(d − 1);
    PK.root ← xmss_node(SK.seed, 0, h′, PK.seed, ADRS)`). -/
theorem merkleRoot_eq (n len h' d : ℕ) :
    merkleRoot thash prf n len h' d =
      some (fipsXmssNode (Tweak.ofCode thash prf) len (Address.zero.setLayer (d - 1)) 0 h') := by
  unfold merkleRoot
  dsimp only
  rw [treehash_neg thash n h' 0 _ _ (dvd_zero _) (-1) (by norm_num)]
  simp only [Option.map_some, Nat.zero_shiftRight]
  rw [specNode_eq_xmssNode]
  rfl

/-- **The verifier's layer step = `xmss_pkFromSig`** (Algorithm 11) for
    the base address `{zero with layer; tree; keypair = leaf}` the code
    builds (only its layer and tree are used by FIPS), every root message
    of `n ≤ 136` bytes and every signature. -/
theorem verifyLayer_eq (n len h' : ℕ) (base : Address) (leaf : ℕ) (hk : base.keypair = leaf)
    (M : Bytes) (hM : ∀ x ∈ M, x < 256) (hn : M.length = n) (hn' : n ≤ 136)
    (wotsSig auth : List Bytes) :
    verifyLayer thash n len h' base leaf M wotsSig auth =
      fipsXmssPkFromSig (Tweak.ofCode thash prf) n len h' leaf wotsSig auth M base := by
  unfold verifyLayer fipsXmssPkFromSig
  subst hn hk
  dsimp only
  rw [wotsPublicKeyFromSignature_eq thash prf M hM hn' len base wotsSig,
    computeRoot_eq_fips thash h' 0 _ (dvd_zero _)]
  simp only [zero_add]
  rfl

/-- **XMSS correctness**: `xmss_pkFromSig(idx, xmss_sign(M, idx), M) =
    xmss_node(0, h′)` for every message `M`, every address and every
    `idx < 2^h′`. -/
theorem fipsXmss_correct (n len h' : ℕ) (M : Bytes) (idx : ℕ) (hidx : idx < 2 ^ h')
    (adrs : Address) :
    fipsXmssPkFromSig (Tweak.ofCode thash prf) n len h' idx
        (fipsXmssSign (Tweak.ofCode thash prf) n len h' M idx adrs).1
        (fipsXmssSign (Tweak.ofCode thash prf) n len h' M idx adrs).2 M adrs =
      fipsXmssNode (Tweak.ofCode thash prf) len adrs 0 h' := by
  unfold fipsXmssPkFromSig fipsXmssSign
  dsimp only
  rw [fipsWots_correct]
  have h1 := computeRoot_eq_fips thash h' 0 (subtreeAddress 2 adrs) (dvd_zero _)
    (fipsWotsPkGen (Tweak.ofCode thash prf) len (leafAdrs adrs idx)) idx
    (fun k => ((List.range h').map fun j =>
      fipsXmssNode (Tweak.ofCode thash prf) len adrs ((idx / 2 ^ j) ^^^ 1) j).getD k [])
  rw [zero_add] at h1
  change fipsRootLoop (nodeHash thash (subtreeAddress 2 adrs)) h' idx idx _ _ = _
  rw [← h1]
  have h2 := computeRoot_auth thash h' 0 (subtreeAddress 2 adrs)
    (fun i => (wotsLeaf thash prf len none adrs i).1) (dvd_zero _) idx hidx
  simp only [add_zero, Nat.zero_shiftRight, zero_add] at h2
  rw [wotsLeaf_pk, specNode_eq_xmssNode] at h2
  rw [← h2]
  unfold computeRoot
  apply List.foldl_ext
  intro node level hlev
  have : level < h' := List.mem_range.mp hlev
  simp [this, Nat.shiftRight_eq_div_pow, specNode_eq_xmssNode]

end OcamlPq.SLHDSA.XMSS
