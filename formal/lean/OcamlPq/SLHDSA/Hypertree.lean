import OcamlPq.SLHDSA.XMSS
import OcamlPq.SLHDSA.FORS

/-!
# SLH-DSA: message-digest split and the hypertree

* `bytes_to_u64`, `low_mask`, `split_message_digest`
  (slhdsa_engine.ml 487–513) = the digest split of FIPS 205 Algorithms 19
  and 20 (lines 6–10 / 8–12): `md`, `idx_tree = toInt(…) mod 2^(h − h/d)`,
  `idx_leaf = toInt(…) mod 2^(h/d)`, including `low_mask 64`.
* The hypertree loops of `sign_formatted_with_randomness` (614–636) and
  `verify_formatted` (688–721) = `ht_sign` (Algorithm 12) and `ht_verify`
  (Algorithm 13): `leaf := tree mod 2^h′`, `tree := tree ≫ h′` per layer,
  the layer addresses, and the root chaining (the code chains `treehash`'s
  root, FIPS chains `xmss_pkFromSig`; they agree by XMSS correctness).
* Hypertree correctness: `ht_verify(M, ht_sign(M)) = true` against
  `PK.root = xmss_node(0, h′)` at layer `d − 1`, tree 0.

Signatures are lists of `n`-byte blocks (see `Top.lean` for the byte
layout).
-/

namespace OcamlPq.SLHDSA.Hypertree

open Address WOTS XMSS Treehash Base2b

/-! ## Digest split -/

/-- FIPS 205 Algorithm 2 `toInt(X, n)`: `total ← 256·total + X[i]`. -/
def fipsToInt (X : Bytes) (n : ℕ) : ℕ :=
  (List.range n).foldl (fun total i => 256 * total + X.getD i 0) 0

/-- `bytes_to_u64 string offset length` (lines 487–494). -/
def bytesToU64 (s : Bytes) (offset length : ℕ) : BitVec 64 :=
  (List.range length).foldl
    (fun result i => (result <<< 8) ||| BitVec.ofNat 64 (s.getD (offset + i) 0)) 0

/-- `low_mask bits` (lines 496–498). -/
def lowMask (bits : ℕ) : BitVec 64 :=
  if bits = 64 then BitVec.allOnes 64 else (1#64 <<< bits) - 1

/-- `split_message_digest digest` (lines 500–513); `Int64.to_int` of the
    masked leaf (below `2^h′ ≤ 2^9`) is its value. -/
def splitMessageDigest (P : Params) (digest : Bytes) : Bytes × BitVec 64 × ℕ :=
  let forsMessage := digest.take P.forsMessageBytes
  let tree := bytesToU64 digest P.forsMessageBytes P.treeBytes &&& lowMask P.treeBits
  let leaf :=
    (bytesToU64 digest (P.forsMessageBytes + P.treeBytes) P.leafBytes &&&
      lowMask P.treeHeight).toNat
  (forsMessage, tree, leaf)

/-- FIPS 205 Algorithm 19 lines 6–10 (Algorithm 20 lines 8–12). -/
def fipsSplit (P : Params) (digest : Bytes) : Bytes × ℕ × ℕ :=
  let mdBytes := (P.k * P.a + 7) / 8
  let treeBytes := (P.h - P.h / P.d + 7) / 8
  let leafBytes := (P.h + 8 * P.d - 1) / (8 * P.d)
  let md := digest.take mdBytes
  let tmpIdxTree := (digest.drop mdBytes).take treeBytes
  let tmpIdxLeaf := (digest.drop (mdBytes + treeBytes)).take leafBytes
  let idxTree := fipsToInt tmpIdxTree treeBytes % 2 ^ (P.h - P.h / P.d)
  let idxLeaf := fipsToInt tmpIdxLeaf leafBytes % 2 ^ (P.h / P.d)
  (md, idxTree, idxLeaf)

theorem getD_drop' (s : Bytes) (o i d : ℕ) : (s.drop o).getD i d = s.getD (o + i) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_take' (s : Bytes) (n i d : ℕ) (h : i < n) : (s.take n).getD i d = s.getD i d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem fipsToInt_succ (X : Bytes) (n : ℕ) :
    fipsToInt X (n + 1) = 256 * fipsToInt X n + X.getD n 0 := by
  simp [fipsToInt, List.range_succ]

theorem bytesToU64_toNat (s : Bytes) (hs : ∀ x ∈ s, x < 256) (offset : ℕ) :
    ∀ length, (bytesToU64 s offset length).toNat = fipsToInt (s.drop offset) length % 2 ^ 64 := by
  intro length
  induction length with
  | zero => simp [bytesToU64, fipsToInt]
  | succ len ih =>
    have hb : s.getD (offset + len) 0 < 256 := by
      rw [List.getD_eq_getElem?_getD]
      cases h : s[offset + len]? with
      | none => simp
      | some x => exact hs x (List.mem_of_getElem? h)
    have hstep : (bytesToU64 s offset (len + 1)) =
        (bytesToU64 s offset len <<< 8) ||| BitVec.ofNat 64 (s.getD (offset + len) 0) := by
      simp [bytesToU64, List.range_succ]
    rw [hstep, fipsToInt_succ, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, ih,
      getD_drop']
    generalize s.getD (offset + len) 0 = b at hb ⊢
    generalize fipsToInt (List.drop offset s) len = T
    rw [Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
    have h1 : ((T % 2 ^ 64) <<< 8) % 2 ^ 64 = (T % 2 ^ 56) <<< 8 := by
      simp only [Nat.shiftLeft_eq]; omega
    rw [h1, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : b < 2 ^ 8), Nat.shiftLeft_eq]
    omega

theorem lowMask_toNat (bits : ℕ) (h : bits ≤ 64) : (lowMask bits).toNat = 2 ^ bits - 1 := by
  unfold lowMask
  split_ifs with h64
  · subst h64; rfl
  · have hlt : bits < 64 := by omega
    rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
    have hp : 2 ^ bits < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hlt
    simp only [BitVec.toNat_ofNat, Nat.one_mod, Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt hp,
      show (1 : BitVec 64).toNat = 1 from rfl]
    have : 1 ≤ 2 ^ bits := Nat.one_le_two_pow
    rw [show 2 ^ 64 - 1 + 2 ^ bits = (2 ^ bits - 1) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

theorem and_lowMask (x : BitVec 64) (bits : ℕ) (h : bits ≤ 64) :
    (x &&& lowMask bits).toNat = x.toNat % 2 ^ bits := by
  rw [BitVec.toNat_and, lowMask_toNat bits h, Nat.and_two_pow_sub_one_eq_mod]

theorem fipsToInt_take (X : Bytes) (n : ℕ) : fipsToInt (X.take n) n = fipsToInt X n := by
  unfold fipsToInt
  apply List.foldl_ext
  intro t i hi
  have : i < n := List.mem_range.mp hi
  rw [getD_take' _ _ _ _ this]

theorem fipsToInt_lt (X : Bytes) (hX : ∀ x ∈ X, x < 256) (n : ℕ) : fipsToInt X n < 2 ^ (8 * n) := by
  induction n with
  | zero => simp [fipsToInt]
  | succ n ih =>
    rw [fipsToInt_succ]
    have hb : X.getD n 0 < 256 := by
      rw [List.getD_eq_getElem?_getD]
      cases h : X[n]? with
      | none => simp
      | some x => exact hX x (List.mem_of_getElem? h)
    rw [show 8 * (n + 1) = 8 * n + 8 by ring, pow_add]
    have : (2 : ℕ) ^ 8 = 256 := by norm_num
    rw [this]
    nlinarith

/-- **`split_message_digest` = the FIPS 205 digest split** for every
    parameter set and every `m`-byte digest: the FORS message is
    `digest[0 : ⌈k·a/8⌉]`, and the tree and leaf indices are
    `toInt(…) mod 2^(h − h/d)` and `toInt(…) mod 2^(h/d)` (the code's
    `low_mask 64 = −1` case included). -/
theorem splitMessageDigest_eq (P : Params) (hP : P ∈ allParams) (digest : Bytes)
    (hd : ∀ x ∈ digest, x < 256) :
    splitMessageDigest P digest =
      ((fipsSplit P digest).1, BitVec.ofNat 64 (fipsSplit P digest).2.1,
        (fipsSplit P digest).2.2) := by
  have hsplit := digest_split_fips P hP
  have hbits : P.treeBits ≤ 64 := (initChecks_all P hP).2.2
  have hbytes : P.treeBytes ≤ 8 := by unfold Params.treeBytes; omega
  have hh : P.treeHeight ≤ 9 := (sizes_portable P hP).2.2.2.2.1
  have hlb : P.leafBytes ≤ 8 := by unfold Params.leafBytes; omega
  have e2 : (P.h - P.h / P.d + 7) / 8 = P.treeBytes := by rw [← hsplit.1]; rfl
  have e3 : (P.h + 8 * P.d - 1) / (8 * P.d) = P.leafBytes := hsplit.2.2.symm
  have e4 : P.h - P.h / P.d = P.treeBits := hsplit.1.symm
  unfold splitMessageDigest fipsSplit
  dsimp only
  rw [e2, e3, e4]
  simp only [Prod.mk.injEq]
  have hdrop : ∀ o, ∀ x ∈ digest.drop o, x < 256 := fun o x hx => hd x (List.mem_of_mem_drop hx)
  refine ⟨rfl, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [and_lowMask _ _ hbits, bytesToU64_toNat digest hd, BitVec.toNat_ofNat, fipsToInt_take]
    have hlt := fipsToInt_lt _ (hdrop P.forsMessageBytes) P.treeBytes
    have : 2 ^ (8 * P.treeBytes) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpb : 2 ^ P.treeBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hbits
    rw [Nat.mod_eq_of_lt (by omega : fipsToInt _ _ < 2 ^ 64),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hpb)]
    rfl
  · rw [and_lowMask _ _ (by omega), bytesToU64_toNat digest hd, fipsToInt_take]
    have hlt := fipsToInt_lt _ (hdrop (P.forsMessageBytes + P.treeBytes)) P.leafBytes
    have : 2 ^ (8 * P.leafBytes) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.mod_eq_of_lt (by omega : fipsToInt _ _ < 2 ^ 64)]
    rfl

/-! ## Hypertree: specification (FIPS 205 Algorithms 12, 13) -/

/-- The hypertree address `ADRS.setLayerAddress(j); ADRS.setTreeAddress(t)`
    (the other fields are cleared or overwritten before every use). -/
def htAdrs (j t : ℕ) : Address := { Address.zero with layer := j, tree := BitVec.ofNat 64 t }

section Spec

variable (hs : Tweak) (n len h' d : ℕ)

/-- Lines 6–16 of FIPS 205 Algorithm 12 (`for j from 1 to d − 1`), as a
    recursion over the remaining `count` layers starting at layer `j`. -/
def fipsHtSignLoop : ℕ → ℕ → Bytes → ℕ → List Bytes
  | _, 0, _, _ => []
  | j, count + 1, root, idxTree =>
    let idxLeaf := idxTree % 2 ^ h'
    let idxTree := idxTree >>> h'
    let adrs := htAdrs j idxTree
    let sigTmp := fipsXmssSign hs n len h' root idxLeaf adrs
    let root :=
      if j < d - 1 then fipsXmssPkFromSig hs n len h' idxLeaf sigTmp.1 sigTmp.2 root adrs
      else root
    sigTmp.1 ++ sigTmp.2 ++ fipsHtSignLoop (j + 1) count root idxTree

/-- FIPS 205 Algorithm 12 `ht_sign(M, SK.seed, PK.seed, idx_tree, idx_leaf)`. -/
def fipsHtSign (M : Bytes) (idxTree idxLeaf : ℕ) : List Bytes :=
  let adrs := htAdrs 0 idxTree
  let sigTmp := fipsXmssSign hs n len h' M idxLeaf adrs
  let root := fipsXmssPkFromSig hs n len h' idxLeaf sigTmp.1 sigTmp.2 M adrs
  sigTmp.1 ++ sigTmp.2 ++ fipsHtSignLoop hs n len h' d 1 (d - 1) root idxTree

/-- `SIG_HT.getXMSSSignature(j)`: blocks `j·(h′ + len) ..< (j + 1)·(h′ + len)`. -/
def getXMSSSignature (sigHt : List Bytes) (j : ℕ) : List Bytes :=
  (sigHt.drop (j * (len + h'))).take (len + h')

/-- Lines 5–12 of FIPS 205 Algorithm 13. -/
def fipsHtVerifyLoop (sigHt : List Bytes) : ℕ → ℕ → Bytes → ℕ → Bytes
  | _, 0, node, _ => node
  | j, count + 1, node, idxTree =>
    let idxLeaf := idxTree % 2 ^ h'
    let idxTree := idxTree >>> h'
    let adrs := htAdrs j idxTree
    let sigTmp := getXMSSSignature len h' sigHt j
    let node := fipsXmssPkFromSig hs n len h' idxLeaf (sigTmp.take len) (sigTmp.drop len) node adrs
    fipsHtVerifyLoop sigHt (j + 1) count node idxTree

/-- FIPS 205 Algorithm 13 `ht_verify(M, SIG_HT, PK.seed, idx_tree, idx_leaf,
    PK.root)`, returning the final `node` (the algorithm returns
    `node = PK.root`). -/
def fipsHtVerifyNode (M : Bytes) (sigHt : List Bytes) (idxTree idxLeaf : ℕ) : Bytes :=
  let adrs := htAdrs 0 idxTree
  let sigTmp := getXMSSSignature len h' sigHt 0
  let node := fipsXmssPkFromSig hs n len h' idxLeaf (sigTmp.take len) (sigTmp.drop len) M adrs
  fipsHtVerifyLoop hs n len h' sigHt 1 (d - 1) node idxTree

end Spec

/-! ## Hypertree: code models -/

/-- The per-layer base address of lines 618–626 and 691–699:
    `{ zero_address with layer; tree = !tree; typ = 0; keypair = !leaf }`. -/
def codeBase (layer : ℕ) (tree : BitVec 64) (leaf : ℕ) : Address :=
  { Address.zero with layer := layer, tree := tree, typ := 0, keypair := leaf }

section Code

variable (thash : Address → List Bytes → Bytes) (prf : Address → Bytes) (n len h' : ℕ)

/-- The `for layer = 0 to P.d - 1` loop of `sign_formatted_with_randomness`
    (lines 617–636), over the remaining `count` layers: `merkle_sign` at
    `{zero_address with layer; tree; typ = 0; keypair = leaf}`, then
    `root := next_root; leaf := tree land low_mask h′; tree := tree lsr h′`. -/
def signLayers : ℕ → ℕ → Bytes → BitVec 64 → ℕ → Option (List Bytes)
  | 0, _, _, _, _ => some []
  | count + 1, layer, root, tree, leaf =>
    let base := codeBase layer tree leaf
    match merkleSign thash prf n len h' base leaf root with
    | none => none
    | some (wotsSig, auth, nextRoot) =>
      (signLayers count (layer + 1) nextRoot (tree >>> h') ((tree &&& lowMask h').toNat)).map
        fun rest => wotsSig ++ auth ++ rest

/-- The `for layer = 0 to P.d - 1` loop of `verify_formatted`
    (lines 690–721) over the remaining `count` layers and the remaining
    signature blocks: `take wots_signature_size` (`len` blocks), `take
    (tree_height * P.n)` (`h′` blocks), the per-layer step, and the index
    update. Returns the final `!root`. -/
def verifyLayers : ℕ → ℕ → Bytes → BitVec 64 → ℕ → List Bytes → Bytes
  | 0, _, root, _, _, _ => root
  | count + 1, layer, root, tree, leaf, sig =>
    let base := codeBase layer tree leaf
    let wotsSignature := sig.take len
    let authentication := (sig.drop len).take h'
    let root := verifyLayer thash n len h' base leaf root wotsSignature authentication
    verifyLayers count (layer + 1) root (tree >>> h') ((tree &&& lowMask h').toNat)
      (sig.drop (len + h'))

end Code

/-! ## Hypertree: theorems -/

theorem setTypeAndClear_congr {a b : Address} (hl : a.layer = b.layer) (ht : a.tree = b.tree)
    (y : ℕ) : a.setTypeAndClear y = b.setTypeAndClear y := by
  cases a; cases b; simp_all [Address.setTypeAndClear]

theorem fipsXmssNode_congr (hs : Tweak) (len : ℕ) {a b : Address} (hl : a.layer = b.layer)
    (ht : a.tree = b.tree) : ∀ z i, fipsXmssNode hs len a i z = fipsXmssNode hs len b i z := by
  intro z
  induction z with
  | zero => intro i; simp [fipsXmssNode, leafAdrs, setTypeAndClear_congr hl ht]
  | succ z ih => intro i; simp [fipsXmssNode, ih, treeH, setTypeAndClear_congr hl ht]

theorem fipsXmssSign_congr (hs : Tweak) (n len h' : ℕ) {a b : Address} (hl : a.layer = b.layer)
    (ht : a.tree = b.tree) (M : Bytes) (idx : ℕ) :
    fipsXmssSign hs n len h' M idx a = fipsXmssSign hs n len h' M idx b := by
  simp [fipsXmssSign, fipsXmssNode_congr hs len hl ht, leafAdrs, setTypeAndClear_congr hl ht]

theorem fipsXmssPkFromSig_congr (hs : Tweak) (n len h' : ℕ) {a b : Address}
    (hl : a.layer = b.layer) (ht : a.tree = b.tree) (idx : ℕ) (sig auth : List Bytes) (M : Bytes) :
    fipsXmssPkFromSig hs n len h' idx sig auth M a = fipsXmssPkFromSig hs n len h' idx sig auth M b := by
  have : treeH hs a = treeH hs b := by
    funext z i l r; simp [treeH, setTypeAndClear_congr hl ht]
  simp [fipsXmssPkFromSig, leafAdrs, setTypeAndClear_congr hl ht, this]

theorem shiftRight_toNat (t : BitVec 64) (h' : ℕ) : (t >>> h').toNat = t.toNat >>> h' :=
  BitVec.toNat_ushiftRight t h'

theorem fipsXmssSign_length (hs : Tweak) (n len h' : ℕ) (M : Bytes) (idx : ℕ) (a : Address) :
    (fipsXmssSign hs n len h' M idx a).1.length = len ∧
      (fipsXmssSign hs n len h' M idx a).2.length = h' := by
  simp [fipsXmssSign, fipsWotsSign]

/-- The byte-string hypotheses on the abstract hash: every `thash` output
    is an `n`-byte string. -/
def NBytes (n : ℕ) (x : Bytes) : Prop := x.length = n ∧ ∀ b ∈ x, b < 256

variable (thash : Address → List Bytes → Bytes) (prf : Address → Bytes)

theorem fipsXmssNode_nbytes (len n : ℕ) (hth : ∀ a bs, NBytes n (thash a bs)) (adrs : Address)
    (i z : ℕ) : NBytes n (fipsXmssNode (Tweak.ofCode thash prf) len adrs i z) := by
  cases z with
  | zero => exact hth _ _
  | succ z => exact hth _ _

/-- The code's hypertree signing loop = the FIPS loop, layer by layer
    (induction on the number of remaining layers). -/
theorem signLayers_eq (n len h' d : ℕ) (hn : n ≤ 136) (hth : ∀ a bs, NBytes n (thash a bs)) :
    ∀ count j (root : Bytes) (t : ℕ), NBytes n root → t < 2 ^ 64 → j + 1 + count = d →
      signLayers thash prf n len h' (count + 1) j root (BitVec.ofNat 64 (t >>> h'))
          (t % 2 ^ h') =
        some (fipsHtSignLoop (Tweak.ofCode thash prf) n len h' d j (count + 1) root t) := by
  intro count
  induction count with
  | zero =>
    intro j root t hroot ht hjd
    simp only [signLayers, fipsHtSignLoop]
    rw [merkleSign_eq thash prf n len h' _ _ (Nat.mod_lt _ (by positivity)) root hroot.2 hroot.1 hn]
    simp only [Option.map_some, List.append_nil]
    rw [fipsXmssSign_congr (a := codeBase j (BitVec.ofNat 64 (t >>> h')) (t % 2 ^ h'))
      (b := htAdrs j (t >>> h')) _ _ _ _ rfl rfl]
  | succ count ih =>
    intro j root t hroot ht hjd
    rw [signLayers]
    rw [merkleSign_eq thash prf n len h' _ _ (Nat.mod_lt _ (by positivity)) root hroot.2 hroot.1 hn]
    dsimp only
    have htl : (t >>> h') < 2 ^ 64 := lt_of_le_of_lt (Nat.shiftRight_le _ _) ht
    have e1 : (BitVec.ofNat 64 (t >>> h') >>> h') = BitVec.ofNat 64 ((t >>> h') >>> h') := by
      apply BitVec.eq_of_toNat_eq
      rw [shiftRight_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl,
        Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) htl)]
    have e2 : (BitVec.ofNat 64 (t >>> h') &&& lowMask h').toNat = (t >>> h') % 2 ^ h' := by
      by_cases hh : h' ≤ 64
      · rw [and_lowMask _ _ hh, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl]
      · -- for `h′ > 64` the tree index is below `2^64 < 2^h′`
        have hsmall : t >>> h' = 0 := by
          rw [Nat.shiftRight_eq_div_pow]
          exact Nat.div_eq_of_lt (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) (by omega)))
        rw [hsmall]; simp
    rw [e1, e2, ih (j + 1) _ (t >>> h') (fipsXmssNode_nbytes thash prf len n hth _ _ _)
      htl (by omega)]
    simp only [Option.map_some]
    conv_rhs => rw [fipsHtSignLoop]
    have hj : j < d - 1 := by omega
    simp only [hj, ↓reduceIte, List.append_assoc]
    rw [fipsXmssSign_congr (a := codeBase j (BitVec.ofNat 64 (t >>> h')) (t % 2 ^ h'))
      (b := htAdrs j (t >>> h')) _ _ _ _ rfl rfl,
      fipsXmss_correct thash prf n len h' root _ (Nat.mod_lt _ (by positivity)),
      fipsXmssNode_congr (a := codeBase j (BitVec.ofNat 64 (t >>> h')) (t % 2 ^ h'))
      (b := htAdrs j (t >>> h')) _ _ rfl rfl]

theorem ofNat_shift (t h' : ℕ) (ht : t < 2 ^ 64) :
    BitVec.ofNat 64 t >>> h' = BitVec.ofNat 64 (t >>> h') := by
  apply BitVec.eq_of_toNat_eq
  rw [shiftRight_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) ht)]

theorem ofNat_mask (t h' : ℕ) (ht : t < 2 ^ 64) (hh : h' ≤ 64) :
    (BitVec.ofNat 64 t &&& lowMask h').toNat = t % 2 ^ h' := by
  rw [and_lowMask _ _ hh, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht]

/-- **`ht_sign`.** The code's hypertree signing loop (all `d` layers,
    starting from `idx_tree`, `idx_leaf`) does not raise and produces
    FIPS 205's `SIG_HT = ht_sign(M, idx_tree, idx_leaf)`, for every `n`-byte
    message, `idx_leaf < 2^h′` and every 64-bit `idx_tree`. -/
theorem signLayers_htSign (n len h' d : ℕ) (hd : 1 ≤ d) (hh : h' ≤ 64) (hn : n ≤ 136)
    (hth : ∀ a bs, NBytes n (thash a bs)) (M : Bytes) (hM : NBytes n M) (idxTree idxLeaf : ℕ)
    (htree : idxTree < 2 ^ 64) (hleaf : idxLeaf < 2 ^ h') :
    signLayers thash prf n len h' d 0 M (BitVec.ofNat 64 idxTree) idxLeaf =
      some (fipsHtSign (Tweak.ofCode thash prf) n len h' d M idxTree idxLeaf) := by
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  rw [signLayers, merkleSign_eq thash prf n len h' _ _ hleaf M hM.2 hM.1 hn]
  dsimp only
  unfold fipsHtSign
  dsimp only
  rw [fipsXmssSign_congr (a := codeBase 0 (BitVec.ofNat 64 idxTree) idxLeaf)
      (b := htAdrs 0 idxTree) _ _ _ _ rfl rfl,
    fipsXmss_correct thash prf n len h' M _ hleaf,
    fipsXmssNode_congr (a := codeBase 0 (BitVec.ofNat 64 idxTree) idxLeaf)
      (b := htAdrs 0 idxTree) _ _ rfl rfl]
  cases c with
  | zero => simp [signLayers, fipsHtSignLoop]
  | succ c =>
    have hmask := ofNat_mask idxTree h' htree hh
    rw [ofNat_shift idxTree h' htree, show (BitVec.ofNat 64 idxTree &&& lowMask h').toNat =
      idxTree % 2 ^ h' from hmask, signLayers_eq thash prf n len h' (c + 1 + 1) hn hth c 1 _ idxTree
      (fipsXmssNode_nbytes thash prf len n hth _ _ _) htree (by omega)]
    simp [List.append_assoc]

theorem computeRoot_nbytes (n h' off : ℕ) (hth : ∀ a bs, NBytes n (thash a bs)) (ta : Address)
    (leaf : Bytes) (hleaf : NBytes n leaf) (L : ℕ) (auth : ℕ → Bytes) :
    NBytes n (computeRoot thash h' off ta leaf L auth) := by
  cases h' with
  | zero => simpa [computeRoot] using hleaf
  | succ h' => rw [computeRoot_range]; exact hth _ _

theorem verifyLayer_nbytes (n len h' : ℕ) (hth : ∀ a bs, NBytes n (thash a bs)) (base : Address)
    (leaf : ℕ) (root : Bytes) (wotsSig auth : List Bytes) :
    NBytes n (verifyLayer thash n len h' base leaf root wotsSig auth) :=
  computeRoot_nbytes thash n h' 0 hth _ _ (hth _ _) _ _

theorem getXMSSSignature_split (len h' : ℕ) (sigHt : List Bytes) (j : ℕ) :
    (getXMSSSignature len h' sigHt j).take len = (sigHt.drop (j * (len + h'))).take len ∧
      (getXMSSSignature len h' sigHt j).drop len =
        ((sigHt.drop (j * (len + h'))).drop len).take h' := by
  unfold getXMSSSignature
  constructor
  · rw [List.take_take, Nat.min_eq_left (by omega)]
  · rw [List.drop_take, Nat.add_sub_cancel_left]

/-- The code's hypertree verification loop = the FIPS loop, layer by layer. -/
theorem verifyLayers_eq (n len h' : ℕ) (hh : h' ≤ 64) (hn : n ≤ 136)
    (hth : ∀ a bs, NBytes n (thash a bs)) (sigHt : List Bytes) :
    ∀ count j (node : Bytes) (t : ℕ), NBytes n node → t < 2 ^ 64 →
      verifyLayers thash n len h' (count + 1) j node (BitVec.ofNat 64 (t >>> h')) (t % 2 ^ h')
          (sigHt.drop (j * (len + h'))) =
        fipsHtVerifyLoop (Tweak.ofCode thash prf) n len h' sigHt j (count + 1) node t := by
  intro count
  induction count with
  | zero =>
    intro j node t hnode ht
    simp only [verifyLayers, fipsHtVerifyLoop]
    rw [verifyLayer_eq thash prf n len h' (codeBase j (BitVec.ofNat 64 (t >>> h')) (t % 2 ^ h'))
      (t % 2 ^ h') rfl node hnode.2 hnode.1 hn,
      (getXMSSSignature_split len h' sigHt j).1, (getXMSSSignature_split len h' sigHt j).2]
    exact fipsXmssPkFromSig_congr _ _ _ _ rfl rfl _ _ _ _
  | succ count ih =>
    intro j node t hnode ht
    have htl : (t >>> h') < 2 ^ 64 := lt_of_le_of_lt (Nat.shiftRight_le _ _) ht
    rw [verifyLayers]
    have hdd : List.drop (len + h') (List.drop (j * (len + h')) sigHt) =
        List.drop ((j + 1) * (len + h')) sigHt := by
      rw [List.drop_drop]; congr 1; ring
    rw [ofNat_shift _ _ htl, ofNat_mask _ _ htl hh, hdd,
      ih (j + 1) _ (t >>> h') (verifyLayer_nbytes thash n len h' hth _ _ _ _ _) htl]
    conv_rhs => rw [fipsHtVerifyLoop]
    rw [verifyLayer_eq thash prf n len h' (codeBase j (BitVec.ofNat 64 (t >>> h')) (t % 2 ^ h'))
      (t % 2 ^ h') rfl node hnode.2 hnode.1 hn,
      (getXMSSSignature_split len h' sigHt j).1, (getXMSSSignature_split len h' sigHt j).2,
      fipsXmssPkFromSig_congr (a := codeBase j (BitVec.ofNat 64 (t >>> h')) (t % 2 ^ h'))
        (b := htAdrs j (t >>> h')) _ _ _ _ rfl rfl]

/-- **`ht_verify`.** The code's hypertree verification loop computes the
    node of FIPS 205's `ht_verify` (which then compares it with `PK.root`),
    for every signature (adversarial ones included). -/
theorem verifyLayers_htVerify (n len h' d : ℕ) (hd : 1 ≤ d) (hh : h' ≤ 64) (hn : n ≤ 136)
    (hth : ∀ a bs, NBytes n (thash a bs)) (M : Bytes) (hM : NBytes n M) (sigHt : List Bytes)
    (idxTree idxLeaf : ℕ) (htree : idxTree < 2 ^ 64) :
    verifyLayers thash n len h' d 0 M (BitVec.ofNat 64 idxTree) idxLeaf sigHt =
      fipsHtVerifyNode (Tweak.ofCode thash prf) n len h' d M sigHt idxTree idxLeaf := by
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  rw [verifyLayers]
  dsimp only [fipsHtVerifyNode]
  have hs := getXMSSSignature_split len h' sigHt 0
  simp only [zero_mul, List.drop_zero] at hs
  rw [verifyLayer_eq thash prf n len h' (codeBase 0 (BitVec.ofNat 64 idxTree) idxLeaf) idxLeaf rfl
    M hM.2 hM.1 hn, hs.1, hs.2,
    fipsXmssPkFromSig_congr (a := codeBase 0 (BitVec.ofNat 64 idxTree) idxLeaf)
      (b := htAdrs 0 idxTree) _ _ _ _ rfl rfl]
  cases c with
  | zero => simp [verifyLayers, fipsHtVerifyLoop]
  | succ c =>
    have := verifyLayers_eq thash prf n len h' hh hn hth sigHt c 1
      (fipsXmssPkFromSig (Tweak.ofCode thash prf) n len h' idxLeaf (List.take len sigHt)
        (List.take h' (List.drop len sigHt)) M (htAdrs 0 idxTree)) idxTree
      (by
        rw [← fipsXmssPkFromSig_congr (a := codeBase 0 (BitVec.ofNat 64 idxTree) idxLeaf)
          (b := htAdrs 0 idxTree) _ _ _ _ rfl rfl, ← verifyLayer_eq thash prf n len h'
          (codeBase 0 (BitVec.ofNat 64 idxTree) idxLeaf) idxLeaf rfl M hM.2 hM.1 hn]
        exact verifyLayer_nbytes thash n len h' hth _ _ _ _ _) htree
    rw [ofNat_shift _ _ htree, ofNat_mask _ _ htree hh, show List.drop (len + h') sigHt =
      List.drop (1 * (len + h')) sigHt by rw [one_mul], this]
    rfl

/-! ## Hypertree correctness -/

section Correct

variable (hs : Tweak) (n len h' d : ℕ)

/-- The root the verifier should reach after `count` layers from layer `j`. -/
def fipsHtRoot (len h' : ℕ) : ℕ → ℕ → Bytes → ℕ → Bytes
  | _, 0, node, _ => node
  | j, count + 1, _, t =>
    fipsHtRoot len h' (j + 1) count (fipsXmssNode hs len (htAdrs j (t >>> h')) 0 h') (t >>> h')

end Correct

theorem fipsHtSignLoop_length (hs : Tweak) (n len h' d : ℕ) :
    ∀ count j root t, (fipsHtSignLoop hs n len h' d j count root t).length = count * (len + h') := by
  intro count
  induction count with
  | zero => intros; simp [fipsHtSignLoop]
  | succ c ih =>
    intro j root t
    simp only [fipsHtSignLoop, List.length_append, ih, fipsXmssSign_length]
    ring

theorem split3 {α : Type} {L A B R : List α} {len h' : ℕ} (hL : L = A ++ B ++ R)
    (hA : A.length = len) (hB : B.length = h') :
    (L.take (len + h')).take len = A ∧ (L.take (len + h')).drop len = B ∧
      L.drop (len + h') = R := by
  subst hL hA hB
  refine ⟨?_, ?_, ?_⟩ <;> simp [List.take_append, List.drop_append]

theorem htVerifyLoop_signLoop (n len h' d : ℕ) :
    ∀ count j (root : Bytes) (t : ℕ) (sigHt : List Bytes), j + count = d →
      sigHt.drop (j * (len + h')) =
        fipsHtSignLoop (Tweak.ofCode thash prf) n len h' d j count root t →
      fipsHtVerifyLoop (Tweak.ofCode thash prf) n len h' sigHt j count root t =
        fipsHtRoot (Tweak.ofCode thash prf) len h' j count root t := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ c ih =>
    intro j root t sigHt hjd hsig
    rw [fipsHtSignLoop] at hsig
    obtain ⟨hA, hB⟩ := fipsXmssSign_length (Tweak.ofCode thash prf) n len h' root (t % 2 ^ h')
      (htAdrs j (t >>> h'))
    have k := split3 hsig hA hB
    rw [fipsHtVerifyLoop, fipsHtRoot]
    unfold getXMSSSignature
    rw [k.1, k.2.1, fipsXmss_correct thash prf n len h' root _ (Nat.mod_lt _ (by positivity))]
    cases c with
    | zero => rfl
    | succ c =>
      apply ih (j + 1) _ (t >>> h') sigHt (by omega)
      rw [show (j + 1) * (len + h') = j * (len + h') + (len + h') by ring, ← List.drop_drop, k.2.2]
      have hj : j < d - 1 := by omega
      simp only [hj, ↓reduceIte, fipsXmss_correct thash prf n len h' root _
        (Nat.mod_lt _ (by positivity))]

/-- The final hypertree root is `xmss_node(0, h′)` of the top tree. -/
theorem fipsHtRoot_eq (hs : Tweak) (len h' : ℕ) :
    ∀ count j (node : Bytes) (t : ℕ),
      fipsHtRoot hs len h' j (count + 1) node t =
        fipsXmssNode hs len (htAdrs (j + count) (t >>> ((count + 1) * h'))) 0 h' := by
  intro count
  induction count with
  | zero => intro j node t; simp [fipsHtRoot]
  | succ c ih =>
    intro j node t
    rw [fipsHtRoot, ih, ← Nat.shiftRight_add, show j + 1 + c = j + (c + 1) by ring,
      show h' + (c + 1) * h' = (c + 1 + 1) * h' by ring]

/-- **Hypertree correctness (FIPS level).** `ht_verify` accepts `ht_sign`'s
    output: the node it computes is `xmss_node(0, h′)` of layer `d − 1`,
    tree `idx_tree ≫ (d−1)h′` — which is `PK.root` (layer `d − 1`, tree 0)
    whenever `idx_tree < 2^((d−1)h′) = 2^(h − h′)`. -/
theorem fips_ht_correct (n len h' d : ℕ) (hd : 1 ≤ d) (M : Bytes) (idxTree idxLeaf : ℕ)
    (hleaf : idxLeaf < 2 ^ h') (htree : idxTree < 2 ^ ((d - 1) * h')) :
    fipsHtVerifyNode (Tweak.ofCode thash prf) n len h' d M
        (fipsHtSign (Tweak.ofCode thash prf) n len h' d M idxTree idxLeaf) idxTree idxLeaf =
      fipsXmssNode (Tweak.ofCode thash prf) len (htAdrs (d - 1) 0) 0 h' := by
  obtain ⟨hA, hB⟩ := fipsXmssSign_length (Tweak.ofCode thash prf) n len h' M idxLeaf
    (htAdrs 0 idxTree)
  unfold fipsHtVerifyNode fipsHtSign
  dsimp only
  have k := split3 rfl hA hB (R := fipsHtSignLoop (Tweak.ofCode thash prf) n len h' d 1 (d - 1)
    (fipsXmssPkFromSig (Tweak.ofCode thash prf) n len h' idxLeaf
      (fipsXmssSign (Tweak.ofCode thash prf) n len h' M idxLeaf (htAdrs 0 idxTree)).1
      (fipsXmssSign (Tweak.ofCode thash prf) n len h' M idxLeaf (htAdrs 0 idxTree)).2 M
      (htAdrs 0 idxTree)) idxTree)
  unfold getXMSSSignature
  simp only [zero_mul, List.drop_zero]
  rw [fipsXmss_correct thash prf n len h' M _ hleaf] at k ⊢
  rw [k.1, k.2.1, fipsXmss_correct thash prf n len h' M _ hleaf]
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  cases c with
  | zero =>
    simp only [Nat.add_sub_cancel, fipsHtVerifyLoop, zero_mul, pow_zero] at htree ⊢
    have : idxTree = 0 := by omega
    subst this; rfl
  | succ c =>
    simp only [Nat.add_sub_cancel] at htree k ⊢
    rw [htVerifyLoop_signLoop thash prf n len h' (c + 1 + 1) (c + 1) 1 _ idxTree _ (by omega)
      (by rw [one_mul, k.2.2]), fipsHtRoot_eq]
    have h0 : idxTree >>> ((c + 1) * h') = 0 := by
      rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (by simpa using htree)
    rw [h0, Nat.add_comm 1 c]

end OcamlPq.SLHDSA.Hypertree
