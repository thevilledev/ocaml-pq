import OcamlPq.SLHDSA.WOTS
import OcamlPq.SLHDSA.Treehash

/-!
# SLH-DSA: FORS

FIPS 205 Algorithms 14 (`fors_skGen`), 15 (`fors_node`), 16 (`fors_sign`)
and 17 (`fors_pkFromSig`), and the code that realises them:
`fors_leaf` (slhdsa_engine.ml 410–415), `fors_sign` (417–439) and
`fors_public_key_from_signature` (441–461).

Signatures are modelled as lists of `n`-byte blocks: the FORS signature is
`k` groups of `1 + a` blocks (secret key, then the `a` authentication
nodes). The code's byte positions (`!position`, advanced by `P.n` and
`P.a * P.n`) are `n` times the block positions used here.

The FORS indices are `message_to_fors_indices message`, modelled with
OCaml `int`s of width `w`; `Base2b.messageToForsIndices_eq` shows it is
`base_2b(md, a, k)` for every `w ≥ a + 7`.
-/

namespace OcamlPq.SLHDSA.FORS

open Address WOTS Treehash Base2b

/-! ## FIPS 205 Algorithms 14–17 -/

section Spec

variable (hs : Tweak) (k a : ℕ)

/-- FIPS 205 Algorithm 14 `fors_skGen(SK.seed, PK.seed, ADRS, idx)`:
    `skADRS.setTypeAndClear(FORS_PRF); skADRS.setKeyPairAddress(…);
    skADRS.setTreeIndex(idx); PRF(PK.seed, SK.seed, skADRS)`. -/
def fipsForsSkGen (adrs : Address) (idx : ℕ) : Bytes :=
  hs.PRF (((adrs.setTypeAndClear FORS_PRF).setKeyPair adrs.keypair).setWord3 idx)

/-- FIPS 205 Algorithm 15 `fors_node(SK.seed, i, z, PK.seed, ADRS)`. -/
def fipsForsNode (adrs : Address) : ℕ → ℕ → Bytes
  | i, 0 =>
    let sk := fipsForsSkGen hs adrs i
    hs.F ((adrs.setWord2 0).setWord3 i) sk
  | i, z + 1 =>
    let lnode := fipsForsNode adrs (2 * i) z
    let rnode := fipsForsNode adrs (2 * i + 1) z
    hs.H ((adrs.setWord2 (z + 1)).setWord3 i) lnode rnode

/-- FIPS 205 Algorithm 16 `fors_sign(md, SK.seed, PK.seed, ADRS)`, as the
    list of its `k·(1 + a)` blocks. -/
def fipsForsSign (md : Bytes) (adrs : Address) : List Bytes :=
  let indices := fipsBase2b md a k
  (List.range k).flatMap fun i =>
    let sk := fipsForsSkGen hs adrs (i * 2 ^ a + indices.getD i 0)
    let auth := (List.range a).map fun j =>
      let s := (indices.getD i 0 / 2 ^ j) ^^^ 1
      fipsForsNode hs adrs (i * 2 ^ (a - j) + s) j
    sk :: auth

/-- `ADRS.setTreeHeight(z); ADRS.setTreeIndex(i); H(PK.seed, ADRS, l ‖ r)`
    on the FORS tree address. -/
def forsH (adrs : Address) (z i : ℕ) (l r : Bytes) : Bytes :=
  hs.H ((adrs.setWord2 z).setWord3 i) l r

/-- FIPS 205 Algorithm 17 `fors_pkFromSig(SIG_FORS, md, PK.seed, ADRS)`;
    `getSK(SIG_FORS, i)` is block `i·(a+1)`, `getAUTH(SIG_FORS, i)[j]` is
    block `i·(a+1) + 1 + j`. -/
def fipsForsPkFromSig (sig : List Bytes) (md : Bytes) (adrs : Address) : Bytes :=
  let indices := fipsBase2b md a k
  let roots := (List.range k).map fun i =>
    let sk := sig.getD (i * (a + 1)) []
    let node0 := hs.F ((adrs.setWord2 0).setWord3 (i * 2 ^ a + indices.getD i 0)) sk
    let auth := fun j => sig.getD (i * (a + 1) + 1 + j) []
    fipsRootLoop (forsH hs adrs) a (indices.getD i 0) (i * 2 ^ a + indices.getD i 0) auth node0
  let forspkADRS := (adrs.setTypeAndClear FORS_ROOTS).setKeyPair adrs.keypair
  hs.T forspkADRS roots

end Spec

/-! ## Code models -/

section Code

variable (thash : Address → List Bytes → Bytes) (prf : Address → Bytes) (w n k a : ℕ)

/-- `message_to_fors_indices message` at `int` width `w`, as the list of
    (non-negative) indices the loops read with `indices.(tree)`. -/
def indicesOf (message : Bytes) : List ℕ :=
  ((messageToForsIndices w a k message).getD []).map Int.toNat

/-- `fors_leaf context base_address index` (lines 410–415). -/
def forsLeaf (base : Address) (index : ℕ) : Bytes :=
  let address := { withType 6 base with field1 := 0, field2 := index }
  let secret := prf address
  thash { address with typ := 3 } [secret]

/-- `fors_sign context base_address message` (lines 417–439): the
    signature blocks and the FORS public key `thash (keypair_address 4 …)
    roots`, or `none` if some `treehash` would raise. -/
def forsSign (base : Address) (message : Bytes) : Option (List Bytes × Bytes) := do
  let indices := indicesOf w k a message
  let treeAddress := keypairAddress 3 base
  let perTree ← (List.range k).mapM fun tree => do
    let indexOffset := tree <<< a
    let selected := indices.getD tree 0 + indexOffset
    let secretAddress := { treeAddress with typ := 6, field1 := 0, field2 := selected }
    let secret := prf secretAddress
    let (root, authentication) ← treehash thash n a (indices.getD tree 0 : ℤ) indexOffset
      treeAddress (forsLeaf thash prf treeAddress) []
    pure (secret :: (List.range a).map (fun j => (authentication j).getD (List.replicate n 0)),
      root)
  let publicKeyAddress := keypairAddress 4 base
  pure (perTree.flatMap Prod.fst, thash publicKeyAddress (perTree.map Prod.snd))

/-- `fors_public_key_from_signature context base_address message signature`
    (lines 441–461). -/
def forsPublicKeyFromSignature (base : Address) (message : Bytes) (signature : List Bytes) :
    Bytes :=
  let indices := indicesOf w k a message
  let treeAddress := keypairAddress 3 base
  let roots := (List.range k).map fun tree =>
    let indexOffset := tree <<< a
    let selected := indices.getD tree 0 + indexOffset
    let secret := signature.getD (tree * (a + 1)) []
    let authentication := fun j => signature.getD (tree * (a + 1) + 1 + j) []
    let leafAddress := { treeAddress with field1 := 0, field2 := selected }
    let leaf := thash leafAddress [secret]
    computeRoot thash a indexOffset treeAddress leaf (indices.getD tree 0) authentication
  thash (keypairAddress 4 base) roots

end Code

/-! ## Theorems -/

variable (thash : Address → List Bytes → Bytes) (prf : Address → Bytes)

/-- The FIPS FORS address of Algorithm 19 lines 11–13
    (`setTypeAndClear(FORS_TREE); setKeyPairAddress(idx_leaf)`) is the
    code's `keypair_address 3`. -/
theorem forsAdrs_eq (base : Address) :
    keypairAddress 3 base = (base.setTypeAndClear FORS_TREE).setKeyPair base.keypair := rfl

/-- **`fors_leaf` = `fors_node(i, 0)`** (Algorithms 14–15) on the FORS tree
    address `keypair_address 3 base`. -/
theorem forsLeaf_eq (base : Address) (i : ℕ) :
    forsLeaf thash prf (keypairAddress 3 base) i =
      fipsForsNode (Tweak.ofCode thash prf) (keypairAddress 3 base) i 0 := rfl

/-- **`treehash`'s node = `fors_node`** (Algorithm 15) for every height and
    index. -/
theorem specNode_eq_forsNode (base : Address) :
    ∀ z i, specNode thash (keypairAddress 3 base) (forsLeaf thash prf (keypairAddress 3 base)) i z =
      fipsForsNode (Tweak.ofCode thash prf) (keypairAddress 3 base) i z := by
  intro z
  induction z with
  | zero => intro i; rfl
  | succ z ih =>
    intro i
    simp only [specNode, node] at ih ⊢
    rw [ih, ih]
    rfl

theorem indicesOf_eq (w k a : ℕ) (md : Bytes) (hw : a + 7 ≤ w) (hlen : k * a ≤ 8 * md.length) :
    indicesOf w k a md = fipsBase2b md a k := by
  simp [indicesOf, messageToForsIndices_eq w a k md hw hlen, List.map_map, Function.comp_def]

theorem index_lt (md : Bytes) (a k i : ℕ) : (fipsBase2b md a k).getD i 0 < 2 ^ a := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (fipsBase2b md a k)[i]? with
  | none => simp
  | some d => exact fipsBase2b_lt md a k 0 0 0 d (List.mem_of_getElem? h)

theorem getD_flatMap_range {β : Type} (f : ℕ → List β) (m : ℕ) (hf : ∀ i, (f i).length = m) :
    ∀ (k i j : ℕ) (d : β), i < k → j < m →
      ((List.range k).flatMap f).getD (i * m + j) d = (f i).getD j d := by
  intro k
  induction k with
  | zero => intro i j d hi; omega
  | succ k ih =>
    intro i j d hi hj
    have hlen : ((List.range k).flatMap f).length = k * m := by
      clear ih; induction k with
      | zero => simp
      | succ k ihk => simp [List.range_succ, List.flatMap_append, hf]; ring
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have : i * m + j < k * m := by nlinarith
      rw [List.getD_append _ _ _ _ (by omega), ih i j d hi hj]
    · rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.add_sub_cancel_left]

theorem mul_pow_shiftRight (i a j : ℕ) (hj : j ≤ a) : (i * 2 ^ a) >>> j = i * 2 ^ (a - j) := by
  rw [Nat.shiftRight_eq_div_pow, show 2 ^ a = 2 ^ (a - j) * 2 ^ j by
    rw [← pow_add]; congr 1; omega, ← mul_assoc, Nat.mul_div_cancel _ (by positivity)]

/-- **FORS correctness**: `fors_pkFromSig(fors_sign(md)) = T_k(roots)` with
    `root_i = fors_node(i, a)`, for every digest and every tweakable hash,
    on the FORS address `keypair_address 3 base` the code uses. -/
theorem fipsFors_correct (k a : ℕ) (md : Bytes) (base : Address) :
    fipsForsPkFromSig (Tweak.ofCode thash prf) k a
        (fipsForsSign (Tweak.ofCode thash prf) k a md (keypairAddress 3 base)) md
        (keypairAddress 3 base) =
      thash (keypairAddress 4 base)
        ((List.range k).map fun i =>
          fipsForsNode (Tweak.ofCode thash prf) (keypairAddress 3 base) i a) := by
  unfold fipsForsPkFromSig
  dsimp only
  show thash _ (List.map _ _) = thash _ (List.map _ _)
  congr 1
  apply List.map_congr_left
  intro i hi
  have hik : i < k := List.mem_range.mp hi
  set ta := keypairAddress 3 base with hta
  set idx := (fipsBase2b md a k).getD i 0 with hidx
  have hidxlt : idx < 2 ^ a := index_lt md a k i
  have hlen : ∀ t, ((fun i =>
      fipsForsSkGen (Tweak.ofCode thash prf) ta (i * 2 ^ a + (fipsBase2b md a k).getD i 0) ::
        (List.range a).map fun j =>
          fipsForsNode (Tweak.ofCode thash prf) ta
            (i * 2 ^ (a - j) + ((fipsBase2b md a k).getD i 0 / 2 ^ j ^^^ 1)) j) t).length =
      a + 1 := by intro t; simp
  have hsk := getD_flatMap_range _ (a + 1) hlen k i 0 [] hik (by omega)
  have hauth : ∀ j, j < a →
      (fipsForsSign (Tweak.ofCode thash prf) k a md ta).getD (i * (a + 1) + 1 + j) [] =
        fipsForsNode (Tweak.ofCode thash prf) ta (i * 2 ^ (a - j) + ((idx / 2 ^ j) ^^^ 1)) j := by
    intro j hj
    have := getD_flatMap_range _ (a + 1) hlen k i (j + 1) [] hik (by omega)
    rw [show i * (a + 1) + 1 + j = i * (a + 1) + (j + 1) by ring]
    unfold fipsForsSign
    rw [this, List.getD_cons_succ, List.getD_eq_getElem _ _ (by simpa using hj),
      List.getElem_map, List.getElem_range]
  rw [Nat.add_zero] at hsk
  have hleaf : (Tweak.ofCode thash prf).F ((ta.setWord2 0).setWord3 (i * 2 ^ a + idx))
      ((fipsForsSign (Tweak.ofCode thash prf) k a md ta).getD (i * (a + 1)) []) =
      forsLeaf thash prf ta (idx + i * 2 ^ a) := by
    unfold fipsForsSign
    rw [hsk, Nat.add_comm idx]
    rfl
  rw [hleaf]
  have hoff : 2 ^ a ∣ i * 2 ^ a := dvd_mul_left _ _
  have h1 := computeRoot_eq_fips thash a (i * 2 ^ a) ta hoff
    (forsLeaf thash prf ta (idx + i * 2 ^ a)) idx
    (fun j => (fipsForsSign (Tweak.ofCode thash prf) k a md ta).getD (i * (a + 1) + 1 + j) [])
  have hH : forsH (Tweak.ofCode thash prf) ta = nodeHash thash ta := rfl
  rw [hH, ← h1]
  have h2 := computeRoot_auth thash a (i * 2 ^ a) ta (forsLeaf thash prf ta) hoff idx hidxlt
  rw [mul_pow_shiftRight i a a le_rfl, Nat.sub_self, pow_zero, mul_one,
    specNode_eq_forsNode] at h2
  rw [← h2]
  unfold computeRoot
  apply List.foldl_ext
  intro node level hlev
  have hl : level < a := List.mem_range.mp hlev
  dsimp only
  rw [hauth level hl, specNode_eq_forsNode, mul_pow_shiftRight i a level hl.le]
  simp only [Nat.shiftRight_eq_div_pow]
  rfl

theorem mapM_some {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (l : List α), (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    rw [List.mapM_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    rfl

/-- **`fors_public_key_from_signature` = `fors_pkFromSig`** (Algorithm 17)
    for every signature and every digest with at least `k·a` bits, at every
    `int` width `w ≥ a + 7`, including the index arithmetic
    `(leaf_index lsr (level+1)) + (index_offset lsr (level+1))`,
    `index_offset = tree lsl a`, and the leaf address with tree index
    `indices.(tree) + index_offset`. -/
theorem forsPublicKeyFromSignature_eq (w k a : ℕ) (hw : a + 7 ≤ w) (base : Address)
    (md : Bytes) (hlen : k * a ≤ 8 * md.length) (sig : List Bytes) :
    forsPublicKeyFromSignature thash w k a base md sig =
      fipsForsPkFromSig (Tweak.ofCode thash prf) k a sig md (keypairAddress 3 base) := by
  unfold forsPublicKeyFromSignature fipsForsPkFromSig
  rw [indicesOf_eq w k a md hw hlen]
  dsimp only
  congr 1
  apply List.map_congr_left
  intro tree _
  rw [Nat.shiftLeft_eq, computeRoot_eq_fips thash a (tree * 2 ^ a) _ (dvd_mul_left _ _),
    Nat.add_comm ((fipsBase2b md a k).getD tree 0) (tree * 2 ^ a)]
  rfl

/-- **`fors_sign` = `fors_sign` + `fors_pkFromSig`.** For every digest with
    at least `k·a` bits and every `int` width `w ≥ a + 7`, the code's
    `fors_sign` does not raise, returns exactly the blocks of FIPS 205's
    `fors_sign` (Algorithm 16: `fors_skGen(i·2^a + indices[i])`, then
    `fors_node(i·2^(a−j) + s, j)`), and a public key equal to
    `fors_pkFromSig` of that signature (Algorithm 19 line 15), although the
    code takes it from `treehash`'s roots. -/
theorem forsSign_eq (w n k a : ℕ) (hw : a + 7 ≤ w) (base : Address) (md : Bytes)
    (hlen : k * a ≤ 8 * md.length) :
    forsSign thash prf w n k a base md =
      some (fipsForsSign (Tweak.ofCode thash prf) k a md (keypairAddress 3 base),
        fipsForsPkFromSig (Tweak.ofCode thash prf) k a
          (fipsForsSign (Tweak.ofCode thash prf) k a md (keypairAddress 3 base)) md
          (keypairAddress 3 base)) := by
  rw [fipsFors_correct]
  unfold forsSign
  rw [indicesOf_eq w k a md hw hlen]
  simp only [Nat.shiftLeft_eq]
  rw [mapM_some (g := fun tree =>
      ((fun i =>
          fipsForsSkGen (Tweak.ofCode thash prf) (keypairAddress 3 base)
              (i * 2 ^ a + (fipsBase2b md a k).getD i 0) ::
            (List.range a).map fun j =>
              fipsForsNode (Tweak.ofCode thash prf) (keypairAddress 3 base)
                (i * 2 ^ (a - j) + ((fipsBase2b md a k).getD i 0 / 2 ^ j ^^^ 1)) j) tree,
        fipsForsNode (Tweak.ofCode thash prf) (keypairAddress 3 base) tree a))]
  · simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, List.map_map,
      Function.comp_def, List.flatMap_map, fipsForsSign]
  · intro tree _
    have hidx := index_lt md a k tree
    rw [treehash_spec thash n a (tree * 2 ^ a) _ _ (dvd_mul_left _ _) _ (by omega)
      (by exact_mod_cast hidx)]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Int.toNat_natCast,
      mul_pow_shiftRight tree a a le_rfl, Nat.sub_self, pow_zero, mul_one,
      specNode_eq_forsNode, Option.some.injEq, Prod.mk.injEq, and_true]
    refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
    · rw [Nat.add_comm]; rfl
    · apply List.map_congr_left
      intro j hj
      have hjl : j < a := List.mem_range.mp hj
      simp [hjl, mul_pow_shiftRight tree a j hjl.le, Nat.shiftRight_eq_div_pow]

end OcamlPq.SLHDSA.FORS
