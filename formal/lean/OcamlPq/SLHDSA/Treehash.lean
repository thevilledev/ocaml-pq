import OcamlPq.SLHDSA.Basic

/-!
# SLH-DSA: `treehash` and `compute_root`

Model of the stack-based Merkle-tree traversal `treehash`
(slhdsa_engine.ml 337–370) and of the authentication-path root computation
`compute_root` (372–392), proved equal to the recursive node definitions of
FIPS 205 (`xmss_node`, Algorithm 9; `fors_node`, Algorithm 15), to the
authentication paths of `xmss_sign`/`fors_sign` (Algorithms 10, 16), and to
the root loops of `xmss_pkFromSig`/`fors_pkFromSig` (Algorithms 11, 17).

The node values are an arbitrary type `α` (in the code, `n`-byte strings)
and the tweakable hash `thash` is an arbitrary function of the address and
the list of input blocks, so every theorem holds for every hash function and
every leaf generator.

## Representation

* The two parallel arrays `stack` and `heights` (each of length
  `height + 1`) together with `offset` are modelled by a list of
  `(value, height)` pairs, top of the stack first; array slot `i < offset`
  holds the list element at position `offset - 1 - i`. Slots at or above
  `offset` are never read before being written, so they are not modelled.
  The only array write that can go out of bounds is the leaf push at
  `stack.(!offset)` (line 343); the model checks it (`offset < height + 1`)
  and fails (`none`) when OCaml would raise `Invalid_argument`.
* The `authentication` buffer (`height * n` bytes, initially zero) is
  modelled slot-wise: slot `j` (bytes `j*n ..< (j+1)*n`) is `none` while it
  still holds zero bytes and `some v` after `v` was blitted there. The blit
  (lines 347, 366–367) is checked against the buffer length exactly as
  `Bytes.blit_string` does, and fails (`none`) when OCaml would raise.
* `leaf_index` is an OCaml `int` and may be negative (`merkle_root` passes
  `-1`); it is modelled as `ℤ`. For non-negative values `lxor`/`lsr` agree
  with the `ℕ` operations on `L.toNat`, and the `leaf_index >= 0 && …`
  guard short-circuits otherwise. `index`, `index_offset` and all heights
  are non-negative `int`s, modelled as `ℕ`; `Portability.lean` shows they
  stay below `2^30`.
-/

namespace OcamlPq.SLHDSA.Treehash

open Address

variable {α : Type}

/-- The authentication buffer, slot-wise (see the module doc). -/
abbrev AuthBuf (α : Type) := ℕ → Option α

/-! ## Model -/

section Model

variable (thash : Address → List α → α) (n height : ℕ) (L : ℤ) (off : ℕ) (ta : Address)
  (gen : ℕ → α)

/-- `if cond then Bytes.blit_string v 0 authentication (slot * P.n) P.n`
    (lines 346–347 and 362–367). `Bytes.blit_string` raises unless
    `slot * n + n ≤ height * n`; that is modelled as `none`. -/
def blitIf (cond : Bool) (slot : ℕ) (v : α) (auth : AuthBuf α) : Option (AuthBuf α) :=
  if cond then
    if slot * n + n ≤ height * n then some (Function.update auth slot (some v)) else none
  else some auth

/-- The inner `while` loop of `treehash` (lines 348–368) for the leaf
    `index`: while the two topmost entries have equal heights, replace them
    by their parent, then capture the parent into the authentication buffer
    if it is the sibling of the signed path at its height. -/
def mergeLoop (index : ℕ) : List (α × ℕ) → AuthBuf α → Option (List (α × ℕ) × AuthBuf α)
  | (v1, h1) :: (v2, h2) :: rest, auth =>
    if h1 = h2 then
      let nodeHeight := h1
      let treeIndex := index >>> (nodeHeight + 1)
      let address := ta.setFields (nodeHeight + 1) (treeIndex + (off >>> (nodeHeight + 1)))
      let w := thash address [v2, v1]
      match blitIf n height
          (decide (0 ≤ L) && ((L.toNat >>> (nodeHeight + 1)) ^^^ 1 == treeIndex))
          (nodeHeight + 1) w auth with
      | none => none
      | some auth' => mergeLoop index ((w, nodeHeight + 1) :: rest) auth'
    else some ((v1, h1) :: (v2, h2) :: rest, auth)
  | st, auth => some (st, auth)
termination_by st => st.length

/-- One iteration of the outer `for` loop of `treehash` (lines 343–368):
    push leaf `index`, capture it if it is the sibling of `leaf_index`, then
    run the merge loop. -/
def step (s : List (α × ℕ) × AuthBuf α) (index : ℕ) : Option (List (α × ℕ) × AuthBuf α) :=
  if s.1.length < height + 1 then
    let leaf := gen (index + off)
    match blitIf n height (decide (0 ≤ L) && (L.toNat ^^^ 1 == index)) 0 leaf s.2 with
    | none => none
    | some auth => mergeLoop thash n height L off ta index ((leaf, 0) :: s.1) auth
  else none

/-- `treehash context ~leaf_index ~index_offset ~height ~tree_address gen_leaf`
    (lines 337–370). Returns `stack.(0)` and the authentication buffer, or
    `none` if the OCaml code would raise. `empty` is the initial `""` of the
    stack array (only returned if the loop ran zero times, which it never
    does). -/
def treehash (empty : α) : Option (α × AuthBuf α) := do
  let s ← (List.range (2 ^ height)).foldlM (step thash n height L off ta gen) ([], fun _ => none)
  pure ((s.1.getLast?.map Prod.fst).getD empty, s.2)

/-- `compute_root context ~leaf ~leaf_index ~index_offset ~height
    ~authentication ~tree_address` (lines 372–392). `auth level` is
    `sub authentication (level * P.n) P.n`. -/
def computeRoot (leaf : α) (leafIndex : ℕ) (auth : ℕ → α) : α :=
  (List.range height).foldl
    (fun node level =>
      let sibling := auth level
      let blocks := if (leafIndex >>> level) &&& 1 = 0 then [node, sibling] else [sibling, node]
      let address :=
        ta.setFields (level + 1) ((leafIndex >>> (level + 1)) + (off >>> (level + 1)))
      thash address blocks)
    leaf

end Model

/-! ## Specification (FIPS 205) -/

section Spec

/-- `H(PK.seed, ADRS, l ‖ r)` after `ADRS.setTreeHeight(z)`,
    `ADRS.setTreeIndex(i)` on the tree address `ta`. -/
def nodeHash (thash : Address → List α → α) (ta : Address) (z i : ℕ) (l r : α) : α :=
  thash (ta.setFields z i) [l, r]

/-- FIPS 205 Algorithm 9 (`xmss_node`) and Algorithm 15 (`fors_node`): the
    node with index `i` at height `z`. The leaf computation (WOTS+ public key
    for XMSS, `F(PK.seed, ADRS, fors_skGen(i))` for FORS) is the parameter
    `leaf`, and the parent hash is `H z i lnode rnode`. -/
def node (leaf : ℕ → α) (H : ℕ → ℕ → α → α → α) : ℕ → ℕ → α
  | i, 0 => leaf i
  | i, z + 1 => H (z + 1) i (node leaf H (2 * i) z) (node leaf H (2 * i + 1) z)

/-- The root loop shared by FIPS 205 Algorithm 11 (`xmss_pkFromSig`,
    lines 4–16) and Algorithm 17 (`fors_pkFromSig`, lines 7–18), written with
    the same mutable tree-index register as the standard:
    `if ⌊idx/2^k⌋ is even then setTreeIndex(getTreeIndex()/2);
       node ← H(node ‖ AUTH[k]) else setTreeIndex((getTreeIndex() − 1)/2);
       node ← H(AUTH[k] ‖ node)`. -/
def fipsRootLoop (H : ℕ → ℕ → α → α → α) (height idx treeIndex0 : ℕ) (auth : ℕ → α)
    (node0 : α) : α :=
  ((List.range height).foldl
    (fun (s : α × ℕ) k =>
      if (idx / 2 ^ k) % 2 = 0 then
        let ti := s.2 / 2
        (H (k + 1) ti s.1 (auth k), ti)
      else
        let ti := (s.2 - 1) / 2
        (H (k + 1) ti (auth k) s.1, ti))
    (node0, treeIndex0)).1

end Spec

/-! ## Arithmetic helpers -/

theorem xor_one_eq (x : ℕ) : x ^^^ 1 = if x % 2 = 0 then x + 1 else x - 1 := by
  split_ifs with h
  · exact Nat.xor_one_of_even (Nat.even_iff.mpr h)
  · exact Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))

theorem shiftRight_succ' (x t : ℕ) : x >>> (t + 1) = (x >>> t) / 2 := by
  simp [Nat.shiftRight_eq_div_pow, pow_succ, Nat.div_div_eq_div_mul]

theorem shiftRight_of_dvd {b t : ℕ} (h : 2 ^ (t + 1) ∣ b) : b >>> t = 2 * (b >>> (t + 1)) := by
  obtain ⟨q, rfl⟩ := h
  simp only [Nat.shiftRight_eq_div_pow]
  have h1 : 2 ^ (t + 1) * q / 2 ^ t = 2 * q := by
    rw [pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
  rw [h1, Nat.mul_div_cancel_left _ (by positivity)]

theorem shiftRight_even_of_dvd {b t : ℕ} (h : 2 ^ (t + 1) ∣ b) : (b >>> t) % 2 = 0 := by
  rw [shiftRight_of_dvd h]; omega

theorem shiftRight_add_pow {b t : ℕ} (h : 2 ^ t ∣ b) : (b + 2 ^ t) >>> t = (b >>> t) + 1 := by
  obtain ⟨q, rfl⟩ := h
  simp only [Nat.shiftRight_eq_div_pow]
  have hp : 0 < 2 ^ t := by positivity
  rw [show 2 ^ t * q + 2 ^ t = 2 ^ t * (q + 1) by ring, Nat.mul_div_cancel_left _ hp,
    Nat.mul_div_cancel_left _ hp]

theorem shiftRight_add_pred {b t : ℕ} (h : 2 ^ t ∣ b) : (b + 2 ^ t - 1) >>> t = b >>> t := by
  obtain ⟨q, rfl⟩ := h
  simp only [Nat.shiftRight_eq_div_pow]
  have hp : 0 < 2 ^ t := by positivity
  rw [Nat.mul_div_cancel_left _ hp, show 2 ^ t * q + 2 ^ t - 1 = (2 ^ t - 1) + 2 ^ t * q by omega,
    Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega), zero_add]

theorem dvd_of_dvd_pow {b s t : ℕ} (hst : s ≤ t) (h : 2 ^ t ∣ b) : 2 ^ s ∣ b :=
  (Nat.pow_dvd_pow 2 hst).trans h

/-! ## `blitIf` and `mergeLoop` basics -/

section Lemmas

variable (thash : Address → List α → α) (n height : ℕ) (L : ℤ) (off : ℕ) (ta : Address)
  (gen : ℕ → α)

/-- The capture condition at height `t` for tree index `i`. -/
def hit (L : ℤ) (t i : ℕ) : Bool := decide (0 ≤ L) && ((L.toNat >>> t) ^^^ 1 == i)

theorem blitIf_of_lt {c : Bool} {slot : ℕ} (hs : slot < height) (v : α)
    (auth : AuthBuf α) :
    blitIf n height c slot v auth =
      some (if c then Function.update auth slot (some v) else auth) := by
  unfold blitIf
  have : slot * n + n ≤ height * n := by
    have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hs); simpa [Nat.succ_mul] using this
  cases c <;> simp [this]

theorem blitIf_false {slot : ℕ} (v : α) (auth : AuthBuf α) :
    blitIf n height false slot v auth = some auth := by
  simp [blitIf]

theorem blitIf_true_ge {slot : ℕ} (hn : 0 < n) (hs : height ≤ slot) (v : α)
    (auth : AuthBuf α) : blitIf n height true slot v auth = none := by
  unfold blitIf
  have : ¬ slot * n + n ≤ height * n := by
    have := Nat.mul_le_mul_right n hs; omega
  simp [this]

theorem mergeLoop_noMerge (index : ℕ) (v : α) (t : ℕ) (S : List (α × ℕ))
    (hS : ∀ e ∈ S.head?, e.2 ≠ t) (auth : AuthBuf α) :
    mergeLoop thash n height L off ta index ((v, t) :: S) auth = some ((v, t) :: S, auth) := by
  match S, hS with
  | [], _ => simp [mergeLoop]
  | (v2, h2) :: rest, hS =>
    have : t ≠ h2 := fun h => hS _ rfl h.symm
    rw [mergeLoop]; simp [this]

theorem mergeLoop_merge (index : ℕ) (v1 v2 : α) (t : ℕ) (rest : List (α × ℕ))
    (auth : AuthBuf α) :
    mergeLoop thash n height L off ta index ((v1, t) :: (v2, t) :: rest) auth =
      (blitIf n height (hit L (t + 1) (index >>> (t + 1))) (t + 1)
          (thash (ta.setFields (t + 1) ((index >>> (t + 1)) + (off >>> (t + 1)))) [v2, v1])
          auth).bind
        (fun auth' => mergeLoop thash n height L off ta index
          ((thash (ta.setFields (t + 1) ((index >>> (t + 1)) + (off >>> (t + 1)))) [v2, v1],
            t + 1) :: rest) auth') := by
  rw [mergeLoop]
  simp only [↓reduceIte, hit]
  cases blitIf n height _ _ _ auth <;> rfl

theorem mergeLoop_single (index : ℕ) (e : α × ℕ) (auth : AuthBuf α) :
    mergeLoop thash n height L off ta index [e] auth = some ([e], auth) := by
  obtain ⟨v, t⟩ := e; simp [mergeLoop]

end Lemmas

/-! ## The block lemma -/

section Block

variable (thash : Address → List α → α) (n height : ℕ) (L : ℤ) (off : ℕ) (ta : Address)
  (gen : ℕ → α)

/-- The specification node, with the code's leaf generator and parent hash. -/
abbrev specNode (i z : ℕ) : α := node gen (nodeHash thash ta) i z

/-- A node of the subtree being built, addressed by its index local to the
    subtree (the code's `index lsr height`); its global index adds
    `index_offset lsr height`. -/
abbrev lnode (i t : ℕ) : α := specNode thash ta gen ((off >>> t) + i) t

theorem lnode_zero (i : ℕ) : lnode thash off ta gen i 0 = gen (i + off) := by
  simp [lnode, specNode, node, Nat.add_comm]

theorem lnode_succ {t : ℕ} (hoff : 2 ^ (t + 1) ∣ off) (i : ℕ) :
    lnode thash off ta gen i (t + 1) =
      thash (ta.setFields (t + 1) ((off >>> (t + 1)) + i))
        [lnode thash off ta gen (2 * i) t, lnode thash off ta gen (2 * i + 1) t] := by
  simp only [lnode, specNode, node, nodeHash]
  rw [shiftRight_of_dvd hoff]
  congr 3 <;> simp only [Nat.mul_add, Nat.add_assoc]

/-- The captures performed while a block of `2^t` leaves starting at `b` is
    processed, excluding the capture of the block's own root: recursively,
    the captures of the left half, of the left child, of the right half and
    of the right child. (A specification-side device for the proof.) -/
def recB : ℕ → ℕ → AuthBuf α → Option (AuthBuf α)
  | 0, _, auth => some auth
  | t + 1, b, auth =>
    (recB t b auth).bind fun a1 =>
      (blitIf n height (hit L t (b >>> t)) t (lnode thash off ta gen (b >>> t) t) a1).bind
        fun a2 =>
          (recB t (b + 2 ^ t) a2).bind fun a3 =>
            blitIf n height (hit L t ((b >>> t) + 1)) t
              (lnode thash off ta gen ((b >>> t) + 1) t) a3

/-- **Block lemma.** Processing the `2^t` consecutive leaves starting at an
    aligned `b` from a stack `S` whose top is higher than `t - 1` has the
    same effect as: performing all captures inside the block, capturing
    the block root, and pushing the block root through the merge loop. -/
theorem foldlM_block (hoff : 2 ^ height ∣ off) :
    ∀ (t b : ℕ) (S : List (α × ℕ)) (auth : AuthBuf α),
      2 ^ t ∣ b → (∀ e ∈ S.head?, t ≤ e.2) → S.length + t ≤ height →
      (List.range' b (2 ^ t)).foldlM (step thash n height L off ta gen) (S, auth) =
        (recB thash n height L off ta gen t b auth).bind fun a1 =>
          (blitIf n height (hit L t (b >>> t)) t (lnode thash off ta gen (b >>> t) t) a1).bind
            fun a2 =>
              mergeLoop thash n height L off ta (b + 2 ^ t - 1)
                ((lnode thash off ta gen (b >>> t) t, t) :: S) a2 := by
  intro t
  induction t with
  | zero =>
    intro b S auth _ _ hlen
    simp only [pow_zero, List.range'_one, List.foldlM_cons, List.foldlM_nil, recB,
      Option.bind_some, Nat.shiftRight_zero, lnode_zero, hit, Nat.add_sub_cancel, bind_pure]
    simp only [step]
    simp only [show S.length < height + 1 by omega, ↓reduceIte]
    cases blitIf n height _ 0 _ auth <;> simp [Option.bind]
  | succ t ih =>
    intro b S auth hb hS hlen
    have hbt : 2 ^ t ∣ b := dvd_of_dvd_pow (Nat.le_succ t) hb
    have hoff' : 2 ^ (t + 1) ∣ off := dvd_of_dvd_pow (by omega) hoff
    rw [show 2 ^ (t + 1) = 2 ^ t + 2 ^ t by ring, ← List.range'_append_1, List.foldlM_append,
      ih b S auth hbt (fun e he => by have := hS e he; omega) (by omega)]
    simp only [recB, Option.bind_assoc, Option.bind_eq_bind]
    refine Option.bind_congr (fun a1 _ => ?_)
    refine Option.bind_congr (fun a2 _ => ?_)
    rw [mergeLoop_noMerge thash n height L off ta _ _ t S
      (fun e he => by have := hS e he; omega), Option.bind_some,
      ih (b + 2 ^ t) _ a2 (Nat.dvd_add hbt dvd_rfl) (by simp) (by simp; omega)]
    refine Option.bind_congr (fun a3 _ => ?_)
    rw [shiftRight_add_pow hbt]
    refine Option.bind_congr (fun a4 _ => ?_)
    rw [mergeLoop_merge]
    have hidx : b + 2 ^ t + 2 ^ t - 1 = b + (2 ^ t + 2 ^ t) - 1 := by omega
    rw [hidx, ← show 2 ^ (t + 1) = 2 ^ t + 2 ^ t by ring, shiftRight_add_pred hb]
    have hw : thash (ta.setFields (t + 1) ((b >>> (t + 1)) + (off >>> (t + 1))))
        [lnode thash off ta gen (b >>> t) t, lnode thash off ta gen ((b >>> t) + 1) t] =
        lnode thash off ta gen (b >>> (t + 1)) (t + 1) := by
      rw [lnode_succ thash off ta gen hoff', shiftRight_of_dvd hb, Nat.add_comm (off >>> _)]
    rw [hw]

end Block

/-! ## The captures made inside a block -/

section Captures

variable (thash : Address → List α → α) (n height : ℕ) (L : ℤ) (off : ℕ) (ta : Address)
  (gen : ℕ → α)

/-- The authentication buffer after all captures inside the block of height
    `t` at `b`: slot `j < t` receives the sibling of the signed path at
    height `j` iff the signed leaf lies in the block. -/
def capB (t b : ℕ) (auth : AuthBuf α) : AuthBuf α := fun j =>
  if j < t ∧ 0 ≤ L ∧ L.toNat >>> t = b >>> t then
    some (lnode thash off ta gen ((L.toNat >>> j) ^^^ 1) j)
  else auth j

theorem xor_one_eq_even {X B : ℕ} (hB : B % 2 = 0) : X ^^^ 1 = B ↔ X = B + 1 := by
  rw [xor_one_eq]; split_ifs <;> omega

theorem xor_one_eq_even_succ {X B : ℕ} (hB : B % 2 = 0) : X ^^^ 1 = B + 1 ↔ X = B := by
  rw [xor_one_eq]; split_ifs <;> omega

theorem recB_eq : ∀ (t b : ℕ) (auth : AuthBuf α), 2 ^ t ∣ b → t ≤ height →
    recB thash n height L off ta gen t b auth = some (capB thash L off ta gen t b auth) := by
  intro t
  induction t with
  | zero =>
    intro b auth _ _
    simp only [recB]
    congr 1
  | succ t ih =>
    intro b auth hb ht
    have hbt : 2 ^ t ∣ b := dvd_of_dvd_pow (Nat.le_succ t) hb
    have hB := shiftRight_even_of_dvd hb
    simp only [recB]
    rw [ih b auth hbt (by omega), Option.bind_some,
      blitIf_of_lt n height (by omega : t < height), Option.bind_some,
      ih (b + 2 ^ t) _ (Nat.dvd_add hbt dvd_rfl) (by omega), Option.bind_some,
      blitIf_of_lt n height (by omega : t < height)]
    congr 1
    funext j
    have hLt : L.toNat >>> (t + 1) = (L.toNat >>> t) / 2 := shiftRight_succ' _ _
    have hbt1 : b >>> (t + 1) = (b >>> t) / 2 := shiftRight_succ' _ _
    by_cases hL : 0 ≤ L
    · -- Classify the position of the signed leaf relative to the two halves.
      unfold capB
      simp only [ite_apply, Function.update_apply, hit, hL, decide_true, Bool.true_and,
        beq_iff_eq, true_and, shiftRight_add_pow hbt, hLt, hbt1]
      set X := L.toNat >>> t with hX
      set B := b >>> t with hBdef
      have e1 := xor_one_eq_even (X := X) hB
      have e2 := xor_one_eq_even_succ (X := X) hB
      have hBx : B ^^^ 1 = B + 1 := (xor_one_eq_even_succ hB).mpr rfl
      have hB1x : (B + 1) ^^^ 1 = B := (xor_one_eq_even hB).mpr rfl
      have hB2 : (B + 1) / 2 = B / 2 := by omega
      rcases lt_trichotomy j t with hj | rfl | hj
      · have : j < t + 1 := by omega
        have hjt : j ≠ t := Nat.ne_of_lt hj
        by_cases hxb : X = B
        · have h1 : ¬ X ^^^ 1 = B := by rw [e1]; omega
          have h3 : X / 2 = B / 2 := by omega
          simp [hj, this, hxb, hBx, hjt]
        · by_cases hxb1 : X = B + 1
          · have h2 : ¬ X ^^^ 1 = B + 1 := by rw [e2]; omega
            have h3 : X / 2 = B / 2 := by omega
            simp [hj, this, hxb1, hB1x, hB2]
          · have h1 : ¬ X ^^^ 1 = B := by rw [e1]; omega
            have h2 : ¬ X ^^^ 1 = B + 1 := by rw [e2]; omega
            have h3 : ¬ X / 2 = B / 2 := by omega
            simp [hj, this, hxb, hxb1, h1, h2, h3]
      · by_cases hxb : X = B
        · have h1 : ¬ X ^^^ 1 = B := by rw [e1]; omega
          have h2 : X ^^^ 1 = B + 1 := by rw [e2]; exact hxb
          have h3 : X / 2 = B / 2 := by omega
          simp [hxb, hBx]
          rw [← hX, h2]
        · by_cases hxb1 : X = B + 1
          · have h1 : X ^^^ 1 = B := by rw [e1]; exact hxb1
            have h2 : ¬ X ^^^ 1 = B + 1 := by rw [e2]; omega
            have h3 : X / 2 = B / 2 := by omega
            simp [hxb1, hB1x, hB2]
            rw [← hX, h1]
          · have h1 : ¬ X ^^^ 1 = B := by rw [e1]; omega
            have h2 : ¬ X ^^^ 1 = B + 1 := by rw [e2]; omega
            have h3 : ¬ X / 2 = B / 2 := by omega
            simp [h1, h2, h3]
      · have h4 : ¬ j < t + 1 := by omega
        have h5 : ¬ j < t := by omega
        simp [h4, h5, Nat.ne_of_gt hj]
    · simp [hit, capB, hL]

end Captures

/-! ## Main theorems about `treehash` -/

section Main

variable (thash : Address → List α → α) (n height : ℕ) (off : ℕ) (ta : Address)
  (gen : ℕ → α)

/-- `treehash` unfolded through the block lemma for the whole tree. -/
theorem treehash_eq (L : ℤ) (hoff : 2 ^ height ∣ off) (empty : α) :
    treehash thash n height L off ta gen empty =
      (blitIf n height (hit L height 0) height (specNode thash ta gen (off >>> height) height)
          (capB thash L off ta gen height 0 (fun _ => none))).bind
        fun a => some (specNode thash ta gen (off >>> height) height, a) := by
  unfold treehash
  rw [List.range_eq_range', foldlM_block thash n height L off ta gen hoff height 0 [] _
      (dvd_zero _) (by simp) (by simp),
    recB_eq thash n height L off ta gen height 0 _ (dvd_zero _) le_rfl]
  simp only [Option.bind_some, Nat.zero_shiftRight, Option.bind_eq_bind]
  cases blitIf n height _ _ _ _ with
  | none => rfl
  | some a =>
    simp only [Option.bind_some, mergeLoop_single, List.getLast?_singleton, Option.map_some,
      Option.getD_some, Option.pure_def, lnode, Nat.add_zero]

/-- **`treehash` correctness.** For every height, every leaf generator and
    hash, every `index_offset` that is a multiple of `2^height`, and every
    `leaf_index ∈ [0, 2^height)`: `treehash` does not raise (in particular
    the stack never exceeds `height + 1` entries and no blit is out of
    bounds), returns the FIPS 205 node of height `height` with index
    `index_offset / 2^height` (Algorithms 9/15), and fills slot `j` of the
    authentication path, for every `j < height`, with the node of height `j`
    and index `index_offset / 2^j + (⌊leaf_index / 2^j⌋ ⊕ 1)`
    (Algorithms 10/16: `xmss_node(⌊idx/2^j⌋ ⊕ 1, j)` and
    `fors_node(i·2^(a−j) + s, j)`). -/
theorem treehash_spec (hoff : 2 ^ height ∣ off) (L : ℤ) (hL0 : 0 ≤ L) (hL : L < 2 ^ height)
    (empty : α) :
    treehash thash n height L off ta gen empty =
      some (specNode thash ta gen (off >>> height) height,
        fun j => if j < height then
          some (specNode thash ta gen ((off >>> j) + ((L.toNat >>> j) ^^^ 1)) j) else none) := by
  have hLn : L.toNat < 2 ^ height := (Int.toNat_lt hL0).mpr (by exact_mod_cast hL)
  have hsh : L.toNat >>> height = 0 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hLn
  rw [treehash_eq thash n height off ta gen L hoff empty]
  have hhit : hit L height 0 = false := by simp [hit, hsh]
  rw [hhit, blitIf_false, Option.bind_some]
  congr 2
  funext j
  simp only [capB, hL0, hsh, Nat.zero_shiftRight, and_true]

/-- With `leaf_index < 0` (as passed by `merkle_root`), `treehash` returns
    the same root and leaves the authentication buffer all zero. -/
theorem treehash_neg (hoff : 2 ^ height ∣ off) (L : ℤ) (hL : L < 0) (empty : α) :
    treehash thash n height L off ta gen empty =
      some (specNode thash ta gen (off >>> height) height, fun _ => none) := by
  rw [treehash_eq thash n height off ta gen L hoff empty]
  have hL' : ¬ 0 ≤ L := by omega
  have hhit : hit L height 0 = false := by simp [hit, hL']
  rw [hhit, blitIf_false, Option.bind_some]
  congr 2
  funext j
  simp [capB, hL']

/-- Out-of-range `leaf_index ∈ [2^height, 2^(height+1))`: the root-level
    capture test `((leaf_index lsr height) lxor 1) = 0` succeeds and the
    blit at offset `height * n` overruns the `height * n`-byte buffer, so
    `Bytes.blit_string` raises `Invalid_argument`. -/
theorem treehash_raises (hn : 0 < n) (hoff : 2 ^ height ∣ off) (L : ℤ)
    (hL1 : 2 ^ height ≤ L) (hL2 : L < 2 ^ (height + 1)) (empty : α) :
    treehash thash n height L off ta gen empty = none := by
  rw [treehash_eq thash n height off ta gen L hoff empty]
  have hL0 : 0 ≤ L := le_trans (by positivity) hL1
  have hsh : L.toNat >>> height = 1 := by
    rw [Nat.shiftRight_eq_div_pow]
    have h1 : 2 ^ height ≤ L.toNat := (Int.le_toNat hL0).mpr (by exact_mod_cast hL1)
    have h2 : L.toNat < 2 ^ (height + 1) := (Int.toNat_lt hL0).mpr (by exact_mod_cast hL2)
    rw [pow_succ] at h2
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  have hhit : hit L height 0 = true := by simp [hit, hsh, hL0]
  rw [hhit, blitIf_true_ge n height hn le_rfl]
  rfl

/-- Out-of-range `leaf_index ≥ 2^(height+1)`: no test ever matches, so the
    root is returned with an all-zero authentication buffer. -/
theorem treehash_large (hoff : 2 ^ height ∣ off) (L : ℤ) (hL : 2 ^ (height + 1) ≤ L)
    (empty : α) :
    treehash thash n height L off ta gen empty =
      some (specNode thash ta gen (off >>> height) height, fun _ => none) := by
  rw [treehash_eq thash n height off ta gen L hoff empty]
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  have hsh : 2 ≤ L.toNat >>> height := by
    rw [Nat.shiftRight_eq_div_pow, Nat.le_div_iff_mul_le (by positivity)]
    have h1 : 2 ^ (height + 1) ≤ L.toNat := (Int.le_toNat hL0).mpr (by exact_mod_cast hL)
    have : 2 ^ (height + 1) = 2 * 2 ^ height := by ring
    omega
  have hhit : hit L height 0 = false := by
    simp only [hit, hL0, decide_true, Bool.true_and, beq_eq_false_iff_ne]
    rw [xor_one_eq]; split_ifs <;> omega
  rw [hhit, blitIf_false, Option.bind_some]
  congr 2
  funext j
  have : ¬ L.toNat >>> height = 0 := by omega
  simp [capB, this]

end Main

/-! ## `compute_root` -/

section ComputeRoot

variable (thash : Address → List α → α) (height : ℕ) (off : ℕ) (ta : Address)

theorem computeRoot_range (leaf : α) (L : ℕ) (auth : ℕ → α) (k : ℕ) :
    computeRoot thash (k + 1) off ta leaf L auth =
      thash (ta.setFields (k + 1) ((L >>> (k + 1)) + (off >>> (k + 1))))
        (if (L >>> k) &&& 1 = 0 then [computeRoot thash k off ta leaf L auth, auth k]
         else [auth k, computeRoot thash k off ta leaf L auth]) := by
  simp only [computeRoot, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **`compute_root` refines FIPS 205.** For every `index_offset` that is a
    multiple of `2^height` and every leaf index, the code's index arithmetic
    `(leaf_index lsr (level+1)) + (index_offset lsr (level+1))` and parity
    test produce exactly the root loop of Algorithms 11/17 started with tree
    index `index_offset + leaf_index` (`idx` for XMSS, `i·2^a + indices[i]`
    for FORS). -/
theorem computeRoot_eq_fips (hoff : 2 ^ height ∣ off) (leaf : α) (L : ℕ) (auth : ℕ → α) :
    computeRoot thash height off ta leaf L auth =
      fipsRootLoop (nodeHash thash ta) height L (off + L) auth leaf := by
  have key : ∀ k ≤ height,
      (List.range k).foldl
        (fun (s : α × ℕ) k =>
          if (L / 2 ^ k) % 2 = 0 then
            let ti := s.2 / 2
            (nodeHash thash ta (k + 1) ti s.1 (auth k), ti)
          else
            let ti := (s.2 - 1) / 2
            (nodeHash thash ta (k + 1) ti (auth k) s.1, ti))
        (leaf, off + L) =
      (computeRoot thash k off ta leaf L auth, (off + L) >>> k) := by
    intro k
    induction k with
    | zero => intro _; simp [computeRoot]
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        computeRoot_range]
      have hk1 : 2 ^ (k + 1) ∣ off := dvd_of_dvd_pow hk hoff
      have hk0 : 2 ^ k ∣ off := dvd_of_dvd_pow (by omega) hoff
      have hsplit : ∀ j, 2 ^ j ∣ off → (off + L) >>> j = (off >>> j) + (L >>> j) := by
        intro j hj
        simp only [Nat.shiftRight_eq_div_pow]; exact Nat.add_div_of_dvd_right hj
      have hoffe : (off >>> k) % 2 = 0 := shiftRight_even_of_dvd hk1
      have hLk : L / 2 ^ k = L >>> k := (Nat.shiftRight_eq_div_pow _ _).symm
      have hnext : (off + L) >>> (k + 1) = ((off + L) >>> k) / 2 := shiftRight_succ' _ _
      have hLs : L >>> (k + 1) = (L >>> k) / 2 := shiftRight_succ' _ _
      have hos : off >>> (k + 1) = (off >>> k) / 2 := shiftRight_succ' _ _
      rw [hsplit k hk0] at hnext ⊢
      rw [hsplit (k + 1) hk1] at hnext
      simp only [hLk, Nat.and_one_is_mod, nodeHash]
      split_ifs with h
      · have e : (off >>> k + L >>> k) / 2 = (L >>> (k + 1)) + (off >>> (k + 1)) := by
          rw [hLs, hos]
          generalize off >>> k = A at hoffe ⊢
          generalize L >>> k = B at h ⊢
          omega
        rw [hsplit (k + 1) hk1, e, Nat.add_comm (off >>> (k + 1))]
      · have e : (off >>> k + L >>> k - 1) / 2 = (L >>> (k + 1)) + (off >>> (k + 1)) := by
          rw [hLs, hos]
          generalize off >>> k = A at hoffe ⊢
          generalize L >>> k = B at h ⊢
          omega
        rw [hsplit (k + 1) hk1, e, Nat.add_comm (off >>> (k + 1))]
  unfold fipsRootLoop
  rw [key height le_rfl]

/-- **Sign/verify consistency of the tree layer.** Starting from the signed
    leaf and the authentication path `treehash` produces (slot `j` =
    `node(index_offset/2^j + (⌊leaf_index/2^j⌋ ⊕ 1), j)`), `compute_root`
    returns the root `treehash` returns, for every leaf index
    `< 2^height`. -/
theorem computeRoot_auth (gen : ℕ → α) (hoff : 2 ^ height ∣ off) (L : ℕ)
    (hL : L < 2 ^ height) :
    computeRoot thash height off ta (gen (L + off)) L
        (fun j => specNode thash ta gen ((off >>> j) + ((L >>> j) ^^^ 1)) j) =
      specNode thash ta gen (off >>> height) height := by
  have key : ∀ k ≤ height,
      computeRoot thash k off ta (gen (L + off)) L
          (fun j => specNode thash ta gen ((off >>> j) + ((L >>> j) ^^^ 1)) j) =
        lnode thash off ta gen (L >>> k) k := by
    intro k
    induction k with
    | zero => intro _; simp [computeRoot, lnode_zero]
    | succ k ih =>
      intro hk
      rw [computeRoot_range, ih (by omega)]
      have hk1 : 2 ^ (k + 1) ∣ off := dvd_of_dvd_pow hk hoff
      rw [lnode_succ thash off ta gen hk1]
      have hLs : L >>> (k + 1) = (L >>> k) / 2 := shiftRight_succ' _ _
      simp only [Nat.and_one_is_mod, lnode]
      rw [xor_one_eq, Nat.add_comm (L >>> (k + 1)), hLs]
      generalize L >>> k = X
      split_ifs with h
      · rw [show 2 * (X / 2) = X by omega]
      · rw [show 2 * (X / 2) + 1 = X by omega, show 2 * (X / 2) = X - 1 by omega]
  rw [key height le_rfl]
  simp only [lnode, Nat.shiftRight_eq_div_pow L, Nat.div_eq_of_lt hL, Nat.add_zero]

/-- The authentication buffer returned by `treehash` for a leaf index in
    range, read back slot by slot (as `sub authentication (level * n) n`
    does), makes `compute_root` recompute exactly the `treehash` root. -/
theorem computeRoot_treehash (n : ℕ) (gen : ℕ → α) (hoff : 2 ^ height ∣ off) (L : ℕ)
    (hL : L < 2 ^ height) (empty dflt : α) (root : α) (auth : AuthBuf α)
    (h : treehash thash n height (L : ℤ) off ta gen empty = some (root, auth)) :
    computeRoot thash height off ta (gen (L + off)) L (fun j => (auth j).getD dflt) = root := by
  rw [treehash_spec thash n height off ta gen hoff (L : ℤ) (by omega) (by exact_mod_cast hL)]
    at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [← computeRoot_auth thash height off ta gen hoff L hL]
  unfold computeRoot
  apply List.foldl_ext
  intro node level hlev
  have : level < height := List.mem_range.mp hlev
  simp [this]

end ComputeRoot

end OcamlPq.SLHDSA.Treehash
