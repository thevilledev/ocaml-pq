import OcamlPq.EndToEnd.SLHDSA.HashFunctions

/-!
# SLH-DSA end to end: the FIPS 205 algorithms only need F, H, T_ℓ, PRF on their call sites

The SLH-DSA area's FIPS 205 algorithms (`fipsChain` … `fipsHtVerifyNode`,
`fipsForsSign`, `fipsForsPkFromSig`) are parametrised by a tweakable hash
family `hs : Tweak`, and `Top` proves that the code computes them for
`hs = Tweak.ofCode thash prf`, the code's `thash`/`prf`. That family is
*not* equal, as a function, to FIPS 205 §11 over the specified primitives:

* `thash` picks SHA-256 or SHA-512 by the *number of blocks*, so its
  `T` on one block is `F`, not `T_1` (irrelevant: FIPS 205 calls `T_ℓ` only
  with `ℓ = len` and `ℓ = k`, both `≥ 2`);
* the OCaml SHA-512 differs from FIPS 180-4 SHA-512 on inputs of `2^61` or
  more bytes (irrelevant: every block the algorithms hash is an `n`-byte
  output or signature block).

`Agree S len k hs hs'` says that `hs` and `hs'` agree on every call the
algorithms make — every block satisfies a predicate `S` that holds for `[]`
and for every output of `hs`, and `T` is only called with `len` or `k`
blocks — and the theorems below show that each algorithm then gives the same
result under `hs` and `hs'` (and that its outputs satisfy `S`). This is
proved by following each algorithm's own recursion; no call site is
assumed.

`keygenRoot`, `signInternal` and `verifyInternal` are Algorithms 18–20 for an
arbitrary tweakable hash and message functions; the area's `Top.fipsKeygenRoot`,
`fipsSlhSignInternal`, `fipsSlhVerifyInternal` are these at the code's
family (by `rfl`).
-/

namespace OcamlPq.EndToEnd.SLHDSA

open OcamlPq.SLHDSA
open WOTS XMSS FORS Treehash Hypertree Base2b

/-- `hs` and `hs'` agree on every call the FIPS 205 algorithms make (see
    the module doc). -/
structure Agree (S : Bytes → Prop) (len k : ℕ) (hs hs' : Tweak) : Prop where
  nil : S []
  F : ∀ a m, S m → hs.F a m = hs'.F a m
  H : ∀ a l r, S l → S r → hs.H a l r = hs'.H a l r
  T : ∀ a (ms : List Bytes), (ms.length = len ∨ ms.length = k) → (∀ m ∈ ms, S m) →
    hs.T a ms = hs'.T a ms
  F_S : ∀ a m, S (hs.F a m)
  H_S : ∀ a l r, S (hs.H a l r)
  T_S : ∀ a ms, S (hs.T a ms)

/-- `PRF` agrees everywhere and its outputs satisfy `S` (signing and key
    generation; verification never calls `PRF`). -/
structure AgreePRF (S : Bytes → Prop) (hs hs' : Tweak) : Prop where
  eq : ∀ a, hs.PRF a = hs'.PRF a
  S : ∀ a, S (hs.PRF a)

section Congr

variable {S : Bytes → Prop} {len k : ℕ} {hs hs' : Tweak}

theorem Agree.getD (h : Agree S len k hs hs') {sig : List Bytes} (hsig : ∀ b ∈ sig, S b) (i : ℕ) :
    S (sig.getD i []) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : sig[i]? with
  | none => exact h.nil
  | some b => exact hsig b (List.mem_of_getElem? hi)

/-- A fold whose step functions agree on states satisfying an invariant. -/
theorem foldl_agree {β γ : Type} (I : β → Prop) (f f' : β → γ → β)
    (hf : ∀ s x, I s → f s x = f' s x) (hI : ∀ s x, I s → I (f s x)) :
    ∀ (l : List γ) (s : β), I s → l.foldl f s = l.foldl f' s ∧ I (l.foldl f s) := by
  intro l
  induction l with
  | nil => intro s hs; exact ⟨rfl, hs⟩
  | cons x l ih =>
    intro s hs
    simp only [List.foldl_cons]
    obtain ⟨e, hs'⟩ := ih (f s x) (hI s x hs)
    exact ⟨by rw [e, hf s x hs], hs'⟩

/-! ### WOTS+ (Algorithms 5–8) -/

theorem chain_eq (h : Agree S len k hs hs') (X : Bytes) (i s : ℕ) (adrs : Address) (hX : S X) :
    fipsChain hs X i s adrs = fipsChain hs' X i s adrs ∧ S (fipsChain hs X i s adrs) :=
  foldl_agree S _ _ (fun t _ ht => h.F _ t ht) (fun _ _ _ => h.F_S _ _) (List.range' i s) X hX

theorem wotsPkGen_eq (h : Agree S len k hs hs') (hp : AgreePRF S hs hs') (adrs : Address) :
    fipsWotsPkGen hs len adrs = fipsWotsPkGen hs' len adrs := by
  unfold fipsWotsPkGen
  dsimp only
  have hmap : ((List.range len).map fun i =>
        fipsChain hs (hs.PRF ((skAdrs adrs).setWord2 i)) 0 (16 - 1) (adrs.setWord2 i)) =
      ((List.range len).map fun i =>
        fipsChain hs' (hs'.PRF ((skAdrs adrs).setWord2 i)) 0 (16 - 1) (adrs.setWord2 i)) := by
    congr 1
    funext i
    rw [(chain_eq h _ _ _ _ (hp.S _)).1, hp.eq]
  rw [← hmap]
  apply h.T
  · left; simp
  · intro m hm
    simp only [List.mem_map] at hm
    obtain ⟨i, -, rfl⟩ := hm
    exact (chain_eq h _ _ _ _ (hp.S _)).2

theorem wotsSign_eq (h : Agree S len k hs hs') (hp : AgreePRF S hs hs') (n len' : ℕ) (M : Bytes)
    (adrs : Address) :
    fipsWotsSign hs n len' M adrs = fipsWotsSign hs' n len' M adrs ∧
      ∀ b ∈ fipsWotsSign hs n len' M adrs, S b := by
  unfold fipsWotsSign
  dsimp only
  refine ⟨?_, ?_⟩
  · congr 1
    funext i
    rw [(chain_eq h _ _ _ _ (hp.S _)).1, hp.eq]
  · intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨i, -, rfl⟩ := hb
    exact (chain_eq h _ _ _ _ (hp.S _)).2

theorem wotsPkFromSig_eq (h : Agree S len k hs hs') (n : ℕ) (sig : List Bytes)
    (hsig : ∀ b ∈ sig, S b) (M : Bytes) (adrs : Address) :
    fipsWotsPkFromSig hs n len sig M adrs = fipsWotsPkFromSig hs' n len sig M adrs ∧
      S (fipsWotsPkFromSig hs n len sig M adrs) := by
  unfold fipsWotsPkFromSig
  dsimp only
  refine ⟨?_, h.T_S _ _⟩
  have hmap : ((List.range len).map fun i =>
        fipsChain hs (sig.getD i []) ((fipsWotsDigits n M).getD i 0)
          (16 - 1 - (fipsWotsDigits n M).getD i 0) (adrs.setWord2 i)) =
      ((List.range len).map fun i =>
        fipsChain hs' (sig.getD i []) ((fipsWotsDigits n M).getD i 0)
          (16 - 1 - (fipsWotsDigits n M).getD i 0) (adrs.setWord2 i)) := by
    congr 1
    funext i
    rw [(chain_eq h _ _ _ _ (h.getD hsig i)).1]
  rw [← hmap]
  apply h.T
  · left; simp
  · intro m hm
    simp only [List.mem_map] at hm
    obtain ⟨i, -, rfl⟩ := hm
    exact (chain_eq h _ _ _ _ (h.getD hsig i)).2

/-! ### The root loop of Algorithms 11 and 17 -/

theorem rootLoop_eq {H H' : ℕ → ℕ → Bytes → Bytes → Bytes}
    (hH : ∀ z i l r, S l → S r → H z i l r = H' z i l r) (hHS : ∀ z i l r, S (H z i l r))
    (height idx ti0 : ℕ) (auth : ℕ → Bytes) (hauth : ∀ j, S (auth j)) (node0 : Bytes)
    (hn : S node0) :
    fipsRootLoop H height idx ti0 auth node0 = fipsRootLoop H' height idx ti0 auth node0 ∧
      S (fipsRootLoop H height idx ti0 auth node0) := by
  obtain ⟨e, hs⟩ := foldl_agree (fun s : Bytes × ℕ => S s.1)
    (fun (s : Bytes × ℕ) j =>
      if (idx / 2 ^ j) % 2 = 0 then (H (j + 1) (s.2 / 2) s.1 (auth j), s.2 / 2)
      else (H (j + 1) ((s.2 - 1) / 2) (auth j) s.1, (s.2 - 1) / 2))
    (fun (s : Bytes × ℕ) j =>
      if (idx / 2 ^ j) % 2 = 0 then (H' (j + 1) (s.2 / 2) s.1 (auth j), s.2 / 2)
      else (H' (j + 1) ((s.2 - 1) / 2) (auth j) s.1, (s.2 - 1) / 2))
    (by
      intro s j hs
      split_ifs
      · rw [hH _ _ _ _ hs (hauth j)]
      · rw [hH _ _ _ _ (hauth j) hs])
    (by
      intro s j _
      split_ifs
      · exact hHS _ _ _ _
      · exact hHS _ _ _ _)
    (List.range height) (node0, ti0) hn
  exact ⟨congrArg Prod.fst e, hs⟩

/-! ### XMSS (Algorithms 9–11) -/

theorem xmssNode_eq (h : Agree S len k hs hs') (hp : AgreePRF S hs hs') (adrs : Address) :
    ∀ z i, fipsXmssNode hs len adrs i z = fipsXmssNode hs' len adrs i z ∧
      S (fipsXmssNode hs len adrs i z) := by
  intro z
  induction z with
  | zero =>
    intro i
    simp only [fipsXmssNode]
    exact ⟨wotsPkGen_eq h hp _, by unfold fipsWotsPkGen; exact h.T_S _ _⟩
  | succ z ih =>
    intro i
    simp only [fipsXmssNode, treeH]
    obtain ⟨a1, a2⟩ := ih (2 * i)
    obtain ⟨b1, b2⟩ := ih (2 * i + 1)
    exact ⟨by rw [← a1, ← b1]; exact h.H _ _ _ a2 b2, h.H_S _ _ _⟩

theorem xmssSign_eq (h : Agree S len k hs hs') (hp : AgreePRF S hs hs') (n h' : ℕ) (M : Bytes)
    (idx : ℕ) (adrs : Address) :
    fipsXmssSign hs n len h' M idx adrs = fipsXmssSign hs' n len h' M idx adrs ∧
      (∀ b ∈ (fipsXmssSign hs n len h' M idx adrs).1, S b) ∧
      (∀ b ∈ (fipsXmssSign hs n len h' M idx adrs).2, S b) := by
  unfold fipsXmssSign
  dsimp only
  obtain ⟨w1, w2⟩ := wotsSign_eq h hp n len M (leafAdrs adrs idx)
  refine ⟨?_, w2, ?_⟩
  · rw [w1]
    congr 2
    funext j
    exact (xmssNode_eq h hp adrs _ _).1
  · intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨j, -, rfl⟩ := hb
    exact (xmssNode_eq h hp adrs _ _).2

theorem xmssPkFromSig_eq (h : Agree S len k hs hs') (n h' idx : ℕ) (sig auth : List Bytes)
    (hsig : ∀ b ∈ sig, S b) (hauth : ∀ b ∈ auth, S b) (M : Bytes) (adrs : Address) :
    fipsXmssPkFromSig hs n len h' idx sig auth M adrs =
        fipsXmssPkFromSig hs' n len h' idx sig auth M adrs ∧
      S (fipsXmssPkFromSig hs n len h' idx sig auth M adrs) := by
  unfold fipsXmssPkFromSig
  dsimp only
  obtain ⟨w1, w2⟩ := wotsPkFromSig_eq h n sig hsig M (leafAdrs adrs idx)
  rw [← w1]
  exact rootLoop_eq (fun z i l r hl hr => h.H _ l r hl hr) (fun z i l r => h.H_S _ l r) h' idx idx
    _ (fun j => h.getD hauth j) _ w2

/-! ### Hypertree (Algorithms 12, 13) -/

theorem htSignLoop_eq (h : Agree S len k hs hs') (hp : AgreePRF S hs hs') (n h' d : ℕ) :
    ∀ count j root t, fipsHtSignLoop hs n len h' d j count root t =
      fipsHtSignLoop hs' n len h' d j count root t := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ c ih =>
    intro j root t
    simp only [fipsHtSignLoop]
    obtain ⟨e1, s1, s2⟩ := xmssSign_eq h hp n h' root (t % 2 ^ h') (htAdrs j (t >>> h'))
    have e2 := (xmssPkFromSig_eq h n h' (t % 2 ^ h') _ _ s1 s2 root (htAdrs j (t >>> h'))).1
    rw [e2, e1, ih]

theorem htSign_eq (h : Agree S len k hs hs') (hp : AgreePRF S hs hs') (n h' d : ℕ) (M : Bytes)
    (t l : ℕ) : fipsHtSign hs n len h' d M t l = fipsHtSign hs' n len h' d M t l := by
  unfold fipsHtSign
  dsimp only
  obtain ⟨e1, s1, s2⟩ := xmssSign_eq h hp n h' M l (htAdrs 0 t)
  have e2 := (xmssPkFromSig_eq h n h' l _ _ s1 s2 M (htAdrs 0 t)).1
  rw [e2, e1, htSignLoop_eq h hp]

theorem htVerifyLoop_eq (h : Agree S len k hs hs') (n h' : ℕ) (sigHt : List Bytes)
    (hsig : ∀ b ∈ sigHt, S b) :
    ∀ count j node t, fipsHtVerifyLoop hs n len h' sigHt j count node t =
      fipsHtVerifyLoop hs' n len h' sigHt j count node t := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ c ih =>
    intro j node t
    simp only [fipsHtVerifyLoop]
    have hx : ∀ b ∈ getXMSSSignature len h' sigHt j, S b := fun b hb =>
      hsig b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
    rw [(xmssPkFromSig_eq h n h' _ _ _ (fun b hb => hx b (List.mem_of_mem_take hb))
      (fun b hb => hx b (List.mem_of_mem_drop hb)) node _).1, ih]

theorem htVerifyNode_eq (h : Agree S len k hs hs') (n h' d : ℕ) (M : Bytes) (sigHt : List Bytes)
    (hsig : ∀ b ∈ sigHt, S b) (t l : ℕ) :
    fipsHtVerifyNode hs n len h' d M sigHt t l = fipsHtVerifyNode hs' n len h' d M sigHt t l := by
  unfold fipsHtVerifyNode
  dsimp only
  have hx : ∀ b ∈ getXMSSSignature len h' sigHt 0, S b := fun b hb =>
    hsig b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
  rw [(xmssPkFromSig_eq h n h' _ _ _ (fun b hb => hx b (List.mem_of_mem_take hb))
    (fun b hb => hx b (List.mem_of_mem_drop hb)) M _).1, htVerifyLoop_eq h n h' sigHt hsig]

/-! ### FORS (Algorithms 14–17) -/

theorem forsNode_eq (h : Agree S len k hs hs') (hp : AgreePRF S hs hs') (adrs : Address) :
    ∀ z i, fipsForsNode hs adrs i z = fipsForsNode hs' adrs i z ∧ S (fipsForsNode hs adrs i z) := by
  intro z
  induction z with
  | zero =>
    intro i
    simp only [fipsForsNode, fipsForsSkGen]
    exact ⟨by rw [h.F _ _ (hp.S _), hp.eq], h.F_S _ _⟩
  | succ z ih =>
    intro i
    simp only [fipsForsNode]
    obtain ⟨a1, a2⟩ := ih (2 * i)
    obtain ⟨b1, b2⟩ := ih (2 * i + 1)
    exact ⟨by rw [← a1, ← b1]; exact h.H _ _ _ a2 b2, h.H_S _ _ _⟩

theorem forsSign_eq (h : Agree S len k hs hs') (hp : AgreePRF S hs hs') (k' a : ℕ) (md : Bytes)
    (adrs : Address) :
    fipsForsSign hs k' a md adrs = fipsForsSign hs' k' a md adrs ∧
      ∀ b ∈ fipsForsSign hs k' a md adrs, S b := by
  unfold fipsForsSign
  dsimp only
  refine ⟨?_, ?_⟩
  · congr 1
    funext i
    simp only [fipsForsSkGen, hp.eq, fun j i => (forsNode_eq h hp adrs j i).1]
  · intro b hb
    simp only [List.mem_flatMap, List.mem_cons, List.mem_map] at hb
    obtain ⟨i, -, hb⟩ := hb
    rcases hb with rfl | ⟨j, -, rfl⟩
    · exact hp.S _
    · exact (forsNode_eq h hp adrs _ _).2

theorem forsPkFromSig_eq (h : Agree S len k hs hs') (a : ℕ) (sig : List Bytes)
    (hsig : ∀ b ∈ sig, S b) (md : Bytes) (adrs : Address) :
    fipsForsPkFromSig hs k a sig md adrs = fipsForsPkFromSig hs' k a sig md adrs ∧
      S (fipsForsPkFromSig hs k a sig md adrs) := by
  unfold fipsForsPkFromSig
  dsimp only
  refine ⟨?_, h.T_S _ _⟩
  have root_eq : ∀ i,
      fipsRootLoop (forsH hs adrs) a ((fipsBase2b md a k).getD i 0)
          (i * 2 ^ a + (fipsBase2b md a k).getD i 0) (fun j => sig.getD (i * (a + 1) + 1 + j) [])
          (hs.F ((adrs.setWord2 0).setWord3 (i * 2 ^ a + (fipsBase2b md a k).getD i 0))
            (sig.getD (i * (a + 1)) [])) =
        fipsRootLoop (forsH hs' adrs) a ((fipsBase2b md a k).getD i 0)
          (i * 2 ^ a + (fipsBase2b md a k).getD i 0) (fun j => sig.getD (i * (a + 1) + 1 + j) [])
          (hs'.F ((adrs.setWord2 0).setWord3 (i * 2 ^ a + (fipsBase2b md a k).getD i 0))
            (sig.getD (i * (a + 1)) [])) ∧
      S (fipsRootLoop (forsH hs adrs) a ((fipsBase2b md a k).getD i 0)
          (i * 2 ^ a + (fipsBase2b md a k).getD i 0) (fun j => sig.getD (i * (a + 1) + 1 + j) [])
          (hs.F ((adrs.setWord2 0).setWord3 (i * 2 ^ a + (fipsBase2b md a k).getD i 0))
            (sig.getD (i * (a + 1)) []))) := by
    intro i
    rw [← h.F _ _ (h.getD hsig _)]
    exact rootLoop_eq (fun z i l r hl hr => h.H _ l r hl hr) (fun z i l r => h.H_S _ l r) _ _ _
      _ (fun j => h.getD hsig _) _ (h.F_S _ _)
  have hmap : ((List.range k).map fun i =>
        fipsRootLoop (forsH hs adrs) a ((fipsBase2b md a k).getD i 0)
          (i * 2 ^ a + (fipsBase2b md a k).getD i 0) (fun j => sig.getD (i * (a + 1) + 1 + j) [])
          (hs.F ((adrs.setWord2 0).setWord3 (i * 2 ^ a + (fipsBase2b md a k).getD i 0))
            (sig.getD (i * (a + 1)) []))) =
      ((List.range k).map fun i =>
        fipsRootLoop (forsH hs' adrs) a ((fipsBase2b md a k).getD i 0)
          (i * 2 ^ a + (fipsBase2b md a k).getD i 0) (fun j => sig.getD (i * (a + 1) + 1 + j) [])
          (hs'.F ((adrs.setWord2 0).setWord3 (i * 2 ^ a + (fipsBase2b md a k).getD i 0))
            (sig.getD (i * (a + 1)) []))) := by
    congr 1
    funext i
    exact (root_eq i).1
  rw [← hmap]
  apply h.T
  · right; simp
  · intro m hm
    simp only [List.mem_map] at hm
    obtain ⟨i, -, rfl⟩ := hm
    exact (root_eq i).2

end Congr

/-! ## Algorithms 18–20 for an arbitrary hash family -/

section Generic

variable (P : Params)

/-- FIPS 205 Algorithm 18 (`slh_keygen_internal`), the `PK.root` line:
    `xmss_node(SK.seed, 0, h′, PK.seed, ADRS)` with `ADRS.setLayerAddress(d − 1)`. -/
def keygenRoot (hs : Tweak) : Bytes :=
  fipsXmssNode hs P.len (Address.zero.setLayer (P.d - 1)) 0 P.treeHeight

/-- FIPS 205 Algorithm 19 (`slh_sign_internal(M, SK, addrnd)`), for a
    tweakable hash `hs` (with `PK.seed`, `SK.seed` fixed), `PRF_msg` and
    `H_msg`. -/
def signInternal (hs : Tweak) (prfMsg : Bytes → Bytes → Bytes → Bytes)
    (hMsg : Bytes → Bytes → Bytes → Bytes → Bytes)
    (M skPrf pkSeed pkRoot addrnd : Bytes) : List Bytes :=
  let R := prfMsg skPrf addrnd M
  let digest := hMsg R pkSeed pkRoot M
  let split := fipsSplit P digest
  let adrs := Top.fipsForsAdrs split.2.1 split.2.2
  let sigFors := fipsForsSign hs P.k P.a split.1 adrs
  let pkFors := fipsForsPkFromSig hs P.k P.a sigFors split.1 adrs
  let sigHt := fipsHtSign hs P.n P.len P.treeHeight P.d pkFors split.2.1 split.2.2
  [R] ++ sigFors ++ sigHt

/-- FIPS 205 Algorithm 20 (`slh_verify_internal(M, SIG, PK)`) at block
    level, for a tweakable hash `hs` (with `PK.seed` fixed; `PRF` is not
    used) and `H_msg`. -/
def verifyInternal (hs : Tweak) (hMsg : Bytes → Bytes → Bytes → Bytes → Bytes)
    (M : Bytes) (SIG : List Bytes) (pkSeed pkRoot : Bytes) : Bool :=
  if SIG.length ≠ 1 + P.k * (1 + P.a) + P.h + P.d * P.len then false
  else
    let R := SIG.getD 0 []
    let sigFors := (SIG.drop 1).take (P.k * (1 + P.a))
    let sigHt := SIG.drop (1 + P.k * (1 + P.a))
    let digest := hMsg R pkSeed pkRoot M
    let split := fipsSplit P digest
    let adrs := Top.fipsForsAdrs split.2.1 split.2.2
    let pkFors := fipsForsPkFromSig hs P.k P.a sigFors split.1 adrs
    decide (fipsHtVerifyNode hs P.n P.len P.treeHeight P.d pkFors sigHt split.2.1 split.2.2 = pkRoot)

theorem fipsKeygenRoot_eq (hf : Top.HashFam) (skSeed pkSeed : Bytes) :
    Top.fipsKeygenRoot hf P skSeed pkSeed =
      keygenRoot P (Tweak.ofCode (hf.thash pkSeed) (hf.prf pkSeed skSeed)) := rfl

theorem fipsSlhSignInternal_eq (hf : Top.HashFam) (M skSeed skPrf pkSeed pkRoot addrnd : Bytes) :
    Top.fipsSlhSignInternal hf P M skSeed skPrf pkSeed pkRoot addrnd =
      signInternal P (Tweak.ofCode (hf.thash pkSeed) (hf.prf pkSeed skSeed)) hf.prfMsg hf.hMsg
        M skPrf pkSeed pkRoot addrnd := rfl

theorem fipsSlhVerifyInternal_eq (hf : Top.HashFam) (M : Bytes) (SIG : List Bytes)
    (pkSeed pkRoot : Bytes) :
    Top.fipsSlhVerifyInternal hf P M SIG pkSeed pkRoot =
      verifyInternal P (Tweak.ofCode (hf.thash pkSeed) (fun _ => [])) hf.hMsg M SIG pkSeed pkRoot :=
  rfl

variable {S : Bytes → Prop} {hs hs' : Tweak}

theorem keygenRoot_congr (h : Agree S P.len P.k hs hs') (hp : AgreePRF S hs hs') :
    keygenRoot P hs = keygenRoot P hs' :=
  (xmssNode_eq h hp _ _ _).1

theorem signInternal_congr (h : Agree S P.len P.k hs hs') (hp : AgreePRF S hs hs')
    (prfMsg prfMsg' : Bytes → Bytes → Bytes → Bytes)
    (hMsg hMsg' : Bytes → Bytes → Bytes → Bytes → Bytes) (M skPrf pkSeed pkRoot addrnd : Bytes)
    (hR : prfMsg skPrf addrnd M = prfMsg' skPrf addrnd M)
    (hD : hMsg (prfMsg skPrf addrnd M) pkSeed pkRoot M =
      hMsg' (prfMsg skPrf addrnd M) pkSeed pkRoot M) :
    signInternal P hs prfMsg hMsg M skPrf pkSeed pkRoot addrnd =
      signInternal P hs' prfMsg' hMsg' M skPrf pkSeed pkRoot addrnd := by
  unfold signInternal
  dsimp only
  rw [hD, hR]
  generalize fipsSplit P (hMsg' (prfMsg' skPrf addrnd M) pkSeed pkRoot M) = sp
  obtain ⟨e1, s1⟩ := forsSign_eq h hp P.k P.a sp.1 (Top.fipsForsAdrs sp.2.1 sp.2.2)
  rw [htSign_eq h hp, (forsPkFromSig_eq h P.a _ s1 _ _).1, e1]

theorem verifyInternal_congr (h : Agree S P.len P.k hs hs')
    (hMsg hMsg' : Bytes → Bytes → Bytes → Bytes → Bytes) (M : Bytes) (SIG : List Bytes)
    (pkSeed pkRoot : Bytes) (hsig : ∀ b ∈ SIG, S b)
    (hD : hMsg (SIG.getD 0 []) pkSeed pkRoot M = hMsg' (SIG.getD 0 []) pkSeed pkRoot M) :
    verifyInternal P hs hMsg M SIG pkSeed pkRoot = verifyInternal P hs' hMsg' M SIG pkSeed pkRoot := by
  unfold verifyInternal
  split_ifs
  · rfl
  · dsimp only
    rw [hD]
    generalize fipsSplit P (hMsg' (SIG.getD 0 []) pkSeed pkRoot M) = sp
    rw [(forsPkFromSig_eq h P.a _
        (fun b hb => hsig b (List.mem_of_mem_drop (List.mem_of_mem_take hb))) _ _).1,
      htVerifyNode_eq h _ _ _ _ _ (fun b hb => hsig b (List.mem_of_mem_drop hb))]

end Generic

end OcamlPq.EndToEnd.SLHDSA
