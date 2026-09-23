import OcamlPq.SLHDSA.Hypertree
import OcamlPq.SLHDSA.Hash

/-!
# SLH-DSA: key generation, signing and verification

* `keypair_from_seed` (slhdsa_engine.ml 541–548) = `slh_keygen_internal`
  (FIPS 205 Algorithm 18); `signing_key_of_octets` (555–574) accepts
  exactly the keys whose `PK.root` is the Algorithm 18 root.
* `sign_formatted_with_randomness` (589–637) = `slh_sign_internal`
  (Algorithm 19), with `formatted_prefix` (639–642) = the `M′` of
  Algorithm 22 and `sign_deterministic` using `opt_rand = PK.seed`.
* `verify_formatted` (662–722) = `slh_verify_internal` (Algorithm 20),
  including the signature-length check.
* End-to-end correctness: verification accepts every signature produced
  with the matching key, for every message and randomness.
* Signature layout: the byte offsets of every `take`/`sub` in the verifier
  stay inside a signature of length `signature_size`.

The hash functions are abstract (a `HashFam`); `Hash.lean` shows that the
code's concrete functions are FIPS 205 §11's. Signatures are modelled as
lists of `n`-byte blocks (`R`, then `k(1 + a)` FORS blocks, then `d` XMSS
signatures of `len + h′` blocks); the `Layout` section relates block
positions to the code's byte positions.
-/

namespace OcamlPq.SLHDSA.Top

open Address WOTS XMSS FORS Treehash Base2b Hypertree

/-- The hash functions as the code uses them: `thash`/`prf` depend on the
    `hash_context = {sk_seed; pk_seed}`. -/
structure HashFam where
  /-- `thash {pk_seed; _}`. -/
  thash : Bytes → Address → List Bytes → Bytes
  /-- `prf {sk_seed; pk_seed}` (`pk_seed` first). -/
  prf : Bytes → Bytes → Address → Bytes
  /-- `prf_message sk_prf randomness message`. -/
  prfMsg : Bytes → Bytes → Bytes → Bytes
  /-- `hash_message randomizer {pk_seed; pk_root} message`. -/
  hMsg : Bytes → Bytes → Bytes → Bytes → Bytes

/-- The code's concrete family for a parameter set over primitives `pr`. -/
def HashFam.ofPrims (pr : Hash.Prims) (P : Params) : HashFam :=
  ⟨Hash.thash pr P, Hash.prf pr P, Hash.prfMessage pr P, Hash.hashMessage pr P⟩

variable (hf : HashFam) (P : Params) (w : ℕ)

/-! ## Code models -/

section Code

/-- `constant_time_equal left right` (lines 270–280). -/
def constantTimeEqual (l r : Bytes) : Bool :=
  if l.length ≠ r.length then false
  else (List.range l.length).foldl (fun diff i => diff ||| (l.getD i 0 ^^^ r.getD i 0)) 0 = 0

/-- `keypair_from_seed seed` (lines 541–548): `(sk_seed, sk_prf, pk_seed,
    pk_root)`. -/
def keypairFromSeed (seed : Bytes) : Option (Bytes × Bytes × Bytes × Bytes) :=
  let skSeed := (seed.drop 0).take P.n
  let skPrf := (seed.drop P.n).take P.n
  let pkSeed := (seed.drop (2 * P.n)).take P.n
  (merkleRoot (hf.thash pkSeed) (hf.prf pkSeed skSeed) P.n P.len P.treeHeight P.d).map
    fun pkRoot => (skSeed, skPrf, pkSeed, pkRoot)

/-- The root check of `signing_key_of_octets` (lines 559–566) on a
    length-checked `4n`-byte key. -/
def signingKeyRootOk (value : Bytes) : Bool :=
  let skSeed := (value.drop 0).take P.n
  let pkSeed := (value.drop (2 * P.n)).take P.n
  let pkRoot := (value.drop (3 * P.n)).take P.n
  match merkleRoot (hf.thash pkSeed) (hf.prf pkSeed skSeed) P.n P.len P.treeHeight P.d with
  | none => false
  | some expectedRoot => constantTimeEqual pkRoot expectedRoot

/-- `sign_formatted_with_randomness key ~formatted_message randomness`
    (lines 589–637), with the key as `(sk_seed, sk_prf, pk_seed, pk_root)`
    and FORS indices computed with `int`s of width `w`. `none` is the
    `Invalid_length` error or an exception. -/
def signFormatted (skSeed skPrf pkSeed pkRoot : Bytes) (M randomness : Bytes) :
    Option (List Bytes) :=
  if randomness.length ≠ P.n then none
  else
    let thash := hf.thash pkSeed
    let prf := hf.prf pkSeed skSeed
    let randomizer := hf.prfMsg skPrf randomness M
    let digest := hf.hMsg randomizer pkSeed pkRoot M
    let split := splitMessageDigest P digest
    let forsAddress : Address := { Address.zero with tree := split.2.1, typ := 0, keypair := split.2.2 }
    match forsSign thash prf w P.n P.k P.a forsAddress split.1 with
    | none => none
    | some (forsSignature, initialRoot) =>
      (signLayers thash prf P.n P.len P.treeHeight P.d 0 initialRoot split.2.1 split.2.2).map
        fun ht => [randomizer] ++ forsSignature ++ ht

/-- `verify_formatted verification_key ~formatted_message signature`
    (lines 662–722) on a signature split into `n`-byte blocks. -/
def verifyFormatted (pkSeed pkRoot : Bytes) (M : Bytes) (signature : List Bytes) : Bool :=
  if signature.length ≠ 1 + P.k * (P.a + 1) + P.d * (P.len + P.treeHeight) then false
  else
    let thash := hf.thash pkSeed
    let randomizer := signature.getD 0 []
    let digest := hf.hMsg randomizer pkSeed pkRoot M
    let split := splitMessageDigest P digest
    let forsAddress : Address := { Address.zero with tree := split.2.1, typ := 0, keypair := split.2.2 }
    let forsSignature := (signature.drop 1).take (P.k * (P.a + 1))
    let root := forsPublicKeyFromSignature thash w P.k P.a forsAddress split.1 forsSignature
    let root := verifyLayers thash P.n P.len P.treeHeight P.d 0 root split.2.1 split.2.2
      (signature.drop (1 + P.k * (P.a + 1)))
    constantTimeEqual root pkRoot

/-- `formatted_prefix context` (lines 639–642); `Char.unsafe_chr` of the
    length keeps its low byte. -/
def formattedPrefix (ctx : Bytes) : Bytes := [0] ++ [ctx.length % 256] ++ ctx

end Code

/-! ## FIPS 205 Algorithms 18–20, 22 -/

section Spec

/-- FIPS 205 Algorithm 18 `slh_keygen_internal(SK.seed, SK.prf, PK.seed)`:
    `ADRS ← toByte(0, 32); ADRS.setLayerAddress(d − 1);
    PK.root ← xmss_node(SK.seed, 0, h′, PK.seed, ADRS)`. -/
def fipsKeygenRoot (skSeed pkSeed : Bytes) : Bytes :=
  fipsXmssNode (Tweak.ofCode (hf.thash pkSeed) (hf.prf pkSeed skSeed)) P.len
    (Address.zero.setLayer (P.d - 1)) 0 P.treeHeight

/-- The FORS address of Algorithm 19 lines 11–13 / Algorithm 20 lines
    13–15. -/
def fipsForsAdrs (idxTree idxLeaf : ℕ) : Address :=
  ((Address.zero.setTree (BitVec.ofNat 64 idxTree)).setTypeAndClear FORS_TREE).setKeyPair idxLeaf

/-- FIPS 205 Algorithm 19 `slh_sign_internal(M, SK, addrnd)` with
    `opt_rand = addrnd`. -/
def fipsSlhSignInternal (M : Bytes) (skSeed skPrf pkSeed pkRoot addrnd : Bytes) : List Bytes :=
  let hs := Tweak.ofCode (hf.thash pkSeed) (hf.prf pkSeed skSeed)
  let optRand := addrnd
  let R := hf.prfMsg skPrf optRand M
  let digest := hf.hMsg R pkSeed pkRoot M
  let split := fipsSplit P digest
  let adrs := fipsForsAdrs split.2.1 split.2.2
  let sigFors := fipsForsSign hs P.k P.a split.1 adrs
  let pkFors := fipsForsPkFromSig hs P.k P.a sigFors split.1 adrs
  let sigHt := fipsHtSign hs P.n P.len P.treeHeight P.d pkFors split.2.1 split.2.2
  [R] ++ sigFors ++ sigHt

/-- FIPS 205 Algorithm 20 `slh_verify_internal(M, SIG, PK)` (block level:
    `|SIG| = 1 + k(1 + a) + h + d·len` blocks of `n` bytes). `PRF` is never
    used by verification. -/
def fipsSlhVerifyInternal (M : Bytes) (SIG : List Bytes) (pkSeed pkRoot : Bytes) : Bool :=
  if SIG.length ≠ 1 + P.k * (1 + P.a) + P.h + P.d * P.len then false
  else
    let hs := Tweak.ofCode (hf.thash pkSeed) (fun _ => [])
    let R := SIG.getD 0 []
    let sigFors := (SIG.drop 1).take (P.k * (1 + P.a))
    let sigHt := SIG.drop (1 + P.k * (1 + P.a))
    let digest := hf.hMsg R pkSeed pkRoot M
    let split := fipsSplit P digest
    let adrs := fipsForsAdrs split.2.1 split.2.2
    let pkFors := fipsForsPkFromSig hs P.k P.a sigFors split.1 adrs
    decide (fipsHtVerifyNode hs P.n P.len P.treeHeight P.d pkFors sigHt split.2.1 split.2.2 = pkRoot)

/-- FIPS 205 Algorithm 22 line 7 / Algorithm 24 line 5:
    `M′ ← toByte(0, 1) ‖ toByte(|ctx|, 1) ‖ ctx ‖ M`. -/
def fipsFormat (ctx M : Bytes) : Bytes := fipsToByte 0 1 ++ fipsToByte ctx.length 1 ++ ctx ++ M

end Spec

/-! ## Helper facts -/

theorem constantTimeEqual_eq (l r : Bytes) : constantTimeEqual l r = decide (l = r) := by
  unfold constantTimeEqual
  by_cases hlen : l.length = r.length
  · simp only [ne_eq, hlen, not_true_eq_false, ↓reduceIte]
    have key : ∀ (m acc : ℕ), m ≤ l.length →
        ((List.range m).foldl (fun diff i => diff ||| (l.getD i 0 ^^^ r.getD i 0)) acc = 0 ↔
          acc = 0 ∧ ∀ i < m, l.getD i 0 = r.getD i 0) := by
      intro m
      induction m with
      | zero => intro acc _; simp
      | succ m ih =>
        intro acc hm
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          Nat.or_eq_zero_iff, ih acc (by omega)]
        have hx : l.getD m 0 ^^^ r.getD m 0 = 0 ↔ l.getD m 0 = r.getD m 0 := by
          constructor
          · intro h
            have := Nat.xor_xor_cancel_left (l.getD m 0) (r.getD m 0)
            rw [h, Nat.xor_zero] at this
            exact this
          · intro h; rw [h, Nat.xor_self]
        rw [hx]
        constructor
        · rintro ⟨⟨h0, hall⟩, hlast⟩
          exact ⟨h0, fun i hi => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
            · exact hall i hi
            · exact hlast⟩
        · rintro ⟨h0, hall⟩
          exact ⟨⟨h0, fun i hi => hall i (by omega)⟩, hall m (by omega)⟩
    rw [hlen] at key
    apply decide_eq_decide.mpr
    rw [key r.length 0 le_rfl]
    constructor
    · rintro ⟨_, hall⟩
      apply List.ext_getElem hlen
      intro i h1 h2
      have := hall i (by omega)
      rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
    · rintro rfl
      exact ⟨rfl, fun i _ => rfl⟩
  · simp only [ne_eq, hlen, not_false_eq_true, ↓reduceIte]
    symm
    simp only [decide_eq_false_iff_not]
    intro h; exact hlen (by rw [h])

theorem fipsSplit_bounds (hP : P ∈ allParams) (digest : Bytes) :
    (fipsSplit P digest).2.1 < 2 ^ ((P.d - 1) * P.treeHeight) ∧
      (fipsSplit P digest).2.1 < 2 ^ 64 ∧ (fipsSplit P digest).2.2 < 2 ^ P.treeHeight := by
  have hsplit := digest_split_fips P hP
  have hbits : P.treeBits ≤ 64 := (initChecks_all P hP).2.2
  have htb : P.h - P.h / P.d = (P.d - 1) * P.treeHeight := by
    rw [← hsplit.1]; unfold Params.treeBits; ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [fipsSplit]; rw [← htb]; exact Nat.mod_lt _ (by positivity)
  · simp only [fipsSplit]
    exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right (by norm_num) (by rw [← hsplit.1]; exact hbits))
  · simp only [fipsSplit]; exact Nat.mod_lt _ (by positivity)

theorem length_flatMap_range {β : Type} (f : ℕ → List β) (m : ℕ) (hf : ∀ i, (f i).length = m) :
    ∀ k, ((List.range k).flatMap f).length = k * m := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => simp [List.range_succ, List.flatMap_append, ih, hf]; ring

theorem fipsForsSign_length (hs : Tweak) (k a : ℕ) (md : Bytes) (adrs : Address) :
    (fipsForsSign hs k a md adrs).length = k * (1 + a) := by
  unfold fipsForsSign
  rw [length_flatMap_range _ (1 + a) (fun i => by simp; ring)]

theorem fipsHtSign_length (hs : Tweak) (n len h' d : ℕ) (hd : 1 ≤ d) (M : Bytes) (t l : ℕ) :
    (fipsHtSign hs n len h' d M t l).length = d * (len + h') := by
  unfold fipsHtSign
  simp only [List.length_append, fipsXmssSign_length, fipsHtSignLoop_length]
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; ring

theorem fipsForsPkFromSig_prf (thash : Address → List Bytes → Bytes) (p q : Address → Bytes)
    (k a : ℕ) (sig : List Bytes) (md : Bytes) (adrs : Address) :
    fipsForsPkFromSig (Tweak.ofCode thash p) k a sig md adrs =
      fipsForsPkFromSig (Tweak.ofCode thash q) k a sig md adrs := rfl

theorem fipsXmssPkFromSig_prf (thash : Address → List Bytes → Bytes) (p q : Address → Bytes)
    (n len h' idx : ℕ) (sig auth : List Bytes) (M : Bytes) (adrs : Address) :
    fipsXmssPkFromSig (Tweak.ofCode thash p) n len h' idx sig auth M adrs =
      fipsXmssPkFromSig (Tweak.ofCode thash q) n len h' idx sig auth M adrs := rfl

theorem fipsHtVerifyLoop_prf (thash : Address → List Bytes → Bytes) (p q : Address → Bytes)
    (n len h' : ℕ) (sig : List Bytes) :
    ∀ count j node t, fipsHtVerifyLoop (Tweak.ofCode thash p) n len h' sig j count node t =
      fipsHtVerifyLoop (Tweak.ofCode thash q) n len h' sig j count node t := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ c ih =>
    intro j node t
    rw [fipsHtVerifyLoop, fipsHtVerifyLoop, ih, fipsXmssPkFromSig_prf thash p q]

theorem fipsHtVerifyNode_prf (thash : Address → List Bytes → Bytes) (p q : Address → Bytes)
    (n len h' d : ℕ) (M : Bytes) (sig : List Bytes) (t l : ℕ) :
    fipsHtVerifyNode (Tweak.ofCode thash p) n len h' d M sig t l =
      fipsHtVerifyNode (Tweak.ofCode thash q) n len h' d M sig t l := by
  unfold fipsHtVerifyNode
  rw [fipsHtVerifyLoop_prf thash p q, fipsXmssPkFromSig_prf thash p q]

theorem fipsForsPkFromSig_nbytes (thash : Address → List Bytes → Bytes) (p : Address → Bytes)
    (n : ℕ) (hth : ∀ a bs, NBytes n (thash a bs)) (k a : ℕ) (sig : List Bytes) (md : Bytes)
    (adrs : Address) : NBytes n (fipsForsPkFromSig (Tweak.ofCode thash p) k a sig md adrs) :=
  hth _ _

/-! ## Key generation -/

/-- **Key generation = Algorithm 18.** For a `3n`-byte seed
    `SK.seed ‖ SK.prf ‖ PK.seed`, `keypair_from_seed` returns
    `(SK.seed, SK.prf, PK.seed, PK.root)` with FIPS 205's `PK.root`. -/
theorem keypairFromSeed_eq (seed : Bytes) :
    keypairFromSeed hf P seed =
      some ((seed.drop 0).take P.n, (seed.drop P.n).take P.n, (seed.drop (2 * P.n)).take P.n,
        fipsKeygenRoot hf P ((seed.drop 0).take P.n) ((seed.drop (2 * P.n)).take P.n)) := by
  unfold keypairFromSeed
  dsimp only
  rw [merkleRoot_eq]
  rfl

/-- **`signing_key_of_octets` root check.** A `4n`-byte signing key
    `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root` is accepted iff `PK.root` is the
    Algorithm 18 root of `SK.seed`, `PK.seed`. -/
theorem signingKeyRootOk_iff (value : Bytes) :
    signingKeyRootOk hf P value = true ↔
      (value.drop (3 * P.n)).take P.n =
        fipsKeygenRoot hf P ((value.drop 0).take P.n) ((value.drop (2 * P.n)).take P.n) := by
  unfold signingKeyRootOk
  dsimp only
  rw [merkleRoot_eq]
  simp only [constantTimeEqual_eq, decide_eq_true_eq]
  rfl

/-! ## Message formatting -/

/-- **`formatted_prefix ctx ^ M` = `M′`** of Algorithms 22/24 for every
    context of at most 255 bytes (longer contexts are rejected by `sign`,
    `sign_deterministic` and `verify` before formatting). -/
theorem formattedPrefix_eq (ctx M : Bytes) (h : ctx.length ≤ 255) :
    formattedPrefix ctx ++ M = fipsFormat ctx M := by
  simp [formattedPrefix, fipsFormat, fipsToByte, toByteRev,
    Nat.mod_eq_of_lt (by omega : ctx.length < 256)]

/-! ## Signing and verification -/

/-- Hypotheses on the abstract hash functions: `thash` returns `n`-byte
    strings, `hash_message` returns `m`-byte strings. -/
structure HashOk (hf : HashFam) (P : Params) : Prop where
  thash : ∀ pk a bs, NBytes P.n (hf.thash pk a bs)
  hMsg : ∀ R pk root M, (hf.hMsg R pk root M).length = P.m ∧ ∀ x ∈ hf.hMsg R pk root M, x < 256

theorem md_length (hP : P ∈ allParams) (digest : Bytes) (hd : digest.length = P.m) :
    P.k * P.a ≤ 8 * ((fipsSplit P digest).1).length := by
  have hm := (initChecks_all P hP).2.1
  simp only [fipsSplit, List.length_take, hd]
  have := (forsMessageBytes_spec P).1
  unfold Params.forsMessageBytes at this hm
  rw [Nat.min_eq_left (by omega)]
  exact this

/-- **Signing = FIPS 205 Algorithm 19.** For every parameter set, every
    `int` width `w ≥ a + 7` (every OCaml platform), every key, message and
    `n`-byte randomness, `sign_formatted_with_randomness` does not raise and
    returns exactly `slh_sign_internal(M, SK, addrnd = randomness)`. -/
theorem signFormatted_eq (hP : P ∈ allParams) (hw : P.a + 7 ≤ w) (hok : HashOk hf P)
    (skSeed skPrf pkSeed pkRoot M randomness : Bytes) (hr : randomness.length = P.n) :
    signFormatted hf P w skSeed skPrf pkSeed pkRoot M randomness =
      some (fipsSlhSignInternal hf P M skSeed skPrf pkSeed pkRoot randomness) := by
  have hsz := sizes_portable P hP
  have hn : P.n ≤ 136 := by rcases n_cases P hP with h | h | h <;> omega
  unfold signFormatted fipsSlhSignInternal
  rw [ite_eq_right (by simp [hr])]
  dsimp only
  set digest := hf.hMsg (hf.prfMsg skPrf randomness M) pkSeed pkRoot M with hdig
  obtain ⟨hdl, hdb⟩ := hok.hMsg (hf.prfMsg skPrf randomness M) pkSeed pkRoot M
  obtain ⟨hb1, hb2, hb3⟩ := fipsSplit_bounds P hP digest
  rw [splitMessageDigest_eq P hP digest hdb]
  dsimp only
  rw [forsSign_eq (hf.thash pkSeed) (hf.prf pkSeed skSeed) w P.n P.k P.a hw _ _
    (md_length P hP digest hdl)]
  dsimp only
  rw [signLayers_htSign (hf.thash pkSeed) (hf.prf pkSeed skSeed) P.n P.len P.treeHeight P.d
    (by omega) (by omega) hn (hok.thash pkSeed) _
    (fipsForsPkFromSig_nbytes _ _ P.n (hok.thash pkSeed) _ _ _ _ _) _ _ hb2 hb3]
  rfl

/-- `sign_deterministic` uses `opt_rand = PK.seed` (Algorithm 19 line 2 with
    the deterministic variant of Algorithm 22). -/
theorem signDeterministic_eq (hP : P ∈ allParams) (hw : P.a + 7 ≤ w) (hok : HashOk hf P)
    (skSeed skPrf pkSeed pkRoot M : Bytes) (hpk : pkSeed.length = P.n) :
    signFormatted hf P w skSeed skPrf pkSeed pkRoot M pkSeed =
      some (fipsSlhSignInternal hf P M skSeed skPrf pkSeed pkRoot pkSeed) :=
  signFormatted_eq hf P w hP hw hok skSeed skPrf pkSeed pkRoot M pkSeed hpk

/-- **Verification = FIPS 205 Algorithm 20**, for every block-structured
    signature (adversarial ones included), including the length check. -/
theorem verifyFormatted_eq (hP : P ∈ allParams) (hw : P.a + 7 ≤ w) (hok : HashOk hf P)
    (pkSeed pkRoot M : Bytes) (sig : List Bytes) :
    verifyFormatted hf P w pkSeed pkRoot M sig = fipsSlhVerifyInternal hf P M sig pkSeed pkRoot := by
  have hsz := sizes_portable P hP
  have hn : P.n ≤ 136 := by rcases n_cases P hP with h | h | h <;> omega
  have hh : P.h = P.d * P.treeHeight := by
    have := (initChecks_all P hP).1
    unfold Params.treeHeight; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero this)).symm
  have hlen : 1 + P.k * (P.a + 1) + P.d * (P.len + P.treeHeight) =
      1 + P.k * (1 + P.a) + P.h + P.d * P.len := by rw [hh]; ring
  unfold verifyFormatted fipsSlhVerifyInternal
  rw [hlen]
  split_ifs with hl
  · rfl
  · dsimp only
    set digest := hf.hMsg (sig.getD 0 []) pkSeed pkRoot M with hdig
    obtain ⟨hdl, hdb⟩ := hok.hMsg (sig.getD 0 []) pkSeed pkRoot M
    obtain ⟨hb1, hb2, hb3⟩ := fipsSplit_bounds P hP digest
    rw [splitMessageDigest_eq P hP digest hdb]
    dsimp only
    rw [forsPublicKeyFromSignature_eq (hf.thash pkSeed) (fun _ => []) w P.k P.a hw _ _
      (md_length P hP digest hdl), verifyLayers_htVerify (hf.thash pkSeed) (fun _ => []) P.n P.len
      P.treeHeight P.d (by omega) (by omega) hn (hok.thash pkSeed) _
      (fipsForsPkFromSig_nbytes _ _ P.n (hok.thash pkSeed) _ _ _ _ _) _ _ _ hb2,
      constantTimeEqual_eq, Nat.mul_comm P.k (P.a + 1), Nat.add_comm P.a 1, Nat.mul_comm (1 + P.a)]
    rfl

/-- `slh_verify_internal` on a signature of the right shape
    `[R] ++ SIG_FORS ++ SIG_HT`. -/
theorem fipsSlhVerifyInternal_concat (hh : P.h = P.d * P.treeHeight) (M pkSeed pkRoot R : Bytes)
    (sigFors sigHt : List Bytes) (hfl : sigFors.length = P.k * (1 + P.a))
    (hhl : sigHt.length = P.d * (P.len + P.treeHeight)) :
    fipsSlhVerifyInternal hf P M ([R] ++ sigFors ++ sigHt) pkSeed pkRoot =
      decide (fipsHtVerifyNode (Tweak.ofCode (hf.thash pkSeed) (fun _ => [])) P.n P.len
        P.treeHeight P.d
        (fipsForsPkFromSig (Tweak.ofCode (hf.thash pkSeed) (fun _ => [])) P.k P.a sigFors
          (fipsSplit P (hf.hMsg R pkSeed pkRoot M)).1
          (fipsForsAdrs (fipsSplit P (hf.hMsg R pkSeed pkRoot M)).2.1
            (fipsSplit P (hf.hMsg R pkSeed pkRoot M)).2.2))
        sigHt (fipsSplit P (hf.hMsg R pkSeed pkRoot M)).2.1
        (fipsSplit P (hf.hMsg R pkSeed pkRoot M)).2.2 = pkRoot) := by
  have hlen : ([R] ++ sigFors ++ sigHt).length = 1 + P.k * (1 + P.a) + P.h + P.d * P.len := by
    simp only [List.length_append, List.length_singleton, hfl, hhl, hh]; ring
  have e0 : ([R] ++ sigFors ++ sigHt).getD 0 [] = R := rfl
  have e1 : (([R] ++ sigFors ++ sigHt).drop 1).take (P.k * (1 + P.a)) = sigFors := by
    simp [hfl]
  have e2 : ([R] ++ sigFors ++ sigHt).drop (1 + P.k * (1 + P.a)) = sigHt := by
    rw [← hfl, Nat.add_comm]
    simp only [List.cons_append, List.drop_succ_cons, List.nil_append, List.drop_left]
  unfold fipsSlhVerifyInternal
  rw [ite_eq_right (by rw [hlen]; simp)]
  simp only [e0, e1, e2]

/-- **FIPS-level correctness**: `slh_verify_internal` accepts every output
    of `slh_sign_internal` under the key pair of Algorithm 18. -/
theorem fips_correct (hP : P ∈ allParams) (skSeed skPrf pkSeed M addrnd : Bytes) :
    fipsSlhVerifyInternal hf P M
        (fipsSlhSignInternal hf P M skSeed skPrf pkSeed (fipsKeygenRoot hf P skSeed pkSeed) addrnd)
        pkSeed (fipsKeygenRoot hf P skSeed pkSeed) = true := by
  have hsz := sizes_portable P hP
  have hh : P.h = P.d * P.treeHeight := by
    have := (initChecks_all P hP).1
    unfold Params.treeHeight; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero this)).symm
  generalize hpk : fipsKeygenRoot hf P skSeed pkSeed = pkRoot
  unfold fipsSlhSignInternal
  dsimp only
  generalize hR : hf.prfMsg skPrf addrnd M = R
  generalize hdig : hf.hMsg R pkSeed pkRoot M = digest
  obtain ⟨hb1, hb2, hb3⟩ := fipsSplit_bounds P hP digest
  generalize hs_def : Tweak.ofCode (hf.thash pkSeed) (hf.prf pkSeed skSeed) = hs
  rw [fipsSlhVerifyInternal_concat hf P hh M pkSeed pkRoot R _ _ (fipsForsSign_length _ _ _ _ _)
    (fipsHtSign_length _ _ _ _ _ (by omega) _ _ _), hdig]
  subst hs_def
  rw [fipsForsPkFromSig_prf _ _ (hf.prf pkSeed skSeed),
    fipsHtVerifyNode_prf _ _ (hf.prf pkSeed skSeed), decide_eq_true_eq,
    fips_ht_correct (hf.thash pkSeed) (hf.prf pkSeed skSeed) P.n P.len P.treeHeight P.d (by omega)
      _ _ _ hb3 hb1, ← hpk]
  exact fipsXmssNode_congr _ _ rfl rfl _ _

/-- **End-to-end correctness of the code.** For every parameter set, every
    OCaml platform (`int` width `w ≥ a + 7`), every seed-derived key pair,
    every message and every `n`-byte randomness (hence also
    `sign_deterministic`), `verify_formatted` accepts the signature
    produced by `sign_formatted_with_randomness`. -/
theorem verify_sign (hP : P ∈ allParams) (hw : P.a + 7 ≤ w) (hok : HashOk hf P)
    (skSeed skPrf pkSeed M randomness : Bytes) (hr : randomness.length = P.n) (sig : List Bytes)
    (hsig : signFormatted hf P w skSeed skPrf pkSeed (fipsKeygenRoot hf P skSeed pkSeed) M
      randomness = some sig) :
    verifyFormatted hf P w pkSeed (fipsKeygenRoot hf P skSeed pkSeed) M sig = true := by
  rw [signFormatted_eq hf P w hP hw hok _ _ _ _ _ _ hr, Option.some.injEq] at hsig
  subst hsig
  rw [verifyFormatted_eq hf P w hP hw hok]
  exact fips_correct hf P hP _ _ _ _ _

/-! ## Byte layout of the signature -/

/-- **Offsets of `verify_formatted`.** The lengths taken by the verifier —
    `n` (R), `fors_signature_size`, then per layer `wots_signature_size` and
    `tree_height·n` — add up exactly to `signature_size`, which is `n` times
    the number of blocks `1 + k(a+1) + d(len + h′)`; so every `take` on a
    signature that passed the length check is in bounds. Inside the FORS
    part, tree `t < k` reads `[t(n + a·n), (t+1)(n + a·n)) ⊆
    [0, fors_signature_size)`; inside a WOTS+ signature, chain `i < len`
    reads `[i·n, i·n + n) ⊆ [0, wots_signature_size)`; inside an
    authentication path, level `ℓ < h′` reads `[ℓ·n, ℓ·n + n) ⊆
    [0, h′·n)`. -/
theorem verify_offsets (P : Params) :
    P.n + P.forsSignatureSize + P.d * (P.wotsSignatureSize + P.treeHeight * P.n) =
        P.signatureSize ∧
      P.signatureSize = P.n * (1 + P.k * (P.a + 1) + P.d * (P.len + P.treeHeight)) ∧
      (∀ t < P.k, (t + 1) * (P.n + P.a * P.n) ≤ P.forsSignatureSize) ∧
      (∀ i < P.len, i * P.n + P.n ≤ P.wotsSignatureSize) ∧
      (∀ l < P.treeHeight, l * P.n + P.n ≤ P.treeHeight * P.n) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · unfold Params.signatureSize Params.forsSignatureSize Params.wotsSignatureSize; ring
  · intro t ht
    unfold Params.forsSignatureSize
    have : (t + 1) * (P.n + P.a * P.n) ≤ P.k * (P.n + P.a * P.n) := Nat.mul_le_mul_right _ ht
    nlinarith
  · intro i hi
    unfold Params.wotsSignatureSize
    have := Nat.mul_le_mul_right P.n (Nat.succ_le_of_lt hi)
    nlinarith
  · intro l hl
    have := Nat.mul_le_mul_right P.n (Nat.succ_le_of_lt hl)
    nlinarith

end OcamlPq.SLHDSA.Top
