import OcamlPq.SLHDSA.Address

/-!
# SLH-DSA: WOTS+

Models of `chain` (slhdsa_engine.ml 301–306), `wots_leaf` (308–323,
including the signature captured by `merkle_sign`) and
`wots_public_key_from_signature` (325–335), proved equal to FIPS 205
Algorithm 5 (`chain`), 6 (`wots_pkGen`), 7 (`wots_sign`) and 8
(`wots_pkFromSig`), and the WOTS+ correctness property
`wots_pkFromSig(wots_sign(M)) = wots_pkGen` for every message.

The tweakable hash functions are abstract: the code's `thash` and `prf`
(with `PK.seed`/`SK.seed` fixed in `context`) are arbitrary functions of the
address and the input blocks. The FIPS functions are `F(ADRS, M₁) =
thash ADRS [M₁]`, `H(ADRS, M₂) = thash ADRS [l, r]`, `T_ℓ(ADRS, M) =
thash ADRS M`, `PRF(ADRS) = prf ADRS`; `Hash.lean` shows that the code's
`thash`/`prf` compute exactly FIPS 205 §11's F, H, T_ℓ, PRF for each
instantiation.

The FIPS algorithms use the ADRS member functions on the code's address
record (`Address.setTypeAndClear`, `setKeyPair`, `setWord2` =
`setChainAddress`/`setTreeHeight`, `setWord3` =
`setHashAddress`/`setTreeIndex`); `Address.lean` proves that these are the
FIPS byte-level operations under `address_full`. FIPS passes `ADRS` by
reference, but every algorithm here sets each field it later reads, so the
value semantics used below is equivalent.
-/

namespace OcamlPq.SLHDSA

/-- Byte strings. -/
abbrev Bytes := List ℕ

/-- The four tweakable hash functions of FIPS 205 §4.1 with `PK.seed` (and
    `SK.seed` for `PRF`) fixed. -/
structure Tweak where
  F : Address → Bytes → Bytes
  H : Address → Bytes → Bytes → Bytes
  T : Address → List Bytes → Bytes
  PRF : Address → Bytes

/-- The FIPS functions realised by the code's single `thash` and `prf`. -/
def Tweak.ofCode (thash : Address → List Bytes → Bytes) (prf : Address → Bytes) : Tweak :=
  ⟨fun a m => thash a [m], fun a l r => thash a [l, r], thash, prf⟩

namespace WOTS

open Address Base2b

/-! ## Code models -/

section Code

variable (thash : Address → List Bytes → Bytes) (prf : Address → Bytes)

/-- `chain context address value position count` (lines 301–306). The
    guard `count = 0 || position = wots_w` is split into the match on
    `count` and the test `position = 16`. `position` and `count` are
    non-negative `int`s at every call site. -/
def chain : Address → Bytes → ℕ → ℕ → Bytes
  | _, value, _, 0 => value
  | address, value, position, count + 1 =>
    if position = 16 then value
    else
      let address := { address with field2 := position }
      chain address (thash address [value]) (position + 1) count

/-- `wots_leaf ?capture context base_address leaf_index` (lines 308–323).
    Returns the WOTS+ public key and, when `capture = Some (lengths, _)`, the
    `wots_len` strings written into the `signature` array. -/
def wotsLeaf (len : ℕ) (capture : Option (List ℕ)) (base : Address) (leafIndex : ℕ) :
    Bytes × Option (List Bytes) :=
  let wotsAddress := { withType 0 base with keypair := leafIndex }
  let publicElements := (List.range len).map fun index =>
    let address := { wotsAddress with field1 := index, field2 := 0 }
    let secret := prf (withType 5 address)
    chain thash address secret 0 (16 - 1)
  let signature := capture.map fun lengths => (List.range len).map fun index =>
    let address := { wotsAddress with field1 := index, field2 := 0 }
    let secret := prf (withType 5 address)
    chain thash address secret 0 (lengths.getD index 0)
  let publicKeyAddress := keypairAddress 1 wotsAddress
  (thash publicKeyAddress publicElements, signature)

/-- `wots_public_key_from_signature context base_address message signature`
    (lines 325–335): the `wots_len` public elements (the caller hashes them,
    lines 708–711). `signature.(index)` is `signature.getD index []`. -/
def wotsPublicKeyFromSignature (len n : ℕ) (base : Address) (message : Bytes)
    (signature : List Bytes) : List Bytes :=
  let lengths := chainLengths (2 * n) message
  let wotsAddress := withType 0 base
  (List.range len).map fun index =>
    let address := { wotsAddress with field1 := index, field2 := 0 }
    chain thash address (signature.getD index []) (lengths.getD index 0)
      (16 - 1 - lengths.getD index 0)

end Code

/-! ## FIPS 205 Algorithms 5–8 -/

section Spec

variable (hs : Tweak)

/-- FIPS 205 Algorithm 5 `chain(X, i, s, PK.seed, ADRS)`:
    `for j from i to i + s − 1: ADRS.setHashAddress(j); tmp ← F(ADRS, tmp)`. -/
def fipsChain (X : Bytes) (i s : ℕ) (adrs : Address) : Bytes :=
  (List.range' i s).foldl (fun tmp j => hs.F (adrs.setWord3 j) tmp) X

/-- The WOTS_PRF key-generation address of Algorithms 6–7:
    `skADRS ← ADRS; skADRS.setTypeAndClear(WOTS_PRF);
     skADRS.setKeyPairAddress(ADRS.getKeyPairAddress())`. -/
def skAdrs (adrs : Address) : Address := (adrs.setTypeAndClear WOTS_PRF).setKeyPair adrs.keypair

/-- The WOTS_PK address of Algorithms 6 and 8. -/
def pkAdrs (adrs : Address) : Address := (adrs.setTypeAndClear WOTS_PK).setKeyPair adrs.keypair

/-- FIPS 205 Algorithm 6 `wots_pkGen(SK.seed, PK.seed, ADRS)`. -/
def fipsWotsPkGen (len : ℕ) (adrs : Address) : Bytes :=
  let tmp := (List.range len).map fun i =>
    let sk := hs.PRF ((skAdrs adrs).setWord2 i)
    fipsChain hs sk 0 (16 - 1) (adrs.setWord2 i)
  hs.T (pkAdrs adrs) tmp

/-- FIPS 205 Algorithm 7 `wots_sign(M, SK.seed, PK.seed, ADRS)` (lines 8–13;
    lines 1–7 are `fipsWotsDigits`). -/
def fipsWotsSign (n len : ℕ) (M : Bytes) (adrs : Address) : List Bytes :=
  let msg := fipsWotsDigits n M
  (List.range len).map fun i =>
    let sk := hs.PRF ((skAdrs adrs).setWord2 i)
    fipsChain hs sk 0 (msg.getD i 0) (adrs.setWord2 i)

/-- FIPS 205 Algorithm 8 `wots_pkFromSig(sig, M, PK.seed, ADRS)`. -/
def fipsWotsPkFromSig (n len : ℕ) (sig : List Bytes) (M : Bytes) (adrs : Address) : Bytes :=
  let msg := fipsWotsDigits n M
  let tmp := (List.range len).map fun i =>
    fipsChain hs (sig.getD i []) (msg.getD i 0) (16 - 1 - msg.getD i 0) (adrs.setWord2 i)
  hs.T (pkAdrs adrs) tmp

end Spec

/-! ## Chain -/

theorem fipsChain_zero (hs : Tweak) (X : Bytes) (i : ℕ) (a : Address) : fipsChain hs X i 0 a = X := by
  simp [fipsChain]

theorem fipsChain_succ (hs : Tweak) (X : Bytes) (i s : ℕ) (a : Address) :
    fipsChain hs X i (s + 1) a = fipsChain hs (hs.F (a.setWord3 i) X) (i + 1) s a := by
  simp [fipsChain, List.range'_succ]

/-- Chains compose: `chain(chain(X, i, s₁), i + s₁, s₂) = chain(X, i, s₁ + s₂)`. -/
theorem fipsChain_add (hs : Tweak) (X : Bytes) (i s₁ s₂ : ℕ) (a : Address) :
    fipsChain hs (fipsChain hs X i s₁ a) (i + s₁) s₂ a = fipsChain hs X i (s₁ + s₂) a := by
  simp only [fipsChain, ← List.range'_append_1, List.foldl_append]

/-- The chain only reads the layer, tree, type, keypair and chain address of
    `ADRS` (the hash address is overwritten). -/
theorem fipsChain_setWord3 (hs : Tweak) (X : Bytes) (i s p : ℕ) (a : Address) :
    fipsChain hs X i s (a.setWord3 p) = fipsChain hs X i s a := by
  simp [fipsChain, Address.setWord3]

/-- **`chain` = FIPS 205 Algorithm 5** whenever `position + count ≤ 16`,
    i.e. the extra guard `position = wots_w` never fires; every call site
    has `position + count ≤ 15`. -/
theorem chain_eq (thash : Address → List Bytes → Bytes) :
    ∀ count (address : Address) (value : Bytes) (position : ℕ), position + count ≤ 16 →
      chain thash address value position count =
        fipsChain (Tweak.ofCode thash (fun _ => [])) value position count address := by
  intro count
  induction count with
  | zero => intro address value position _; simp [chain, fipsChain]
  | succ count ih =>
    intro address value position h
    rw [chain]
    simp only [show ¬position = 16 by omega, ↓reduceIte]
    rw [ih _ _ _ (by omega), fipsChain_succ]
    change fipsChain _ _ _ _ (address.setWord3 position) = _
    rw [fipsChain_setWord3]
    rfl

/-- `chain` does not depend on the `prf` part of the tweak. -/
theorem fipsChain_ofCode_prf (thash : Address → List Bytes → Bytes) (p q : Address → Bytes)
    (X : Bytes) (i s : ℕ) (a : Address) :
    fipsChain (Tweak.ofCode thash p) X i s a = fipsChain (Tweak.ofCode thash q) X i s a := rfl

/-! ## `wots_leaf` = `wots_pkGen` / `wots_sign` -/

/-- The FIPS address at the `wots_pkGen` call of `xmss_node`
    (Algorithm 9 lines 2–3) and of `xmss_sign` (Algorithm 10 lines 5–6):
    `ADRS.setTypeAndClear(WOTS_HASH); ADRS.setKeyPairAddress(i)`. -/
def leafAdrs (base : Address) (i : ℕ) : Address := (base.setTypeAndClear WOTS_HASH).setKeyPair i

/-- **`wots_leaf` = `wots_pkGen`** (Algorithm 6) at the address
    `setKeyPairAddress(i) ∘ setTypeAndClear(WOTS_HASH)` of `base`, for any
    `base` (the code's `with_type 0` does not clear, but every field it
    keeps is overwritten before use), with or without capture. -/
theorem wotsLeaf_pk (thash : Address → List Bytes → Bytes) (prf : Address → Bytes) (len : ℕ)
    (capture : Option (List ℕ)) (base : Address) (i : ℕ) :
    (wotsLeaf thash prf len capture base i).1 =
      fipsWotsPkGen (Tweak.ofCode thash prf) len (leafAdrs base i) := by
  simp only [wotsLeaf, fipsWotsPkGen]
  congr 1

/-- **The captured signature = `wots_sign`** (Algorithm 7): when
    `merkle_sign` passes `capture = Some (chain_lengths M, …)`, the array it
    gets back is `wots_sign(M, …)` at the same address, for every `n`-byte
    message (`n ≤ 136`). -/
theorem wotsLeaf_sig (thash : Address → List Bytes → Bytes) (prf : Address → Bytes)
    (M : Bytes) (hM : ∀ x ∈ M, x < 256) (hn : M.length ≤ 136) (len : ℕ)
    (base : Address) (i : ℕ) :
    (wotsLeaf thash prf len (some (chainLengths (2 * M.length) M)) base i).2 =
      some (fipsWotsSign (Tweak.ofCode thash prf) M.length len M (leafAdrs base i)) := by
  simp only [wotsLeaf, fipsWotsSign, Option.map_some, chainLengths_eq M hM hn]
  congr 1
  apply List.map_congr_left
  intro idx hidx
  have hd := fipsWotsDigits_getD_lt M.length M idx
  rw [chain_eq thash _ _ _ _ (by omega)]
  rfl

/-- **`wots_public_key_from_signature` (hashed with `keypair_address 1`, as
    `verify_formatted` does at lines 704–711) = `wots_pkFromSig`**
    (Algorithm 8) at the address `setKeyPairAddress(base.keypair) ∘
    setTypeAndClear(WOTS_HASH)` of `base` — the address `xmss_pkFromSig`
    (Algorithm 11 lines 1–2) passes. -/
theorem wotsPublicKeyFromSignature_eq (thash : Address → List Bytes → Bytes)
    (prf : Address → Bytes) (M : Bytes) (hM : ∀ x ∈ M, x < 256) (hn : M.length ≤ 136)
    (len : ℕ) (base : Address) (sig : List Bytes) :
    thash (keypairAddress 1 base) (wotsPublicKeyFromSignature thash len M.length base M sig) =
      fipsWotsPkFromSig (Tweak.ofCode thash prf) M.length len sig M
        (leafAdrs base base.keypair) := by
  simp only [wotsPublicKeyFromSignature, fipsWotsPkFromSig, chainLengths_eq M hM hn]
  congr 1
  apply List.map_congr_left
  intro idx hidx
  have hd := fipsWotsDigits_getD_lt M.length M idx
  rw [chain_eq thash _ _ _ _ (by omega)]
  rfl

/-- **WOTS+ correctness**: for every message `M`, every address and every
    tweakable hash, `wots_pkFromSig(wots_sign(M, ADRS), M, ADRS) =
    wots_pkGen(ADRS)` (chain composition, using that every digit is `< w`). -/
theorem fipsWots_correct (hs : Tweak) (n len : ℕ) (M : Bytes) (adrs : Address) :
    fipsWotsPkFromSig hs n len (fipsWotsSign hs n len M adrs) M adrs =
      fipsWotsPkGen hs len adrs := by
  simp only [fipsWotsPkFromSig, fipsWotsPkGen, fipsWotsSign]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < len := List.mem_range.mp hi
  have hd := fipsWotsDigits_getD_lt n M i
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_range]
  rw [show 16 - 1 = (fipsWotsDigits n M).getD i 0 + (16 - 1 - (fipsWotsDigits n M).getD i 0)
    by omega]
  conv_rhs => rw [← fipsChain_add]
  simp

end WOTS

end OcamlPq.SLHDSA
