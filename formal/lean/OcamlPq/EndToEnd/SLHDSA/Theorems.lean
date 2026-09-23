import OcamlPq.EndToEnd.SLHDSA.Congr

/-!
# SLH-DSA end to end: `slhdsa_engine.ml` + `slhdsa_hash.ml` = FIPS 205

The specification side: FIPS 205 §11 (`fipsPublicTweak`, `fipsTweak`,
`Hash.fipsPRFmsg specPrims`, `Hash.fipsHmsg specPrims`) over FIPS 180-4
SHA-256/SHA-512, FIPS 202 SHAKE256, FIPS 198-1 HMAC and RFC 8017 MGF1, and
FIPS 205 Algorithms 18, 19, 20, 22, 24 built from them (`slhKeygenInternal`,
`slhSignInternal`, `slhVerifyInternal`, `slhSign`, `slhVerify`).

The code side: the SLH-DSA area's models of `keypair_from_seed`,
`signing_key_of_octets`, `sign_formatted_with_randomness`,
`verify_formatted` over the Hash area's models of `Slhdsa_hash`
(`codeFam`), and models of the external `sign`, `sign_deterministic` and
`verify` (`codeSign`, `codeSignDeterministic`, `codeVerify`).

## Hypotheses

* `P ∈ allParams` (the twelve parameter sets) and `P.a + 7 ≤ w` for the
  OCaml `int` width `w` (every platform: `platform_ok`).
* Key components, randomness and verification keys are `n`-byte strings
  (as every key and randomness the OCaml API accepts).
* `MsgOk P M`: for the four sets that use SHA-512 (`usesSha512`: SHA2 with
  `n ∈ {24, 32}`), the (formatted) message has fewer than `2^57` bytes. The
  OCaml SHA-512 agrees with FIPS 180-4 only below `2^61` bytes; every OCaml
  string is shorter than `2^57` bytes (`Sys.max_string_length = 2^57 − 9` on
  64-bit platforms, less elsewhere). Vacuous for the other eight sets.
* `SigOk P sig`: for the same four sets, the blocks of the (block-level)
  signature given to `verify_formatted` have at most `n` bytes — the code
  cuts them as `n`-byte substrings. Vacuous for the other eight sets.

`verify_sign_e2e` and its variants (the code's verification accepts the
code's signatures) need none of the length hypotheses: they only use the
code's hash functions, through `hashOk_code`.
-/

namespace OcamlPq.EndToEnd.SLHDSA

open OcamlPq.SLHDSA
open WOTS XMSS FORS Treehash Hypertree Base2b

/-! ## FIPS 205 over the specified primitives -/

section Spec

variable (P : Params)

/-- FIPS 205 §11 `F`, `H`, `T_ℓ` keyed by `PK.seed`, over the specified
    primitives, at the ADRS `address_full a` (§11.1 for SHAKE; §11.2.1 /
    §11.2.2 for SHA2, which compress it to `ADRS_c`). `PRF` needs `SK.seed`
    (see `fipsTweak`); a verifier never calls it, and here it returns `[]`. -/
noncomputable def fipsPublicTweak (pkSeed : Bytes) : Tweak where
  F a m := Hash.fipsF specPrims P pkSeed (Code.addressFull a) m
  H a l r := Hash.fipsHT specPrims P pkSeed (Code.addressFull a) (l ++ r)
  T a ms := Hash.fipsHT specPrims P pkSeed (Code.addressFull a) ms.flatten
  PRF _ := []

/-- FIPS 205 §11 `F`, `H`, `T_ℓ`, `PRF` keyed by `PK.seed` and `SK.seed`,
    over the specified primitives. -/
noncomputable def fipsTweak (pkSeed skSeed : Bytes) : Tweak :=
  { fipsPublicTweak P pkSeed with
    PRF := fun a => Hash.fipsPRF specPrims P pkSeed skSeed (Code.addressFull a) }

/-- **FIPS 205 Algorithm 18** `slh_keygen_internal(SK.seed, SK.prf, PK.seed)`,
    returning `SK = (SK.seed, SK.prf, PK.seed, PK.root)` (`PK = (PK.seed,
    PK.root)`). -/
noncomputable def slhKeygenInternal (skSeed skPrf pkSeed : Bytes) : Bytes × Bytes × Bytes × Bytes :=
  (skSeed, skPrf, pkSeed, keygenRoot P (fipsTweak P pkSeed skSeed))

/-- **FIPS 205 Algorithm 19** `slh_sign_internal(M, SK, addrnd)`. -/
noncomputable def slhSignInternal (M skSeed skPrf pkSeed pkRoot addrnd : Bytes) : List Bytes :=
  signInternal P (fipsTweak P pkSeed skSeed) (Hash.fipsPRFmsg specPrims P)
    (Hash.fipsHmsg specPrims P) M skPrf pkSeed pkRoot addrnd

/-- **FIPS 205 Algorithm 20** `slh_verify_internal(M, SIG, PK)` (block level). -/
noncomputable def slhVerifyInternal (M : Bytes) (SIG : List Bytes) (pkSeed pkRoot : Bytes) : Bool :=
  verifyInternal P (fipsPublicTweak P pkSeed) (Hash.fipsHmsg specPrims P) M SIG pkSeed pkRoot

/-- **FIPS 205 Algorithm 22** `slh_sign(M, ctx, SK)` with the randomness
    `addrnd` (line 2; `addrnd = PK.seed` in the deterministic variant);
    `none` is the `⊥` of line 1 (`|ctx| > 255`). -/
noncomputable def slhSign (M ctx : Bytes) (SK : Bytes × Bytes × Bytes × Bytes) (addrnd : Bytes) :
    Option (List Bytes) :=
  if ctx.length > 255 then none
  else some (slhSignInternal P (Top.fipsFormat ctx M) SK.1 SK.2.1 SK.2.2.1 SK.2.2.2 addrnd)

/-- **FIPS 205 Algorithm 24** `slh_verify(M, SIG, ctx, PK)`. -/
noncomputable def slhVerify (M : Bytes) (SIG : List Bytes) (ctx : Bytes) (PK : Bytes × Bytes) :
    Bool :=
  if ctx.length > 255 then false
  else slhVerifyInternal P (Top.fipsFormat ctx M) SIG PK.1 PK.2

end Spec

/-! ## Code models of the external API (slhdsa_engine.ml 644–730) -/

section Code

variable (P : Params) (w : ℕ)

/-- `sign ?(context = ctx) ~random key ~message:M` (lines 644–650) where
    `random P.n` returns `randomness`, with `key = (sk_seed, sk_prf, pk_seed,
    pk_root)`: `Context_too_long` if `|ctx| > 255`, otherwise
    `sign_formatted_with_randomness key ~formatted_message:(formatted_prefix
    ctx ^ M) randomness`. `none` is any error or exception (a wrong-length
    `randomness` makes `require_random` raise). -/
def codeSign (key : Bytes × Bytes × Bytes × Bytes) (ctx M randomness : Bytes) :
    Option (List Bytes) :=
  if ctx.length > 255 then none
  else Top.signFormatted (codeFam P) P w key.1 key.2.1 key.2.2.1 key.2.2.2
    (Top.formattedPrefix ctx ++ M) randomness

/-- `sign_deterministic ?(context = ctx) key ~message:M` (lines 652–657):
    the randomness is `key.verification_key.pk_seed`. -/
def codeSignDeterministic (key : Bytes × Bytes × Bytes × Bytes) (ctx M : Bytes) :
    Option (List Bytes) :=
  if ctx.length > 255 then none
  else Top.signFormatted (codeFam P) P w key.1 key.2.1 key.2.2.1 key.2.2.2
    (Top.formattedPrefix ctx ++ M) key.2.2.1

/-- `verify ?(context = ctx) {pk_seed; pk_root} ~message:M signature`
    (lines 724–729), on the signature's `n`-byte blocks. -/
def codeVerify (pkSeed pkRoot ctx M : Bytes) (sig : List Bytes) : Bool :=
  if ctx.length > 255 then false
  else Top.verifyFormatted (codeFam P) P w pkSeed pkRoot (Top.formattedPrefix ctx ++ M) sig

end Code

/-! ## Length side conditions -/

/-- See the module doc. -/
def MsgOk (P : Params) (M : Bytes) : Prop := usesSha512 P → M.length < 2 ^ 57

/-- A signature block the SHA-512 sets hash without leaving FIPS 180-4's
    domain: at most `n` bytes (every block the code cuts is `n` bytes). -/
def BlockOk (P : Params) (b : Bytes) : Prop := usesSha512 P → b.length ≤ P.n

/-- See the module doc. -/
def SigOk (P : Params) (sig : List Bytes) : Prop := ∀ b ∈ sig, BlockOk P b

theorem MsgOk.of_length {P : Params} {M : Bytes} (h : M.length < 2 ^ 57) : MsgOk P M := fun _ => h

theorem MsgOk.of_not {P : Params} (h : ¬ usesSha512 P) (M : Bytes) : MsgOk P M :=
  fun hu => absurd hu h

theorem SigOk.of_not {P : Params} (h : ¬ usesSha512 P) (sig : List Bytes) : SigOk P sig :=
  fun _ _ hu => absurd hu h

theorem SigOk.of_blocks {P : Params} {sig : List Bytes} (h : ∀ b ∈ sig, b.length = P.n) :
    SigOk P sig := fun b hb _ => (h b hb).le

/-- The four SHA-512 sets. -/
theorem usesSha512_iff : ∀ P ∈ allParams,
    usesSha512 P ↔ P ∈ [sha2_192s, sha2_192f, sha2_256s, sha2_256f] := by decide +kernel

theorem params_small : ∀ P ∈ allParams,
    P.len ≤ 67 ∧ P.k ≤ 35 ∧ P.n ≤ 32 ∧ P.m ≤ 49 ∧ 2 ≤ P.len ∧ 2 ≤ P.k := by decide +kernel

/-- Every OCaml platform's `int` width is covered by the area's theorems. -/
theorem platform_ok (P : Params) (hP : P ∈ allParams) (p : Platform) : P.a + 7 ≤ p.intBits := by
  have := (sizes_portable P hP).2.2.2.1
  have := p.intBits_ge
  omega

/-! ## The code's tweakable hash agrees with FIPS 205 §11 on every call -/

theorem flatten_length_le (ms : List Bytes) (n : ℕ) (h : ∀ m ∈ ms, m.length ≤ n) :
    ms.flatten.length ≤ ms.length * n := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    have h1 := h m (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    rw [Nat.succ_mul]
    omega

theorem prf_length_code (P : Params) (hP : P ∈ allParams) (pkSeed skSeed : Bytes) (a : Address) :
    (Hash.prf codePrims P pkSeed skSeed a).length = P.n := by
  have hn : P.n ≤ 32 := by rcases n_cases P hP with h | h | h <;> omega
  unfold Hash.prf
  rcases h : P.hash with _ | _
  · exact (truncate_nbytes _ _ (by rw [codePrims_sha256_length]; omega) (codePrims_sha256_lt _)).1
  · exact codePrims_shake256_length _ _

/-- **F, H, T_ℓ.** The code's `thash` (any `PRF`) and FIPS 205 §11 over the
    specified primitives agree on every call of the algorithms: one block
    (`F`, always SHA-256/SHAKE256), two blocks (`H`), `len` or `k` blocks
    (`T_ℓ`, `ℓ ≥ 2`), all blocks `BlockOk`; and every `thash` output is
    `n` bytes, hence `BlockOk`. -/
theorem agree_code (P : Params) (hP : P ∈ allParams) (pkSeed : Bytes) (hpk : pkSeed.length = P.n)
    (prf : Address → Bytes) :
    Agree (BlockOk P) P.len P.k (Tweak.ofCode ((codeFam P).thash pkSeed) prf)
      (fipsPublicTweak P pkSeed) := by
  obtain ⟨hlen, hk, hn, -, hl2, hk2⟩ := params_small P hP
  have hout : ∀ a bs, ((codeFam P).thash pkSeed a bs).length = P.n := fun a bs =>
    ((hashOk_code P hP).thash pkSeed a bs).1
  refine ⟨fun _ => Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a m _
    show Hash.thash codePrims P pkSeed a [m] = Hash.fipsF specPrims P pkSeed (Code.addressFull a) m
    rw [thash_one _ _ _ hpk, fipsF_code]
  · intro a l r hl hr
    show Hash.thash codePrims P pkSeed a [l, r] =
      Hash.fipsHT specPrims P pkSeed (Code.addressFull a) (l ++ r)
    rw [thash_many _ _ hP _ hpk _ _ (by simp)]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    refine fipsHT_code P _ _ _ (by omega) (fun hu => ?_)
    have := hl hu
    have := hr hu
    simp only [List.length_append]
    omega
  · intro a ms hms hb
    show Hash.thash codePrims P pkSeed a ms =
      Hash.fipsHT specPrims P pkSeed (Code.addressFull a) ms.flatten
    rw [thash_many _ _ hP _ hpk _ _ (by omega)]
    refine fipsHT_code P _ _ _ (by omega) (fun hu => ?_)
    have h1 := flatten_length_le ms P.n (fun m hm => hb m hm hu)
    have h2 : ms.length * P.n ≤ 67 * 32 := Nat.mul_le_mul (by omega) hn
    omega
  · intro a m _; exact (hout a [m]).le
  · intro a l r _; exact (hout a [l, r]).le
  · intro a ms _; exact (hout a ms).le

theorem agree_code' (P : Params) (hP : P ∈ allParams) (pkSeed : Bytes) (hpk : pkSeed.length = P.n)
    (prf : Address → Bytes) (skSeed : Bytes) :
    Agree (BlockOk P) P.len P.k (Tweak.ofCode ((codeFam P).thash pkSeed) prf)
      (fipsTweak P pkSeed skSeed) :=
  have h := agree_code P hP pkSeed hpk prf
  ⟨h.nil, h.F, h.H, h.T, h.F_S, h.H_S, h.T_S⟩

/-- **PRF.** The code's `prf` is FIPS 205 §11 `PRF` over the specified
    primitives (SHA-256 / SHAKE256, no length condition); outputs are `n`
    bytes. -/
theorem agreePRF_code (P : Params) (hP : P ∈ allParams) (pkSeed skSeed : Bytes)
    (hpk : pkSeed.length = P.n) :
    AgreePRF (BlockOk P) (Tweak.ofCode ((codeFam P).thash pkSeed) ((codeFam P).prf pkSeed skSeed))
      (fipsTweak P pkSeed skSeed) := by
  refine ⟨fun a => ?_, fun a _ => ?_⟩
  · show Hash.prf codePrims P pkSeed skSeed a =
      Hash.fipsPRF specPrims P pkSeed skSeed (Code.addressFull a)
    rw [prf_fips _ _ _ _ hpk, fipsPRF_code]
  · exact (prf_length_code P hP pkSeed skSeed a).le

/-! ## Headline theorems -/

section Main

variable (P : Params) (w : ℕ)

/-- **Key generation, end to end (Algorithm 18).** For every parameter set
    and every seed of at least `3n` bytes, the code's `keypair_from_seed`
    (over the OCaml SHA-2/SHAKE models) returns FIPS 205's
    `slh_keygen_internal(SK.seed, SK.prf, PK.seed)` with FIPS 180-4 / FIPS
    202 hash functions. -/
theorem keypairFromSeed_e2e (hP : P ∈ allParams) (seed : Bytes) (hseed : 3 * P.n ≤ seed.length) :
    Top.keypairFromSeed (codeFam P) P seed =
      some (slhKeygenInternal P ((seed.drop 0).take P.n) ((seed.drop P.n).take P.n)
        ((seed.drop (2 * P.n)).take P.n)) := by
  have hpk : ((seed.drop (2 * P.n)).take P.n).length = P.n := by simp; omega
  rw [Top.keypairFromSeed_eq, fipsKeygenRoot_eq, slhKeygenInternal,
    keygenRoot_congr P (agree_code' P hP _ hpk _ _) (agreePRF_code P hP _ _ hpk)]

/-- **`signing_key_of_octets`, end to end.** A `4n`-byte signing key is
    accepted iff its `PK.root` is the FIPS 205 Algorithm 18 root (with the
    specified hash functions) of its `SK.seed` and `PK.seed`. -/
theorem signingKeyRootOk_e2e (hP : P ∈ allParams) (value : Bytes)
    (hv : 4 * P.n ≤ value.length) :
    Top.signingKeyRootOk (codeFam P) P value = true ↔
      (value.drop (3 * P.n)).take P.n =
        (slhKeygenInternal P ((value.drop 0).take P.n) ((value.drop P.n).take P.n)
          ((value.drop (2 * P.n)).take P.n)).2.2.2 := by
  have hpk : ((value.drop (2 * P.n)).take P.n).length = P.n := by simp; omega
  rw [Top.signingKeyRootOk_iff, fipsKeygenRoot_eq, slhKeygenInternal,
    keygenRoot_congr P (agree_code' P hP _ hpk _ _) (agreePRF_code P hP _ _ hpk)]

/-- **Signing, end to end (Algorithm 19).** For every parameter set, every
    `int` width `w ≥ a + 7` (every platform), every key with `n`-byte
    components, every message (fewer than `2^57` bytes for the SHA-512
    sets) and every `n`-byte randomness, the code's
    `sign_formatted_with_randomness` returns FIPS 205's
    `slh_sign_internal(M, SK, addrnd = randomness)` with the specified hash
    functions. -/
theorem signFormatted_e2e (hP : P ∈ allParams) (hw : P.a + 7 ≤ w)
    (skSeed skPrf pkSeed pkRoot M randomness : Bytes) (hprf : skPrf.length = P.n)
    (hpk : pkSeed.length = P.n) (hroot : pkRoot.length = P.n) (hr : randomness.length = P.n)
    (hM : MsgOk P M) :
    Top.signFormatted (codeFam P) P w skSeed skPrf pkSeed pkRoot M randomness =
      some (slhSignInternal P M skSeed skPrf pkSeed pkRoot randomness) := by
  obtain ⟨-, -, hn, hm, -, -⟩ := params_small P hP
  rw [Top.signFormatted_eq (codeFam P) P w hP hw (hashOk_code P hP) _ _ _ _ _ _ hr,
    fipsSlhSignInternal_eq]
  congr 1
  apply signInternal_congr P (agree_code' P hP pkSeed hpk _ skSeed) (agreePRF_code P hP _ _ hpk)
  · show Hash.prfMessage codePrims P skPrf randomness M =
      Hash.fipsPRFmsg specPrims P skPrf randomness M
    rw [Hash.prfMessage_eq, fipsPRFmsg_code]
    intro hu
    have := hM hu
    simp only [List.length_append]
    omega
  · show Hash.hashMessage codePrims P (Hash.prfMessage codePrims P skPrf randomness M) pkSeed
        pkRoot M =
      Hash.fipsHmsg specPrims P (Hash.prfMessage codePrims P skPrf randomness M) pkSeed pkRoot M
    rw [Hash.hashMessage_eq, fipsHmsg_code P (by omega)]
    intro hu
    have := hM hu
    have := prfMessage_length P hP skPrf randomness M
    simp only [List.length_append]
    omega

/-- A randomness of the wrong length is rejected (`Invalid_length`). -/
theorem signFormatted_badRandomness (skSeed skPrf pkSeed pkRoot M randomness : Bytes)
    (hr : randomness.length ≠ P.n) :
    Top.signFormatted (codeFam P) P w skSeed skPrf pkSeed pkRoot M randomness = none := by
  simp [Top.signFormatted, hr]

/-- **Verification, end to end (Algorithm 20).** For every parameter set,
    every `int` width `w ≥ a + 7`, every `n`-byte `PK.seed`, `PK.root`,
    every message (fewer than `2^57` bytes for the SHA-512 sets) and every
    block-level signature (adversarial ones included; blocks of at most `n`
    bytes for the SHA-512 sets), the code's `verify_formatted` returns
    FIPS 205's `slh_verify_internal(M, SIG, PK)` with the specified hash
    functions, including the signature-length check. -/
theorem verifyFormatted_e2e (hP : P ∈ allParams) (hw : P.a + 7 ≤ w) (pkSeed pkRoot M : Bytes)
    (sig : List Bytes) (hpk : pkSeed.length = P.n) (hroot : pkRoot.length = P.n)
    (hM : MsgOk P M) (hsig : SigOk P sig) :
    Top.verifyFormatted (codeFam P) P w pkSeed pkRoot M sig =
      slhVerifyInternal P M sig pkSeed pkRoot := by
  obtain ⟨-, -, hn, hm, -, -⟩ := params_small P hP
  rw [Top.verifyFormatted_eq (codeFam P) P w hP hw (hashOk_code P hP), fipsSlhVerifyInternal_eq]
  apply verifyInternal_congr P (agree_code P hP pkSeed hpk _) _ _ _ _ _ _ hsig
  show Hash.hashMessage codePrims P (sig.getD 0 []) pkSeed pkRoot M =
    Hash.fipsHmsg specPrims P (sig.getD 0 []) pkSeed pkRoot M
  rw [Hash.hashMessage_eq, fipsHmsg_code P (by omega)]
  intro hu
  have h1 := hM hu
  have h2 : (sig.getD 0 []).length ≤ P.n := (agree_code P hP pkSeed hpk (fun _ => [])).getD hsig 0 hu
  simp only [List.length_append]
  omega

/-- **`sign`, end to end (Algorithm 22).** For every parameter set, platform
    width, context, key with `n`-byte components, message (formatted
    message shorter than `2^57` bytes for the SHA-512 sets) and `n`-byte
    randomness, the code's `sign` = FIPS 205 `slh_sign(M, ctx, SK)` with
    `addrnd = randomness` (both `⊥` when `|ctx| > 255`). -/
theorem sign_e2e (hP : P ∈ allParams) (hw : P.a + 7 ≤ w) (skSeed skPrf pkSeed pkRoot : Bytes)
    (hprf : skPrf.length = P.n) (hpk : pkSeed.length = P.n) (hroot : pkRoot.length = P.n)
    (ctx M randomness : Bytes) (hr : randomness.length = P.n) (hM : MsgOk P (Top.fipsFormat ctx M)) :
    codeSign P w (skSeed, skPrf, pkSeed, pkRoot) ctx M randomness =
      slhSign P M ctx (skSeed, skPrf, pkSeed, pkRoot) randomness := by
  unfold codeSign slhSign
  split_ifs with hc
  · rfl
  · dsimp only
    rw [Top.formattedPrefix_eq ctx M (by omega)]
    exact signFormatted_e2e P w hP hw _ _ _ _ _ _ hprf hpk hroot hr hM

/-- **`sign_deterministic`, end to end (Algorithm 22, deterministic
    variant `addrnd = PK.seed`).** -/
theorem signDeterministic_e2e (hP : P ∈ allParams) (hw : P.a + 7 ≤ w)
    (skSeed skPrf pkSeed pkRoot : Bytes) (hprf : skPrf.length = P.n) (hpk : pkSeed.length = P.n)
    (hroot : pkRoot.length = P.n) (ctx M : Bytes) (hM : MsgOk P (Top.fipsFormat ctx M)) :
    codeSignDeterministic P w (skSeed, skPrf, pkSeed, pkRoot) ctx M =
      slhSign P M ctx (skSeed, skPrf, pkSeed, pkRoot) pkSeed := by
  unfold codeSignDeterministic slhSign
  split_ifs with hc
  · rfl
  · dsimp only
    rw [Top.formattedPrefix_eq ctx M (by omega)]
    exact signFormatted_e2e P w hP hw _ _ _ _ _ _ hprf hpk hroot hpk hM

/-- **`verify`, end to end (Algorithm 24).** -/
theorem verify_e2e (hP : P ∈ allParams) (hw : P.a + 7 ≤ w) (pkSeed pkRoot : Bytes)
    (hpk : pkSeed.length = P.n) (hroot : pkRoot.length = P.n) (ctx M : Bytes) (sig : List Bytes)
    (hM : MsgOk P (Top.fipsFormat ctx M)) (hsig : SigOk P sig) :
    codeVerify P w pkSeed pkRoot ctx M sig = slhVerify P M sig ctx (pkSeed, pkRoot) := by
  unfold codeVerify slhVerify
  split_ifs with hc
  · rfl
  · dsimp only
    rw [Top.formattedPrefix_eq ctx M (by omega)]
    exact verifyFormatted_e2e P w hP hw _ _ _ _ hpk hroot hM hsig

/-- The Algorithm 18 root is an `n`-byte string. -/
theorem slhKeygenInternal_root_length (hP : P ∈ allParams) (skSeed skPrf pkSeed : Bytes)
    (hpk : pkSeed.length = P.n) : (slhKeygenInternal P skSeed skPrf pkSeed).2.2.2.length = P.n := by
  simp only [slhKeygenInternal]
  rw [← keygenRoot_congr P (agree_code' P hP _ hpk _ _) (agreePRF_code P hP _ _ hpk),
    ← fipsKeygenRoot_eq]
  exact (Hypertree.fipsXmssNode_nbytes _ _ P.len P.n ((hashOk_code P hP).thash pkSeed) _ _ _).1

/-- **Key generation then signing, end to end.** For a `3n`-byte seed (as
    `generate` and `signing_key_of_seed` require), signing with the key
    `keypair_from_seed` returns is `slh_sign` (Algorithm 22) under the
    Algorithm 18 key of the seed. -/
theorem keygen_sign_e2e (hP : P ∈ allParams) (hw : P.a + 7 ≤ w) (seed : Bytes)
    (hseed : seed.length = 3 * P.n) (ctx M randomness : Bytes) (hr : randomness.length = P.n)
    (hM : MsgOk P (Top.fipsFormat ctx M)) :
    (Top.keypairFromSeed (codeFam P) P seed).bind (fun key => codeSign P w key ctx M randomness) =
      slhSign P M ctx (slhKeygenInternal P ((seed.drop 0).take P.n) ((seed.drop P.n).take P.n)
        ((seed.drop (2 * P.n)).take P.n)) randomness := by
  have hpk : ((seed.drop (2 * P.n)).take P.n).length = P.n := by simp; omega
  have hprf : ((seed.drop P.n).take P.n).length = P.n := by simp; omega
  have hroot := slhKeygenInternal_root_length P hP ((seed.drop 0).take P.n)
    ((seed.drop P.n).take P.n) _ hpk
  rw [keypairFromSeed_e2e P hP seed (by omega), Option.bind_some]
  simp only [slhKeygenInternal] at hroot ⊢
  exact sign_e2e P w hP hw _ _ _ _ hprf hpk hroot ctx M randomness hr hM

/-! ### Correctness of the concrete code: verify accepts sign -/

/-- A key `(SK.seed, SK.prf, PK.seed, PK.root)` whose root is the one the
    code computes (keys from `keypair_from_seed`, and keys accepted by
    `signing_key_of_octets`). -/
def ValidKey (key : Bytes × Bytes × Bytes × Bytes) : Prop :=
  key.2.2.2 = Top.fipsKeygenRoot (codeFam P) P key.1 key.2.2.1

theorem validKey_of_keypairFromSeed (seed : Bytes) (key : Bytes × Bytes × Bytes × Bytes)
    (h : Top.keypairFromSeed (codeFam P) P seed = some key) : ValidKey P key := by
  rw [Top.keypairFromSeed_eq, Option.some.injEq] at h
  subst h
  rfl

theorem validKey_of_signingKeyRootOk (value : Bytes)
    (h : Top.signingKeyRootOk (codeFam P) P value = true) :
    ValidKey P ((value.drop 0).take P.n, (value.drop P.n).take P.n,
      (value.drop (2 * P.n)).take P.n, (value.drop (3 * P.n)).take P.n) :=
  (Top.signingKeyRootOk_iff _ P value).mp h

/-- **End-to-end correctness, formatted level.** On every platform width
    `w ≥ a + 7`, for every valid key, every message and every randomness,
    whenever the concrete `sign_formatted_with_randomness` returns a
    signature, the concrete `verify_formatted` accepts it. -/
theorem verify_signFormatted_e2e (hP : P ∈ allParams) (hw : P.a + 7 ≤ w)
    (key : Bytes × Bytes × Bytes × Bytes) (hkey : ValidKey P key) (M randomness : Bytes)
    (sig : List Bytes)
    (hsig : Top.signFormatted (codeFam P) P w key.1 key.2.1 key.2.2.1 key.2.2.2 M randomness =
      some sig) :
    Top.verifyFormatted (codeFam P) P w key.2.2.1 key.2.2.2 M sig = true := by
  obtain ⟨skSeed, skPrf, pkSeed, pkRoot⟩ := key
  simp only [ValidKey] at hkey hsig ⊢
  subst hkey
  have hr : randomness.length = P.n := by
    by_contra hne
    rw [signFormatted_badRandomness _ _ _ _ _ _ _ _ hne] at hsig
    cases hsig
  exact Top.verify_sign (codeFam P) P w hP hw (hashOk_code P hP) _ _ _ _ _ hr sig hsig

/-- **End-to-end correctness of the external API.** On every platform, for
    every parameter set, every key produced by `keypair_from_seed` (or
    accepted by `signing_key_of_octets`: `ValidKey`), every context, message
    and randomness: if `sign` returns a signature, `verify` accepts it. -/
theorem verify_sign_e2e (hP : P ∈ allParams) (p : Platform) (key : Bytes × Bytes × Bytes × Bytes)
    (hkey : ValidKey P key) (ctx M randomness : Bytes) (sig : List Bytes)
    (hsig : codeSign P p.intBits key ctx M randomness = some sig) :
    codeVerify P p.intBits key.2.2.1 key.2.2.2 ctx M sig = true := by
  unfold codeSign at hsig
  unfold codeVerify
  split_ifs at hsig ⊢ with hc
  exact verify_signFormatted_e2e P p.intBits hP (platform_ok P hP p) key hkey _ _ sig hsig

/-- The same for `sign_deterministic`. -/
theorem verify_signDeterministic_e2e (hP : P ∈ allParams) (p : Platform)
    (key : Bytes × Bytes × Bytes × Bytes) (hkey : ValidKey P key) (ctx M : Bytes)
    (sig : List Bytes) (hsig : codeSignDeterministic P p.intBits key ctx M = some sig) :
    codeVerify P p.intBits key.2.2.1 key.2.2.2 ctx M sig = true := by
  unfold codeSignDeterministic at hsig
  unfold codeVerify
  split_ifs at hsig ⊢ with hc
  exact verify_signFormatted_e2e P p.intBits hP (platform_ok P hP p) key hkey _ _ sig hsig

/-- Signatures are platform independent: a signature produced on any
    platform verifies on any other. -/
theorem verify_sign_cross_platform (hP : P ∈ allParams) (p q : Platform)
    (key : Bytes × Bytes × Bytes × Bytes) (hkey : ValidKey P key) (ctx M randomness : Bytes)
    (sig : List Bytes) (hsig : codeSign P p.intBits key ctx M randomness = some sig) :
    codeVerify P q.intBits key.2.2.1 key.2.2.2 ctx M sig = true := by
  have hs : codeSign P q.intBits key ctx M randomness = some sig := by
    rw [← hsig]
    unfold codeSign
    split_ifs
    · rfl
    · by_cases hr : randomness.length = P.n
      · rw [Top.signFormatted_eq _ P _ hP (platform_ok P hP q) (hashOk_code P hP) _ _ _ _ _ _ hr,
          Top.signFormatted_eq _ P _ hP (platform_ok P hP p) (hashOk_code P hP) _ _ _ _ _ _ hr]
      · rw [signFormatted_badRandomness _ _ _ _ _ _ _ _ hr,
          signFormatted_badRandomness _ _ _ _ _ _ _ _ hr]
  exact verify_sign_e2e P hP q key hkey ctx M randomness sig hs

end Main

end OcamlPq.EndToEnd.SLHDSA
