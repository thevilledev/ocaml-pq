import OcamlPq.EndToEnd.MLDSA.Pack

/-!
# Key generation end to end

* `keyOps P`: the `MLDSAAlg.KeyOps` bundle of the concrete OCaml models
  (arithmetic area: `ntt`, `inverse_ntt`, `matrix_vector_ntt`, `add_mod`,
  `power2round`; Encoding area: `pack_t1`, `pack_eta`, `pack_t0`), through
  the adapters of `Adapters.lean`.
* `keyFips P`: the `KeyFips` bundle of FIPS 204 transcriptions (Algorithms
  41, 42, 48, 35, 16, 17 and addition in `R_q`).

**`KeyOps.Refines (keyOps P) (keyFips P) P` is false**: its fields `packT1`,
`packEta`, `packT0` quantify over *all* polynomials, and outside the FIPS
input ranges the OCaml `pack_codes` and the transcribed `SimpleBitPack` /
`BitPack` differ (see `Pack.lean`). Every other field holds
(`keyOps_refines_arith`). The bridge: `keyOpsIdeal P` is `keyOps P` with
the three packers replaced by the FIPS ones; it satisfies `Refines`
(`keyOpsIdeal_refines`), and on every value key generation actually packs
(`t1 ∈ [0, 2^10)`, `t0 ∈ (−2^12, 2^12]` from `Power2Round`, `s1, s2 ∈ [−η, η]`
from `RejBoundedPoly`) the two bundles agree (`keypairFromSeed_ideal`).

`MLDSAAlg.keypairFromSeed_eq` also asks the sampler hypotheses for *every*
seed `ρ` (`∀ ρ, ExpandMatrixReturns G P ρ (expandMatrix ρ)`), which would
require `expand_matrix` to terminate on every input; `keypairFromSeed_eq_at`
re-proves it with the hypotheses only at the seeds `keypair_from_seed ξ`
uses, and in the weaker "value" form (`= ExpandA(ρ)`), which the
"returns" form implies.
-/

namespace OcamlPq.EndToEnd.MLDSA

open OcamlPq.MLDSAAlg

/-! ## The bundles -/

/-- **The OCaml building blocks of key generation** (`KeyOps`). -/
def keyOps (P : Params) : KeyOps where
  ntt := MLDSA.ntt
  inverseNtt := ocamlInverseNtt
  matrixVectorNtt := ocamlMatVec P.l
  addMod := MLDSA.addMod
  power2round := MLDSA.power2round
  packT1 := ocamlPackT1
  packEta := ocamlPackEta P.eta
  packT0 := ocamlPackT0

/-- **The FIPS 204 building blocks of Algorithm 6** (`KeyFips`). -/
def keyFips (P : Params) : KeyFips where
  NTT := fipsNTT
  NTTinv := fipsNTTinv
  mulMatVec := fipsMulMatVec P.l
  addPoly := fipsAddPoly
  power2Round := MLDSA.power2RoundSpec
  simpleBitPack := fipsSimpleBitPack
  bitPack := fipsBitPack

/-- `keyOps` with the packers replaced by FIPS 204's (used only in proofs). -/
def keyOpsIdeal (P : Params) : KeyOps :=
  { keyOps P with
    packT1 := fun p => fipsSimpleBitPack p (2 ^ (bitlen (q - 1) - d) - 1)
    packEta := fun p => fipsBitPack p P.eta P.eta
    packT0 := fun p => fipsBitPack p (2 ^ (d - 1) - 1) (2 ^ (d - 1)) }

/-- The arithmetic fields of `KeyOps.Refines` hold for the concrete models,
    on every input. -/
theorem keyOps_refines_arith (P : Params) :
    (keyOps P).ntt = (keyFips P).NTT ∧ (keyOps P).inverseNtt = (keyFips P).NTTinv ∧
    (keyOps P).matrixVectorNtt = (keyFips P).mulMatVec ∧
    (∀ a b : Poly, (fun i => (keyOps P).addMod (a i) (b i)) = (keyFips P).addPoly a b) ∧
    (keyOps P).power2round = (keyFips P).power2Round ∧
    (∀ (A A' : PolyMat) (v v' : PolyVec),
      (∀ r < P.k, ∀ s < P.l, A r s = A' r s) → (∀ s < P.l, v s = v' s) →
      ∀ r < P.k, (keyFips P).mulMatVec A v r = (keyFips P).mulMatVec A' v' r) :=
  ⟨ntt_eq_fips, inverseNtt_eq_fips, matVec_eq_fips P.l, addMod_eq_fips,
    funext MLDSA.power2round_eq_spec,
    fun A A' v v' hA hv r hr => fipsMulMatVec_local P.l A A' v v' r (hA r hr) hv⟩

/-- The packing fields of `KeyOps.Refines`, on the FIPS input ranges. -/
theorem keyOps_refines_pack {P : Params} (hP : P.Valid) :
    (∀ p : Poly, (∀ i < 256, 0 ≤ p i ∧ p i < 2 ^ 10) →
      (keyOps P).packT1 p = (keyFips P).simpleBitPack p (2 ^ (bitlen (q - 1) - d) - 1)) ∧
    (∀ p : Poly, (∀ i < 256, -(P.eta : ℤ) ≤ p i ∧ p i ≤ P.eta) →
      (keyOps P).packEta p = (keyFips P).bitPack p P.eta P.eta) ∧
    (∀ p : Poly, (∀ i < 256, -(2 ^ 12 : ℤ) < p i ∧ p i ≤ 2 ^ 12) →
      (keyOps P).packT0 p = (keyFips P).bitPack p (2 ^ (d - 1) - 1) (2 ^ (d - 1))) := by
  have hf := e2eFacts hP
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · simp only [keyOps, keyFips]
    rw [hf.t1Bound]; exact packT1_eq_fips p hp
  · simp only [keyOps, keyFips]
    exact packEta_eq_fips hf.eta p hp
  · simp only [keyOps, keyFips]
    rw [hf.t0a, hf.t0b]; exact packT0_eq_fips p hp

/-- **`keyOpsIdeal P` refines `keyFips P`** (every field of `KeyOps.Refines`). -/
theorem keyOpsIdeal_refines (P : Params) : (keyOpsIdeal P).Refines (keyFips P) P where
  ntt := ntt_eq_fips
  inverseNtt := inverseNtt_eq_fips
  matrixVectorNtt := matVec_eq_fips P.l
  addMod := addMod_eq_fips
  power2round := funext MLDSA.power2round_eq_spec
  packT1 := fun _ => by simp only [keyOpsIdeal, keyFips]
  packEta := fun _ => by simp only [keyOpsIdeal, keyFips]
  packT0 := fun _ => by simp only [keyOpsIdeal, keyFips]
  mulMatVec_local := fun A A' v v' hA hv r hr => fipsMulMatVec_local P.l A A' v v' r (hA r hr) hv

/-! ## Ranges -/

/-- `Power2Round` outputs: `t1 ∈ [0, 2^10)`, `t0 ∈ (−2^12, 2^12]`. -/
theorem computePublicParts_range (E : KeyOps) (hE : E.power2round = MLDSA.power2round)
    (m : PolyMat) (e : ExpandedKey) (r i : ℕ) :
    (0 ≤ (computePublicParts E m e).1 r i ∧ (computePublicParts E m e).1 r i < 2 ^ 10) ∧
    (-(2 ^ 12 : ℤ) < (computePublicParts E m e).2 r i ∧
      (computePublicParts E m e).2 r i ≤ 2 ^ 12) := by
  unfold computePublicParts
  simp only [hE]
  have := MLDSA.power2round_range
    (E.addMod (E.inverseNtt (E.matrixVectorNtt m (fun i => E.ntt (e.s1 i)) r) i) (e.s2 r i))
  omega

/-- Every value of FIPS 204 `RejBoundedPoly` lies in `[−η, η]` (and it is `0`
    when the sampler does not terminate, by the convention of `rejBoundedPoly`). -/
theorem rejBoundedPoly_range {eta : ℕ} (heta : eta = 2 ∨ eta = 4) (s : ℕ → Byte) (i : ℕ) :
    -(eta : ℤ) ≤ rejBoundedPoly eta s i ∧ rejBoundedPoly eta s i ≤ eta := by
  unfold rejBoundedPoly
  split
  · rename_i h
    obtain ⟨f, hf⟩ := Classical.choose_spec h
    have hst := etaState_complete eta heta s f 0 _ (by simpa using hf) f (by omega)
    have hb := etaState_coeff_bound eta heta s f i
    rw [hst] at hb
    simp only at hb
    by_cases hi : i < 256
    · exact hb.1 hi
    · rw [hb.2 (by omega)]; omega
  · simp

/-! ## The OCaml model versus the ideal bundle -/

theorem encodeVerificationKey_ideal {P : Params} (hP : P.Valid) (rho : Bytes) (t1 : PolyVec)
    (ht : ∀ r < P.k, ∀ i < 256, 0 ≤ t1 r i ∧ t1 r i < 2 ^ 10) :
    encodeVerificationKey (keyOps P) P rho t1 = encodeVerificationKey (keyOpsIdeal P) P rho t1 := by
  unfold encodeVerificationKey concatMap
  rw [List.map_congr_left (fun r hr => (keyOps_refines_pack hP).1 _ (ht r (List.mem_range.mp hr)))]
  simp only [keyOpsIdeal, keyFips]

theorem encodeExpandedSigningKey_ideal {P : Params} (hP : P.Valid) (e : ExpandedKey)
    (hs1 : ∀ r < P.l, ∀ i < 256, -(P.eta : ℤ) ≤ e.s1 r i ∧ e.s1 r i ≤ P.eta)
    (hs2 : ∀ r < P.k, ∀ i < 256, -(P.eta : ℤ) ≤ e.s2 r i ∧ e.s2 r i ≤ P.eta)
    (ht0 : ∀ r < P.k, ∀ i < 256, -(2 ^ 12 : ℤ) < e.t0 r i ∧ e.t0 r i ≤ 2 ^ 12) :
    encodeExpandedSigningKey (keyOps P) P e = encodeExpandedSigningKey (keyOpsIdeal P) P e := by
  have hp := keyOps_refines_pack hP
  unfold encodeExpandedSigningKey concatMap
  rw [List.map_congr_left (fun r hr => hp.2.1 _ (hs1 r (List.mem_range.mp hr))),
    List.map_congr_left (fun r hr => hp.2.1 _ (hs2 r (List.mem_range.mp hr))),
    List.map_congr_left (fun r hr => hp.2.2 _ (ht0 r (List.mem_range.mp hr)))]
  simp only [keyOpsIdeal, keyFips]

/-- `ρ` of `keypair_from_seed ξ`: bytes `0 … 31` of `H(ξ ‖ k ‖ ℓ, 128)`. -/
def seedRho (P : Params) (H : XOF) (xi : Bytes) : Bytes :=
  sub (H.squeeze (xi ++ byteString P.k ++ byteString P.l) 128) 0 32

/-- `ρ′` of `keypair_from_seed ξ`: bytes `32 … 95`. -/
def seedRhoPrime (P : Params) (H : XOF) (xi : Bytes) : Bytes :=
  sub (H.squeeze (xi ++ byteString P.k ++ byteString P.l) 128) 32 64

/-- **On the secrets key generation samples, the OCaml bundle and the ideal
    bundle give the same key.** -/
theorem keypairFromSeed_ideal {P : Params} (hP : P.Valid) (H : XOF)
    (expandMatrix : Bytes → PolyMat) (expandSecret : Bytes → PolyVec × PolyVec) (xi : Bytes)
    (hs1 : ∀ r < P.l, ∀ i < 256, -(P.eta : ℤ) ≤ (expandSecret (seedRhoPrime P H xi)).1 r i ∧
      (expandSecret (seedRhoPrime P H xi)).1 r i ≤ P.eta)
    (hs2 : ∀ r < P.k, ∀ i < 256, -(P.eta : ℤ) ≤ (expandSecret (seedRhoPrime P H xi)).2 r i ∧
      (expandSecret (seedRhoPrime P H xi)).2 r i ≤ P.eta) :
    keypairFromSeed (keyOps P) P H expandMatrix expandSecret xi =
      keypairFromSeed (keyOpsIdeal P) P H expandMatrix expandSecret xi := by
  have hcpp : ∀ m e, computePublicParts (keyOpsIdeal P) m e = computePublicParts (keyOps P) m e :=
    fun m e => by unfold computePublicParts; rfl
  have hr := computePublicParts_range (keyOps P) rfl
  unfold keypairFromSeed
  simp only [hcpp]
  rw [← encodeVerificationKey_ideal hP _ _ (fun r _ i _ => (hr _ _ r i).1)]
  rw [← encodeExpandedSigningKey_ideal hP]
  · exact hs1
  · exact hs2
  · exact fun r _ i _ => (hr _ _ r i).2

/-! ## `keypairFromSeed_eq` with pointwise hypotheses -/

/-- `MLDSAAlg.keypairFromSeed_eq` with the sampler hypotheses only at the two
    seeds `keypair_from_seed ξ` uses, in value form. (Same proof.) -/
theorem keypairFromSeed_eq_at (E : KeyOps) (F : KeyFips) {P : Params} (hP : P.Valid)
    (hR : E.Refines F P) (H G : XOF) (expandMatrix : Bytes → PolyMat)
    (expandSecret : Bytes → PolyVec × PolyVec) (xi : Bytes)
    (hA' : ∀ r < P.k, ∀ s < P.l,
      expandMatrix (seedRho P H xi) r s = expandA G (seedRho P H xi) r s)
    (hS' : (∀ r < P.l, (expandSecret (seedRhoPrime P H xi)).1 r =
        (expandS H P (seedRhoPrime P H xi)).1 r) ∧
      (∀ r < P.k, (expandSecret (seedRhoPrime P H xi)).2 r =
        (expandS H P (seedRhoPrime P H xi)).2 r)) :
    (keypairFromSeed E P H expandMatrix expandSecret xi).verificationKey =
      (keyGenInternal F P H G xi).1 ∧
    (keypairFromSeed E P H expandMatrix expandSecret xi).expandedOctets =
      (keyGenInternal F P H G xi).2 := by
  obtain ⟨-, -, hk, hl, -⟩ := hP.facts
  simp only [seedRho, seedRhoPrime] at hA' hS'
  rw [byteString_eq hk, byteString_eq hl] at hA' hS'
  set out := H.squeeze (xi ++ integerToBytes P.k 1 ++ integerToBytes P.l 1) 128 with hout
  have hlen : out.length = 128 := by simp [hout]
  have hsplit : sub out 96 32 = out.drop 96 := sub_last hlen
  have hpp := computePublicParts_eq E F P hR G (expandMatrix (sub out 0 32))
    { rho := sub out 0 32, key := sub out 96 32, tr := List.replicate 64 0,
      s1 := (expandSecret (sub out 32 64)).1, s2 := (expandSecret (sub out 32 64)).2,
      t0 := fun _ _ => 0 } hA'
  have hpp2 : ∀ r < P.k,
      (publicParts F G (sub out 0 32) (expandSecret (sub out 32 64)).1
        (expandSecret (sub out 32 64)).2).1 r =
        (publicParts F G (sub out 0 32) (expandS H P (sub out 32 64)).1
          (expandS H P (sub out 32 64)).2).1 r ∧
      (publicParts F G (sub out 0 32) (expandSecret (sub out 32 64)).1
        (expandSecret (sub out 32 64)).2).2 r =
        (publicParts F G (sub out 0 32) (expandS H P (sub out 32 64)).1
          (expandS H P (sub out 32 64)).2).2 r := by
    intro r hr
    have hmv := hR.mulMatVec_local (expandA G (sub out 0 32)) (expandA G (sub out 0 32))
      (fun i => F.NTT ((expandSecret (sub out 32 64)).1 i))
      (fun i => F.NTT ((expandS H P (sub out 32 64)).1 i)) (fun _ _ _ _ => rfl)
      (fun s hs => by rw [hS'.1 s hs]) r hr
    unfold publicParts
    simp only [hmv, hS'.2 r hr]
    constructor <;> trivial
  have hvk : ∀ t1 t1' : PolyVec, (∀ r < P.k, t1 r = t1' r) →
      pkEncode F P (sub out 0 32) t1 = pkEncode F P (sub out 0 32) t1' := by
    intro t1 t1' h
    rw [← encodeVerificationKey_eq E F P hR, ← encodeVerificationKey_eq E F P hR]
    unfold encodeVerificationKey
    rw [concatMap_congr h]
  have hsk : ∀ (tr : Bytes) (s1 s2 t0 s1' s2' t0' : PolyVec), (∀ i < P.l, s1 i = s1' i) →
      (∀ i < P.k, s2 i = s2' i) → (∀ i < P.k, t0 i = t0' i) →
      skEncode F P (sub out 0 32) (sub out 96 32) tr s1 s2 t0 =
        skEncode F P (sub out 0 32) (sub out 96 32) tr s1' s2' t0' := by
    intro tr s1 s2 t0 s1' s2' t0' h1 h2 h3
    have e1 := encodeExpandedSigningKey_eq E F P hR
      { rho := sub out 0 32, key := sub out 96 32, tr := tr, s1 := s1, s2 := s2, t0 := t0 }
    have e2 := encodeExpandedSigningKey_eq E F P hR
      { rho := sub out 0 32, key := sub out 96 32, tr := tr, s1 := s1', s2 := s2', t0 := t0' }
    simp only at e1 e2
    rw [← e1, ← e2]
    unfold encodeExpandedSigningKey
    simp only
    rw [concatMap_congr h1, concatMap_congr h2, concatMap_congr h3]
  have hpk : encodeVerificationKey E P (sub out 0 32)
      (computePublicParts E (expandMatrix (sub out 0 32))
        { rho := sub out 0 32, key := sub out 96 32, tr := List.replicate 64 0,
          s1 := (expandSecret (sub out 32 64)).1, s2 := (expandSecret (sub out 32 64)).2,
          t0 := fun _ _ => 0 }).1 =
      pkEncode F P (out.take 32)
        (publicParts F G (out.take 32) (expandS H P ((out.drop 32).take 64)).1
          (expandS H P ((out.drop 32).take 64)).2).1 := by
    rw [encodeVerificationKey_eq E F P hR]
    exact hvk _ _ (fun r hr => ((hpp r hr).1.trans (hpp2 r hr).1))
  refine ⟨?_, ?_⟩
  · simp only [keypairFromSeed, keyGenInternal, byteString_eq hk, byteString_eq hl, ← hout]
    exact hpk
  · simp only [keypairFromSeed, keyGenInternal, byteString_eq hk, byteString_eq hl, ← hout]
    rw [hpk, encodeExpandedSigningKey_eq E F P hR]
    simp only
    rw [← hsplit]
    exact hsk _ _ _ _ _ _ _ (fun i hi => hS'.1 i hi) (fun i hi => hS'.2 i hi)
      (fun r hr => ((hpp r hr).2.trans (hpp2 r hr).2))

/-! ## End to end -/

/-- **Key generation from a seed, end to end (value form).** For a valid
    parameter set, if the matrix and secrets used by the OCaml
    `keypair_from_seed ξ` are `ExpandA(ρ)` (on the `k × ℓ` entries) and
    `ExpandS(ρ′)` (on the `ℓ`/`k` rows), then its verification key and
    signing-key encoding are those of FIPS 204 Algorithm 6
    `ML-DSA.KeyGen_internal(ξ)` with FIPS 202 SHAKE. -/
theorem keypairFromSeed_e2e_values {P : Params} (hP : P.Valid) (expandMatrix : Bytes → PolyMat)
    (expandSecret : Bytes → PolyVec × PolyVec) (xi : Bytes)
    (hA : ∀ r < P.k, ∀ s < P.l, expandMatrix (seedRho P ocamlShake256 xi) r s =
      expandA ocamlShake128 (seedRho P ocamlShake256 xi) r s)
    (hS : (∀ r < P.l, (expandSecret (seedRhoPrime P ocamlShake256 xi)).1 r =
        (expandS ocamlShake256 P (seedRhoPrime P ocamlShake256 xi)).1 r) ∧
      (∀ r < P.k, (expandSecret (seedRhoPrime P ocamlShake256 xi)).2 r =
        (expandS ocamlShake256 P (seedRhoPrime P ocamlShake256 xi)).2 r)) :
    (keypairFromSeed (keyOps P) P ocamlShake256 expandMatrix expandSecret xi).verificationKey =
      (keyGenInternal (keyFips P) P fipsShake256 fipsShake128 xi).1 ∧
    (keypairFromSeed (keyOps P) P ocamlShake256 expandMatrix expandSecret xi).expandedOctets =
      (keyGenInternal (keyFips P) P fipsShake256 fipsShake128 xi).2 := by
  have hf := e2eFacts hP
  rw [keypairFromSeed_ideal hP]
  · rw [fipsShake128_eq, fipsShake256_eq]
    exact keypairFromSeed_eq_at _ _ hP (keyOpsIdeal_refines P) _ _ _ _ xi hA hS
  · intro r hr i _
    rw [hS.1 r hr]
    exact rejBoundedPoly_range hf.eta _ i
  · intro r hr i _
    rw [hS.2 r hr]
    exact rejBoundedPoly_range hf.eta _ i

/-- **Key generation from a seed, end to end.** For a valid parameter set and
    every seed `ξ`: if the OCaml calls `expand_matrix ρ` and
    `expand_secret ρ′` made by `keypair_from_seed ξ` return `A` and
    `(s1, s2)`, then `keypair_from_seed ξ` (OCaml model, with the OCaml
    SHAKE) returns the verification key and signing-key encoding of FIPS 204
    Algorithm 6 `ML-DSA.KeyGen_internal(ξ)` (with FIPS 202 SHAKE128/256). -/
theorem keypairFromSeed_e2e {P : Params} (hP : P.Valid) (xi : Bytes) (A : PolyMat)
    (s1 s2 : PolyVec)
    (hA : ExpandMatrixReturns ocamlShake128 P (seedRho P ocamlShake256 xi) A)
    (hS : ExpandSecretReturns ocamlShake256 P (seedRhoPrime P ocamlShake256 xi) s1 s2) :
    (keypairFromSeed (keyOps P) P ocamlShake256 (fun _ => A) (fun _ => (s1, s2)) xi).verificationKey =
      (keyGenInternal (keyFips P) P fipsShake256 fipsShake128 xi).1 ∧
    (keypairFromSeed (keyOps P) P ocamlShake256 (fun _ => A) (fun _ => (s1, s2)) xi).expandedOctets =
      (keyGenInternal (keyFips P) P fipsShake256 fipsShake128 xi).2 :=
  keypairFromSeed_e2e_values hP _ _ xi ((expandMatrix_spec _ hP _).1 A hA)
    (expandSecret_spec _ hP _ s1 s2 hS)

/-- **Completeness.** If FIPS 204's `ExpandA(ρ)` and `ExpandS(ρ′)` terminate
    (every `RejNTTPoly`/`RejBoundedPoly` call finishes), the OCaml
    `expand_matrix ρ` and `expand_secret ρ′` return `ExpandA(ρ)` and
    `ExpandS(ρ′)`, so `keypairFromSeed_e2e` applies. -/
theorem keypairFromSeed_samplers_return {P : Params} (hP : P.Valid) (xi : Bytes)
    (hA : ∀ r < P.k, ∀ s < P.l, ∃ a, RejNTTPolyReturns
      (ocamlShake128 (seedRho P ocamlShake256 xi ++ integerToBytes s 1 ++ integerToBytes r 1)) a)
    (hS : (∀ r < P.l, ∃ a, RejBoundedReturns P.eta
        (ocamlShake256 (seedRhoPrime P ocamlShake256 xi ++ integerToBytes r 2)) a) ∧
      (∀ r < P.k, ∃ a, RejBoundedReturns P.eta
        (ocamlShake256 (seedRhoPrime P ocamlShake256 xi ++ integerToBytes (r + P.l) 2)) a)) :
    ExpandMatrixReturns ocamlShake128 P (seedRho P ocamlShake256 xi)
        (expandA ocamlShake128 (seedRho P ocamlShake256 xi)) ∧
      ExpandSecretReturns ocamlShake256 P (seedRhoPrime P ocamlShake256 xi)
        (expandS ocamlShake256 P (seedRhoPrime P ocamlShake256 xi)).1
        (expandS ocamlShake256 P (seedRhoPrime P ocamlShake256 xi)).2 :=
  ⟨(expandMatrix_spec _ hP _).2 hA, expandSecret_complete _ hP _ hS⟩

/-- **FIPS 204 Algorithm 1 (`ML-DSA.KeyGen`), end to end.** `generate`
    requests exactly 32 bytes `ξ` from the randomness callback; if it gets
    them (and the sampler calls return `A`, `(s1, s2)`), the returned
    verification key and signing-key encoding are those of
    `ML-DSA.KeyGen_internal(ξ)`, and the key's seed is `ξ`. -/
theorem generate_e2e {P : Params} (hP : P.Valid) (random : ℕ → Bytes) (A : PolyMat)
    (s1 s2 : PolyVec)
    (hA : ExpandMatrixReturns ocamlShake128 P (seedRho P ocamlShake256 (random 32)) A)
    (hS : ExpandSecretReturns ocamlShake256 P (seedRhoPrime P ocamlShake256 (random 32)) s1 s2) :
    (generate (keyOps P) P ocamlShake256 (fun _ => A) (fun _ => (s1, s2)) random).1 = [32] ∧
    ((random 32).length = 32 → ∃ sk pk,
      (generate (keyOps P) P ocamlShake256 (fun _ => A) (fun _ => (s1, s2)) random).2 =
        some (sk, pk) ∧
      pk = (keyGenInternal (keyFips P) P fipsShake256 fipsShake128 (random 32)).1 ∧
      sk.expandedOctets = (keyGenInternal (keyFips P) P fipsShake256 fipsShake128 (random 32)).2 ∧
      signingKeyToSeed sk = some (random 32)) := by
  refine ⟨by unfold generate; dsimp only; split_ifs <;> rfl, fun h => ?_⟩
  have := keypairFromSeed_e2e hP (random 32) A s1 s2 hA hS
  refine ⟨keypairFromSeed (keyOps P) P ocamlShake256 (fun _ => A) (fun _ => (s1, s2)) (random 32),
    (keypairFromSeed (keyOps P) P ocamlShake256 (fun _ => A) (fun _ => (s1, s2))
      (random 32)).verificationKey, by simp [generate, h], this.1, this.2, ?_⟩
  simp [signingKeyToSeed, keypairFromSeed, sub,
    List.take_of_length_le (by omega : (random 32).length ≤ 32)]

end OcamlPq.EndToEnd.MLDSA
