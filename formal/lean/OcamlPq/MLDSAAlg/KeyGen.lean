import OcamlPq.MLDSAAlg.SignLoop

/-!
# Key generation, key import and the seed round trip

Models of `compute_public_parts`, `encode_verification_key`,
`encode_expanded_signing_key`, `equal_string`, `equal_polyvec`,
`build_signing_key`, `keypair_from_seed`, `signing_key_of_seed` and
`signing_key_to_seed` (`mldsa_engine.ml`, lines 469–618), against FIPS 204
Algorithm 6 (`ML-DSA.KeyGen_internal`), Algorithm 22 (`pkEncode`) and
Algorithm 24 (`skEncode`).

The polynomial arithmetic (NTT, `add_mod`, `power2round`) and the bit
packing are verified in other modules; here they are black boxes
(`KeyOps` on the OCaml side, `KeyFips` on the FIPS side) linked by the
hypotheses of `KeyOps.Refines`. What is verified here is the composition:
the domain separator of the seed expansion, the byte slicing of
`H(ξ ‖ k ‖ ℓ, 128)` into `ρ`, `ρ′`, `K`, which seed feeds which expansion,
`tr = H(pk, 64)`, the order of the encodings, and the consistency checks of
key import.
-/

namespace OcamlPq.MLDSAAlg

/-- An OCaml `polyvec` (array of polynomials), indexed by row. -/
abbrev PolyVec := ℕ → Poly
/-- A matrix of polynomials (`polyvec array`), indexed by row and column. -/
abbrev PolyMat := ℕ → ℕ → Poly

/-- `String.concat "" (Array.to_list (Array.map f v))` for an array `v` of
    length `len`. -/
def concatMap (len : ℕ) (f : Poly → Bytes) (v : PolyVec) : Bytes :=
  ((List.range len).map fun i => f (v i)).flatten

/-- The OCaml arithmetic and packing functions used by key generation. -/
structure KeyOps where
  ntt : Poly → Poly
  inverseNtt : Poly → Poly
  matrixVectorNtt : PolyMat → PolyVec → PolyVec
  addMod : ℤ → ℤ → ℤ
  power2round : ℤ → ℤ × ℤ
  packT1 : Poly → Bytes
  packEta : Poly → Bytes
  packT0 : Poly → Bytes

/-- FIPS 204 building blocks used by Algorithm 6. -/
structure KeyFips where
  /-- `NTT` (Algorithm 41). -/
  NTT : Poly → Poly
  /-- `NTT⁻¹` (Algorithm 42). -/
  NTTinv : Poly → Poly
  /-- `Â ∘ v̂` (`MatrixVectorNTT`, Algorithm 48). -/
  mulMatVec : PolyMat → PolyVec → PolyVec
  /-- Addition in `R_q`. -/
  addPoly : Poly → Poly → Poly
  /-- `Power2Round` (Algorithm 35), on one coefficient. -/
  power2Round : ℤ → ℤ × ℤ
  /-- `SimpleBitPack(w, b)` (Algorithm 16). -/
  simpleBitPack : Poly → ℕ → Bytes
  /-- `BitPack(w, a, b)` (Algorithm 17). -/
  bitPack : Poly → ℕ → ℕ → Bytes

/-- The hypotheses (proved in the arithmetic and encoding modules) that the
    OCaml building blocks implement the FIPS ones. `mulMatVec_local` says
    that `Â ∘ v̂` (rows `< k`) only reads entries `Â[r][s]`, `v̂[s]` with
    `r < k`, `s < ℓ`. -/
structure KeyOps.Refines (E : KeyOps) (F : KeyFips) (P : Params) : Prop where
  ntt : E.ntt = F.NTT
  inverseNtt : E.inverseNtt = F.NTTinv
  matrixVectorNtt : E.matrixVectorNtt = F.mulMatVec
  addMod : ∀ a b : Poly, (fun i => E.addMod (a i) (b i)) = F.addPoly a b
  power2round : E.power2round = F.power2Round
  packT1 : ∀ p, E.packT1 p = F.simpleBitPack p (2 ^ (bitlen (q - 1) - d) - 1)
  packEta : ∀ p, E.packEta p = F.bitPack p P.eta P.eta
  packT0 : ∀ p, E.packT0 p = F.bitPack p (2 ^ (d - 1) - 1) (2 ^ (d - 1))
  mulMatVec_local : ∀ (A A' : PolyMat) (v v' : PolyVec),
    (∀ r < P.k, ∀ s < P.l, A r s = A' r s) → (∀ s < P.l, v s = v' s) →
    ∀ r < P.k, F.mulMatVec A v r = F.mulMatVec A' v' r

/-- `expanded_signing_key` (`mldsa_engine.ml`, lines 138–145). -/
structure ExpandedKey where
  rho : Bytes
  key : Bytes
  tr : Bytes
  s1 : PolyVec
  s2 : PolyVec
  t0 : PolyVec

/-- `signing_key` (lines 149–154). -/
structure SigningKey where
  seed : Option Bytes
  expandedOctets : Bytes
  expanded : ExpandedKey
  verificationKey : Bytes

/-! ## Model -/

/-- `compute_public_parts expanded` (lines 531–555); `matrix` is the value
    of `expand_matrix expanded.rho`. `Array.init n f` is modelled by `f`
    (indices `≥ n` are never read). -/
def computePublicParts (E : KeyOps) (matrix : PolyMat) (e : ExpandedKey) : PolyVec × PolyVec :=
  let s1Ntt := fun i => E.ntt (e.s1 i)
  let product := E.matrixVectorNtt matrix s1Ntt
  let t : PolyVec := fun row =>
    let polynomial := E.inverseNtt (product row)
    fun index => E.addMod (polynomial index) (e.s2 row index)
  (fun row index => (E.power2round (t row index)).1,
   fun row index => (E.power2round (t row index)).2)

/-- `encode_verification_key rho t1` (lines 469–470). -/
def encodeVerificationKey (E : KeyOps) (P : Params) (rho : Bytes) (t1 : PolyVec) : Bytes :=
  rho ++ concatMap P.k E.packT1 t1

/-- `encode_expanded_signing_key expanded` (lines 485–491). -/
def encodeExpandedSigningKey (E : KeyOps) (P : Params) (e : ExpandedKey) : Bytes :=
  e.rho ++ e.key ++ e.tr ++ concatMap P.l E.packEta e.s1 ++ concatMap P.k E.packEta e.s2 ++
    concatMap P.k E.packT0 e.t0

/-- `keypair_from_seed seed` (lines 598–616). `expandMatrix` and
    `expandSecret` are the values returned by `expand_matrix` and
    `expand_secret`. -/
def keypairFromSeed (E : KeyOps) (P : Params) (H : XOF) (expandMatrix : Bytes → PolyMat)
    (expandSecret : Bytes → PolyVec × PolyVec) (seed : Bytes) : SigningKey :=
  let expandedSeed := H.squeeze (seed ++ byteString P.k ++ byteString P.l) 128
  let rho := sub expandedSeed 0 32
  let rhoPrime := sub expandedSeed 32 64
  let key := sub expandedSeed 96 32
  let s := expandSecret rhoPrime
  let provisional : ExpandedKey :=
    { rho := rho, key := key, tr := List.replicate 64 0, s1 := s.1, s2 := s.2,
      t0 := fun _ _ => 0 }
  let pp := computePublicParts E (expandMatrix provisional.rho) provisional
  let verificationKey := encodeVerificationKey E P rho pp.1
  let tr := H.squeeze verificationKey 64
  let expanded := { provisional with tr := tr, t0 := pp.2 }
  { seed := some seed, expandedOctets := encodeExpandedSigningKey E P expanded,
    expanded := expanded, verificationKey := verificationKey }

/-! ## Specification -/

/-- FIPS 204 Algorithm 22, `pkEncode(ρ, t1)`. -/
def pkEncode (F : KeyFips) (P : Params) (rho : Bytes) (t1 : PolyVec) : Bytes :=
  (List.range P.k).foldl
    (fun pk i => pk ++ F.simpleBitPack (t1 i) (2 ^ (bitlen (q - 1) - d) - 1)) rho

/-- FIPS 204 Algorithm 24, `skEncode(ρ, K, tr, s1, s2, t0)`. -/
def skEncode (F : KeyFips) (P : Params) (rho K tr : Bytes) (s1 s2 t0 : PolyVec) : Bytes :=
  let sk := rho ++ K ++ tr
  let sk := (List.range P.l).foldl (fun sk i => sk ++ F.bitPack (s1 i) P.eta P.eta) sk
  let sk := (List.range P.k).foldl (fun sk i => sk ++ F.bitPack (s2 i) P.eta P.eta) sk
  (List.range P.k).foldl (fun sk i => sk ++ F.bitPack (t0 i) (2 ^ (d - 1) - 1) (2 ^ (d - 1))) sk

/-- Lines 3–6 of FIPS 204 Algorithm 6: `t ← NTT⁻¹(Â ∘ NTT(s1)) + s2`,
    `(t1, t0) ← Power2Round(t)`, from `ρ`, `s1`, `s2`. -/
noncomputable def publicParts (F : KeyFips) (G : XOF) (rho : Bytes) (s1 s2 : PolyVec) :
    PolyVec × PolyVec :=
  let A := expandA G rho
  let t : PolyVec := fun r => F.addPoly (F.NTTinv (F.mulMatVec A (fun i => F.NTT (s1 i)) r)) (s2 r)
  (fun r i => (F.power2Round (t r i)).1, fun r i => (F.power2Round (t r i)).2)

/-- FIPS 204 Algorithm 6, `ML-DSA.KeyGen_internal(ξ)`, returning `(pk, sk)`;
    `G` is SHAKE128 and `H` SHAKE256. -/
noncomputable def keyGenInternal (F : KeyFips) (P : Params) (H G : XOF) (xi : Bytes) :
    Bytes × Bytes :=
  let out := H.squeeze (xi ++ integerToBytes P.k 1 ++ integerToBytes P.l 1) 128
  let rho := out.take 32
  let rhoPrime := (out.drop 32).take 64
  let K := out.drop 96
  let s := expandS H P rhoPrime
  let pp := publicParts F G rho s.1 s.2
  let pk := pkEncode F P rho pp.1
  let tr := H.squeeze pk 64
  (pk, skEncode F P rho K tr s.1 s.2 pp.2)

/-! ## Encodings -/

theorem foldl_append_eq (len : ℕ) (f : ℕ → Bytes) (acc : Bytes) :
    (List.range len).foldl (fun a i => a ++ f i) acc = acc ++ ((List.range len).map f).flatten := by
  induction len generalizing acc with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp

theorem concatMap_congr {len : ℕ} {f : Poly → Bytes} {v v' : PolyVec} (h : ∀ i < len, v i = v' i) :
    concatMap len f v = concatMap len f v' := by
  unfold concatMap
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

theorem encodeVerificationKey_eq (E : KeyOps) (F : KeyFips) (P : Params) (hR : E.Refines F P)
    (rho : Bytes) (t1 : PolyVec) : encodeVerificationKey E P rho t1 = pkEncode F P rho t1 := by
  unfold encodeVerificationKey pkEncode concatMap
  rw [foldl_append_eq]
  simp [hR.packT1]

theorem encodeExpandedSigningKey_eq (E : KeyOps) (F : KeyFips) (P : Params) (hR : E.Refines F P)
    (e : ExpandedKey) :
    encodeExpandedSigningKey E P e = skEncode F P e.rho e.key e.tr e.s1 e.s2 e.t0 := by
  unfold encodeExpandedSigningKey skEncode concatMap
  simp only [foldl_append_eq, hR.packEta, hR.packT0, List.append_assoc]

/-- `compute_public_parts` computes FIPS 204 Algorithm 6 lines 3–6 on the rows
    `< k`, provided the matrix it uses agrees with `ExpandA(ρ)`. -/
theorem computePublicParts_eq (E : KeyOps) (F : KeyFips) (P : Params) (hR : E.Refines F P)
    (G : XOF) (matrix : PolyMat) (e : ExpandedKey)
    (hA : ∀ r < P.k, ∀ s < P.l, matrix r s = expandA G e.rho r s) :
    ∀ r < P.k, (computePublicParts E matrix e).1 r = (publicParts F G e.rho e.s1 e.s2).1 r ∧
      (computePublicParts E matrix e).2 r = (publicParts F G e.rho e.s1 e.s2).2 r := by
  intro r hr
  have hmv := hR.mulMatVec_local matrix (expandA G e.rho) (fun i => F.NTT (e.s1 i))
    (fun i => F.NTT (e.s1 i)) hA (fun _ _ => rfl) r hr
  unfold computePublicParts publicParts
  simp only [hR.ntt, hR.inverseNtt, hR.matrixVectorNtt, hR.power2round, hmv]
  have hadd := hR.addMod (F.NTTinv (F.mulMatVec (expandA G e.rho) (fun i => F.NTT (e.s1 i)) r))
    (e.s2 r)
  constructor <;> funext i <;> rw [← hadd]

/-! ## Key generation -/

theorem byteString_eq {x : ℕ} (h : x < 256) : byteString x = integerToBytes x 1 :=
  (integerToBytes_one h).symm

theorem sub_last {s : Bytes} (hs : s.length = 128) : sub s 96 32 = s.drop 96 := by
  unfold sub
  apply List.take_of_length_le
  simp [hs]

/-- **Obligation 5 (KeyGen).** For every seed `ξ`, `keypair_from_seed ξ`
    produces the verification key `pk` and the signing-key encoding `sk` of
    FIPS 204 Algorithm 6 `ML-DSA.KeyGen_internal(ξ)`, provided the OCaml
    building blocks refine the FIPS ones and `expand_matrix`/`expand_secret`
    return (their returned values are then `ExpandA`/`ExpandS` by
    `expandMatrix_spec`/`expandSecret_spec`). -/
theorem keypairFromSeed_eq (E : KeyOps) (F : KeyFips) {P : Params} (hP : P.Valid)
    (hR : E.Refines F P) (H G : XOF) (expandMatrix : Bytes → PolyMat)
    (expandSecret : Bytes → PolyVec × PolyVec)
    (hA : ∀ rho, ExpandMatrixReturns G P rho (expandMatrix rho))
    (hS : ∀ rho', ExpandSecretReturns H P rho' (expandSecret rho').1 (expandSecret rho').2)
    (xi : Bytes) :
    (keypairFromSeed E P H expandMatrix expandSecret xi).verificationKey =
      (keyGenInternal F P H G xi).1 ∧
    (keypairFromSeed E P H expandMatrix expandSecret xi).expandedOctets =
      (keyGenInternal F P H G xi).2 := by
  obtain ⟨-, -, hk, hl, -⟩ := hP.facts
  set out := H.squeeze (xi ++ integerToBytes P.k 1 ++ integerToBytes P.l 1) 128 with hout
  have hlen : out.length = 128 := by simp [hout]
  have hsplit : sub out 96 32 = out.drop 96 := sub_last hlen
  have hS' := expandSecret_spec H hP _ _ _ (hS (sub out 32 64))
  have hA' := (expandMatrix_spec G hP (sub out 0 32)).1 _ (hA (sub out 0 32))
  -- the public parts agree on all rows < k
  have hpp := computePublicParts_eq E F P hR G (expandMatrix (sub out 0 32))
    { rho := sub out 0 32, key := sub out 96 32, tr := List.replicate 64 0,
      s1 := (expandSecret (sub out 32 64)).1, s2 := (expandSecret (sub out 32 64)).2,
      t0 := fun _ _ => 0 } hA'
  -- publicParts only reads s1 at indices < ℓ and s2 at rows < k
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

/-! ## Constant-time comparisons -/

/-- `equal_string left right` (lines 557–564). -/
def equalString (left right : Bytes) : Bool :=
  if left.length ≠ right.length then false
  else (List.range left.length).foldl
    (fun difference index => difference ||| (getU8 left index ^^^ getU8 right index)) 0 = 0

theorem foldl_or_eq_zero (len : ℕ) (f : ℕ → ℕ) (acc : ℕ) :
    (List.range len).foldl (fun a i => a ||| f i) acc = 0 ↔ acc = 0 ∧ ∀ i < len, f i = 0 := by
  induction len generalizing acc with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    constructor
    · intro h
      rw [Nat.or_eq_zero_iff] at h
      obtain ⟨h1, h2⟩ := (ih acc).mp h.1
      exact ⟨h1, fun i hi => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h2 i hi
        · exact h.2⟩
    · rintro ⟨h1, h2⟩
      rw [Nat.or_eq_zero_iff]
      exact ⟨(ih acc).mpr ⟨h1, fun i hi => h2 i (by omega)⟩, h2 m (by omega)⟩

/-- `equal_string` decides equality of byte strings. -/
theorem equalString_iff (left right : Bytes) : equalString left right = true ↔ left = right := by
  unfold equalString
  split_ifs with hl
  · simp only [false_iff]
    rintro rfl; exact hl rfl
  · rw [decide_eq_true_iff, foldl_or_eq_zero]
    simp only [true_and, Nat.xor_eq_zero_iff]
    constructor
    · intro h
      apply List.ext_getElem (by omega)
      intro i h1 h2
      have := h i h1
      unfold getU8 at this
      rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
      exact Fin.ext this
    · rintro rfl; intro i _; rfl

/-- `equal_polyvec left right` (lines 566–575) for `int` of width `w`
    (two's complement `lxor`/`lor` on `BitVec w`); `lenL`, `lenR` are the
    array lengths. -/
def equalPolyvec (w lenL lenR : ℕ) (left right : PolyVec) : Bool :=
  lenL = lenR &&
    (List.range lenL).foldl (fun difference row =>
      (List.range n).foldl (fun difference index =>
        difference ||| (BitVec.ofInt w (left row index) ^^^ BitVec.ofInt w (right row index)))
        difference) 0 = 0

theorem bv_or_eq_zero_iff {w : ℕ} (a b : BitVec w) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [BitVec.toNat_eq, BitVec.toNat_eq, BitVec.toNat_eq, BitVec.toNat_or]
  exact Nat.or_eq_zero_iff

theorem foldl_bv_or_eq_zero {w : ℕ} (len : ℕ) (f : ℕ → BitVec w) (acc : BitVec w) :
    (List.range len).foldl (fun a i => a ||| f i) acc = 0 ↔ acc = 0 ∧ ∀ i < len, f i = 0 := by
  induction len generalizing acc with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [bv_or_eq_zero_iff, ih]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, fun i hi => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h2 i hi
        · exact h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun i hi => h2 i (by omega)⟩, h2 m (by omega)⟩

theorem foldl_bv_or_eq_zero2 {w : ℕ} (len₁ len₂ : ℕ) (f : ℕ → ℕ → BitVec w) (acc : BitVec w) :
    (List.range len₁).foldl (fun a r => (List.range len₂).foldl (fun a i => a ||| f r i) a) acc = 0 ↔
      acc = 0 ∧ ∀ r < len₁, ∀ i < len₂, f r i = 0 := by
  induction len₁ generalizing acc with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_bv_or_eq_zero, ih]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, fun r hr => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
        · exact h2 r hr
        · exact h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun r hr => h2 r (by omega)⟩, h2 m (by omega)⟩

/-- Two portable integers have equal `w`-bit representations (`w ≥ 31`) iff
    they are equal. -/
theorem ofInt_inj_portable {w : ℕ} (hw : 31 ≤ w) {a b : ℤ} (ha : Portable a) (hb : Portable b) :
    BitVec.ofInt w a = BitVec.ofInt w b ↔ a = b := by
  constructor
  · intro h
    have h' := congrArg BitVec.toInt h
    rw [BitVec.toInt_ofInt, BitVec.toInt_ofInt] at h'
    have hp : (2 : ℤ) ^ 30 ≤ 2 ^ (w - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hw' : ((2 : ℕ) ^ w : ℕ) = (2 : ℤ) * 2 ^ (w - 1) := by
      push_cast; rw [← pow_succ']; congr 1; omega
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    have hm2 : (((2 : ℕ) ^ w : ℕ) : ℤ) / 2 = 2 ^ (w - 1) := by rw [hw']; omega
    have hm3 : ((((2 : ℕ) ^ w : ℕ) : ℤ) + 1) / 2 = 2 ^ (w - 1) := by rw [hw']; omega
    rw [Int.bmod_eq_of_le (by rw [hm2]; omega) (by rw [hm3]; omega),
      Int.bmod_eq_of_le (by rw [hm2]; omega) (by rw [hm3]; omega)] at h'
    exact h'
  · rintro rfl; rfl

/-- `equal_polyvec` decides equality of the first `lenL` rows (coefficients
    `< 256`) when all entries are `Portable` and the `int` width is `≥ 31`. -/
theorem equalPolyvec_iff {w : ℕ} (hw : 31 ≤ w) (len : ℕ) (left right : PolyVec)
    (hl : ∀ r < len, ∀ i < n, Portable (left r i)) (hr : ∀ r < len, ∀ i < n, Portable (right r i)) :
    equalPolyvec w len len left right = true ↔ ∀ r < len, ∀ i < n, left r i = right r i := by
  unfold equalPolyvec
  simp only [decide_true, Bool.true_and, decide_eq_true_eq]
  rw [foldl_bv_or_eq_zero2]
  simp only [true_and, xor_eq_zero_iff]
  constructor
  · intro h r hr' i hi; exact (ofInt_inj_portable hw (hl r hr' i hi) (hr r hr' i hi)).mp (h r hr' i hi)
  · intro h r hr' i hi; rw [h r hr' i hi]

/-! ## Key import -/

/-- `build_signing_key ?seed expanded` (lines 577–590), on a platform whose
    `int` has `w` bits; `matrix` is the value of `expand_matrix
    expanded.rho`. -/
def buildSigningKey (E : KeyOps) (P : Params) (H : XOF) (w : ℕ) (matrix : PolyMat)
    (seed : Option Bytes) (e : ExpandedKey) : Except MLDSAError SigningKey :=
  let pp := computePublicParts E matrix e
  let verificationKey := encodeVerificationKey E P e.rho pp.1
  let expectedTr := H.squeeze verificationKey 64
  if !equalString e.tr expectedTr then
    .error (.invalidEncoding "ML-DSA signing key has an inconsistent public-key hash")
  else if !equalPolyvec w P.k P.k e.t0 pp.2 then
    .error (.invalidEncoding "ML-DSA signing key has an inconsistent t0 vector")
  else
    .ok { seed := seed, expandedOctets := encodeExpandedSigningKey E P e, expanded := e,
          verificationKey := verificationKey }

/-- The expanded key that the key-generation computation (FIPS 204
    Algorithm 6, lines 3–10) derives from `(ρ, K, s1, s2)`. -/
noncomputable def deriveExpanded (F : KeyFips) (P : Params) (H G : XOF) (rho K : Bytes)
    (s1 s2 : PolyVec) : ExpandedKey :=
  let pp := publicParts F G rho s1 s2
  { rho := rho, key := K, tr := H.squeeze (pkEncode F P rho pp.1) 64, s1 := s1, s2 := s2,
    t0 := pp.2 }

/-- **Obligation 8.** `build_signing_key` accepts an expanded key exactly when
    its `tr` and `t0` are the ones key generation derives from its
    `(ρ, K, s1, s2)` (Algorithm 6 lines 3–10: `tr = H(pkEncode(ρ, t1), 64)`,
    `t0` = low part of `Power2Round(NTT⁻¹(Â ∘ NTT(s1)) + s2)`), on rows
    `< k` and coefficients `< 256`. Preconditions: the building blocks refine
    FIPS, `expand_matrix` returned `matrix`, `int` has at least 31 bits, and
    the stored and recomputed `t0` coefficients are `Portable` (both lie in
    `[−4095, 4096]`). It then returns the key with the given seed, the
    re-encoded octets and the recomputed verification key. -/
theorem buildSigningKey_ok_iff (E : KeyOps) (F : KeyFips) {P : Params} (hR : E.Refines F P)
    (H G : XOF) {w : ℕ} (hw : 31 ≤ w) (matrix : PolyMat) (seed : Option Bytes) (e : ExpandedKey)
    (hA : ExpandMatrixReturns G P e.rho matrix) (hP : P.Valid)
    (hport : ∀ r < P.k, ∀ i < n, Portable (e.t0 r i) ∧
      Portable ((publicParts F G e.rho e.s1 e.s2).2 r i)) :
    (∃ key, buildSigningKey E P H w matrix seed e = .ok key) ↔
      (e.tr = (deriveExpanded F P H G e.rho e.key e.s1 e.s2).tr ∧
        ∀ r < P.k, ∀ i < n, e.t0 r i = (deriveExpanded F P H G e.rho e.key e.s1 e.s2).t0 r i) := by
  have hA' := (expandMatrix_spec G hP e.rho).1 matrix hA
  have hpp := computePublicParts_eq E F P hR G matrix e hA'
  have hvk : encodeVerificationKey E P e.rho (computePublicParts E matrix e).1 =
      pkEncode F P e.rho (publicParts F G e.rho e.s1 e.s2).1 := by
    rw [encodeVerificationKey_eq E F P hR]
    unfold pkEncode
    rw [foldl_append_eq, foldl_append_eq]
    congr 2
    apply List.map_congr_left
    intro r hr
    rw [(hpp r (List.mem_range.mp hr)).1]
  have ht0 : equalPolyvec w P.k P.k e.t0 (computePublicParts E matrix e).2 = true ↔
      ∀ r < P.k, ∀ i < n, e.t0 r i = (publicParts F G e.rho e.s1 e.s2).2 r i := by
    rw [equalPolyvec_iff hw]
    · constructor
      · intro h r hr i hi; rw [h r hr i hi, (hpp r hr).2]
      · intro h r hr i hi; rw [h r hr i hi, (hpp r hr).2]
    · exact fun r hr i hi => (hport r hr i hi).1
    · exact fun r hr i hi => by rw [(hpp r hr).2]; exact (hport r hr i hi).2
  unfold buildSigningKey deriveExpanded
  simp only [hvk]
  by_cases h1 : equalString e.tr (H.squeeze (pkEncode F P e.rho (publicParts F G e.rho e.s1 e.s2).1) 64) = true
  · by_cases h2 : equalPolyvec w P.k P.k e.t0 (computePublicParts E matrix e).2 = true
    · simp only [h1, h2, Bool.not_true, Bool.false_eq_true, ite_false]
      exact ⟨fun _ => ⟨(equalString_iff _ _).mp h1, ht0.mp h2⟩, fun _ => ⟨_, rfl⟩⟩
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [Bool.not_eq_true] at h2
      simp only [h2, Bool.not_false, ite_true]
      constructor
      · rintro ⟨_, h⟩; cases h
      · rintro ⟨_, h⟩; rw [← ht0] at h; rw [h] at h2; cases h2
  · rw [Bool.not_eq_true] at h1
    simp only [h1, Bool.not_false, ite_true]
    constructor
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨h, _⟩; rw [← equalString_iff] at h; rw [h] at h1; cases h1

/-! ## Seeds -/

/-- `signing_key_of_seed seed` (lines 618–621). -/
def signingKeyOfSeed (E : KeyOps) (P : Params) (H : XOF) (expandMatrix : Bytes → PolyMat)
    (expandSecret : Bytes → PolyVec × PolyVec) (seed : Bytes) : Except MLDSAError SigningKey :=
  if seed.length ≠ 32 then .error (.invalidLength "ML-DSA seed" 32 seed.length)
  else .ok (keypairFromSeed E P H expandMatrix expandSecret seed)

/-- `signing_key_to_seed key` (line 623). -/
def signingKeyToSeed (key : SigningKey) : Option Bytes := key.seed.map fun seed => sub seed 0 32

/-- **Obligation 8 (seed round trip).** `signing_key_to_seed (signing_key_of_seed
    s) = Some s` for every 32-byte `s`, and `signing_key_of_seed` rejects
    every other length. -/
theorem seed_roundtrip (E : KeyOps) (P : Params) (H : XOF) (expandMatrix : Bytes → PolyMat)
    (expandSecret : Bytes → PolyVec × PolyVec) (seed : Bytes) :
    (seed.length = 32 → ∃ key, signingKeyOfSeed E P H expandMatrix expandSecret seed = .ok key ∧
        signingKeyToSeed key = some seed) ∧
    (seed.length ≠ 32 → signingKeyOfSeed E P H expandMatrix expandSecret seed =
        .error (.invalidLength "ML-DSA seed" 32 seed.length)) := by
  constructor
  · intro h
    refine ⟨keypairFromSeed E P H expandMatrix expandSecret seed, by simp [signingKeyOfSeed, h], ?_⟩
    simp [signingKeyToSeed, keypairFromSeed, sub, List.take_of_length_le (by omega : seed.length ≤ 32)]
  · intro h; simp [signingKeyOfSeed, h]

/-- `generate ~random ()` (lines 833–836) with `require_random`
    (lines 824–831): the lengths requested from the callback, and `none` if
    `require_random` raises `Invalid_argument`. -/
def generate (E : KeyOps) (P : Params) (H : XOF) (expandMatrix : Bytes → PolyMat)
    (expandSecret : Bytes → PolyVec × PolyVec) (random : ℕ → Bytes) :
    List ℕ × Option (SigningKey × Bytes) :=
  let seed := random 32
  if seed.length ≠ 32 then ([32], none)
  else
    let signingKey := keypairFromSeed E P H expandMatrix expandSecret seed
    ([32], some (signingKey, signingKey.verificationKey))

/-- **FIPS 204 Algorithm 1 (`ML-DSA.KeyGen`).** `generate` requests exactly
    32 bytes `ξ` from the randomness source; if it gets them, the returned
    verification key and signing-key encoding are those of
    `ML-DSA.KeyGen_internal(ξ)`, and the key remembers `ξ` as its seed. -/
theorem generate_eq (E : KeyOps) (F : KeyFips) {P : Params} (hP : P.Valid)
    (hR : E.Refines F P) (H G : XOF) (expandMatrix : Bytes → PolyMat)
    (expandSecret : Bytes → PolyVec × PolyVec)
    (hA : ∀ rho, ExpandMatrixReturns G P rho (expandMatrix rho))
    (hS : ∀ rho', ExpandSecretReturns H P rho' (expandSecret rho').1 (expandSecret rho').2)
    (random : ℕ → Bytes) :
    (generate E P H expandMatrix expandSecret random).1 = [32] ∧
    ((random 32).length = 32 → ∃ sk pk,
      (generate E P H expandMatrix expandSecret random).2 = some (sk, pk) ∧
      pk = (keyGenInternal F P H G (random 32)).1 ∧
      sk.expandedOctets = (keyGenInternal F P H G (random 32)).2 ∧
      signingKeyToSeed sk = some (random 32)) := by
  refine ⟨by unfold generate; dsimp only; split_ifs <;> rfl, fun h => ?_⟩
  have := keypairFromSeed_eq E F hP hR H G expandMatrix expandSecret hA hS (random 32)
  refine ⟨keypairFromSeed E P H expandMatrix expandSecret (random 32),
    (keypairFromSeed E P H expandMatrix expandSecret (random 32)).verificationKey,
    by simp [generate, h], this.1, this.2, ?_⟩
  simp [signingKeyToSeed, keypairFromSeed, sub, List.take_of_length_le (by omega : (random 32).length ≤ 32)]

/-- Keys imported from octets carry no seed. -/
theorem buildSigningKey_no_seed (E : KeyOps) (P : Params) (H : XOF) (w : ℕ) (matrix : PolyMat)
    (e : ExpandedKey) (key : SigningKey) (h : buildSigningKey E P H w matrix none e = .ok key) :
    signingKeyToSeed key = none := by
  unfold buildSigningKey at h
  simp only at h
  split_ifs at h
  cases h; rfl

end OcamlPq.MLDSAAlg
