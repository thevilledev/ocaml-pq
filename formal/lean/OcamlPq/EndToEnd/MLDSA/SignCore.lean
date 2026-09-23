import OcamlPq.EndToEnd.MLDSA.KeyGen

/-!
# One signing candidate: the OCaml body versus FIPS 204 Algorithm 7

`MLDSAAlg.SignOps.candidate y w0 w1 ĉ` is lines 747–797 of
`sign_mu_with_randomness` (the key's `s1_ntt`, `s2_ntt`, `t0_ntt` fixed), and
`SignFips.finish y w ĉ` is Algorithm 7 lines 15–30. This file defines both
concretely:

* `ocamlCandidate P key`: `cs1`, `cs2`, `ct0` as
  `Array.map center (inverse_ntt (pointwise ĉ (ntt s)))` (arithmetic area's
  models), `z = y + cs1`, and `codeTail`, a literal transcription of lines
  766–798 over `(w0, w1, cs2, ct0)` (the code's shortcuts: `r0 = center (w0 −
  cs2)`, hint `make_hint (center (r0 + ct0)) w1`, all four flags ORed);
* `fipsFinish P key`: `⟨⟨c·s⟩⟩ = NTT⁻¹(ĉ ∘ NTT(s))` (FIPS transcriptions),
  `z = y + ⟨⟨cs1⟩⟩`, the arithmetic area's `signAttemptSpec` (Algorithm 7 lines
  17–29: `r0 = LowBits(w − cs2)`, the norm checks, `MakeHint(−ct0, w − cs2 +
  ct0)`, the hint count), returning `(z mod± q, h)` as line 33 encodes it.

`ocamlCandidate_eq_fipsFinish` proves them equal, for the `w0, w1` of
`Decompose(w)`, discharging the side conditions of the arithmetic area's
`signAttempt_eq_spec` (`‖cs2‖∞ ≤ β`) with `center_cs` from the challenge's
shape (`sampleInBall_output`) and `s2 ∈ [−η, η]`, and relating the code's
centered `cs1`, `cs2`, `ct0` to FIPS's canonical ones modulo `q`. The
equality needs `y ∈ (−γ1, γ1]` (so `z = y + cs1` is its own `mod±`
representative) and a challenge of FIPS shape: `SignOps.Refines.candidate_eq`
quantifies over *all* `y` and `ĉ`, where it is false.
-/

namespace OcamlPq.EndToEnd.MLDSA

open OcamlPq.MLDSAAlg

/-! ## Rows as lists -/

/-- `k` rows of 256 entries of an index function, as lists (an OCaml
    `'a array array` with `k` rows of `n = 256`). -/
def mkRows {α : Type} (k : ℕ) (f : ℕ → ℕ → α) : List (List α) :=
  (List.range k).map fun r => (List.range 256).map (f r)

theorem vecToLists_eq_mkRows (k : ℕ) (v : PolyVec) : vecToLists k v = mkRows k v := rfl

theorem mkRows_map {α β : Type} (k : ℕ) (f : ℕ → ℕ → α) (g : α → β) :
    (mkRows k f).map (List.map g) = mkRows k fun r i => g (f r i) := by
  simp [mkRows, List.map_map, Function.comp_def]

theorem mkRows_congr {α : Type} {k : ℕ} {f f' : ℕ → ℕ → α}
    (h : ∀ r < k, ∀ i < 256, f r i = f' r i) : mkRows k f = mkRows k f' := by
  unfold mkRows
  apply List.map_congr_left
  intro r hr
  apply List.map_congr_left
  intro i hi
  exact h r (List.mem_range.mp hr) i (List.mem_range.mp hi)

theorem mem_mkRows {α : Type} {k : ℕ} {f : ℕ → ℕ → α} {p : List α} :
    p ∈ mkRows k f ↔ ∃ r < k, (List.range 256).map (f r) = p := by
  simp [mkRows]

theorem infNormGe_mkRows (k : ℕ) (f : ℕ → ℕ → ℤ) (b : ℤ) :
    MLDSA.infNormGe (mkRows k f) b ↔ ∃ r < k, ∃ i < 256, MLDSA.coeffNorm (f r i) ≥ b :=
  infNormGe_vecToLists k f b

theorem listsToVec_mkRows (k : ℕ) (f : ℕ → ℕ → ℤ) (r i : ℕ) (hr : r < k) (hi : i < 256) :
    listsToVec (mkRows k f) r i = f r i := by
  simp [listsToVec, mkRows, listToPoly, List.getD_eq_getElem?_getD, hr, hi]

theorem listsToVec_mkRows_trunc (k : ℕ) (f : ℕ → ℕ → ℤ) (r i : ℕ) :
    listsToVec (mkRows k f) r i = if r < k ∧ i < 256 then f r i else 0 := by
  by_cases h : r < k ∧ i < 256
  · rw [ite_eq_left h, listsToVec_mkRows k f r i h.1 h.2]
  · rw [ite_eq_right h]
    by_cases hr : r < k
    · simp [listsToVec, mkRows, listToPoly, List.getD_eq_getElem?_getD, hr, show ¬ i < 256 by tauto]
    · simp [listsToVec, mkRows, listToPoly, List.getD_eq_getElem?_getD, hr]

theorem sum_mkRows (k : ℕ) (f : ℕ → ℕ → ℤ) :
    ((mkRows k f).map List.sum).sum = ((vecToLists k (listsToVec (mkRows k f))).map List.sum).sum := by
  rw [vecToLists_eq_mkRows]
  congr 2
  exact mkRows_congr fun r hr i hi => (listsToVec_mkRows k f r i hr hi).symm

/-! ## Residues -/

theorem coeffNorm_congr {x y : ℤ} (h : x % MLDSA.q = y % MLDSA.q) :
    MLDSA.coeffNorm x = MLDSA.coeffNorm y := by
  unfold MLDSA.coeffNorm MLDSA.modPM; rw [h]

theorem modPM_congr {x y : ℤ} (h : x % MLDSA.q = y % MLDSA.q) :
    MLDSA.modPM x MLDSA.q = MLDSA.modPM y MLDSA.q := by
  unfold MLDSA.modPM; rw [h]

/-- `signAttemptSpec` (Algorithm 7 lines 17–29) only depends on its inputs
    modulo `q`, except that it returns its `z` input unchanged. -/
theorem signAttemptSpec_congr (γ1 γ2 β ω : ℤ) (l k : ℕ) (z z' w w' cs cs' ct ct' : ℕ → ℕ → ℤ)
    (hz : ∀ r < l, ∀ i < 256, z r i % MLDSA.q = z' r i % MLDSA.q)
    (hw : ∀ r < k, ∀ i < 256, w r i % MLDSA.q = w' r i % MLDSA.q)
    (hcs : ∀ r < k, ∀ i < 256, cs r i % MLDSA.q = cs' r i % MLDSA.q)
    (hct : ∀ r < k, ∀ i < 256, ct r i % MLDSA.q = ct' r i % MLDSA.q) :
    MLDSA.signAttemptSpec γ1 γ2 β ω (mkRows l z) (mkRows k fun r i => (w r i, cs r i, ct r i)) =
      (MLDSA.signAttemptSpec γ1 γ2 β ω (mkRows l z')
        (mkRows k fun r i => (w' r i, cs' r i, ct' r i))).map fun zh => (mkRows l z, zh.2) := by
  have e1 : MLDSA.infNormGe (mkRows l z) (γ1 - β) ↔ MLDSA.infNormGe (mkRows l z') (γ1 - β) := by
    rw [infNormGe_mkRows, infNormGe_mkRows]
    constructor <;> rintro ⟨r, hr, i, hi, h⟩ <;> refine ⟨r, hr, i, hi, ?_⟩
    · rwa [← coeffNorm_congr (hz r hr i hi)]
    · rwa [coeffNorm_congr (hz r hr i hi)]
  have hwc : ∀ r < k, ∀ i < 256, (w r i - cs r i) % MLDSA.q = (w' r i - cs' r i) % MLDSA.q := by
    intro r hr i hi
    rw [Int.sub_emod, hw r hr i hi, hcs r hr i hi, ← Int.sub_emod]
  have e2 : MLDSA.infNormGe (mkRows k fun r i => MLDSA.lowBits γ2 (w r i - cs r i)) (γ2 - β) ↔
      MLDSA.infNormGe (mkRows k fun r i => MLDSA.lowBits γ2 (w' r i - cs' r i)) (γ2 - β) := by
    rw [infNormGe_mkRows, infNormGe_mkRows]
    constructor <;> rintro ⟨r, hr, i, hi, h⟩ <;> refine ⟨r, hr, i, hi, ?_⟩
    · rwa [← MLDSA.lowBits_congr γ2 (hwc r hr i hi)]
    · rwa [MLDSA.lowBits_congr γ2 (hwc r hr i hi)]
  have e3 : MLDSA.infNormGe (mkRows k ct) γ2 ↔ MLDSA.infNormGe (mkRows k ct') γ2 := by
    rw [infNormGe_mkRows, infNormGe_mkRows]
    constructor <;> rintro ⟨r, hr, i, hi, h⟩ <;> refine ⟨r, hr, i, hi, ?_⟩
    · rwa [← coeffNorm_congr (hct r hr i hi)]
    · rwa [coeffNorm_congr (hct r hr i hi)]
  have e4 : (mkRows k fun r i => MLDSA.makeHintSpec γ2 (-ct r i) (w r i - cs r i + ct r i)) =
      mkRows k fun r i => MLDSA.makeHintSpec γ2 (-ct' r i) (w' r i - cs' r i + ct' r i) := by
    apply mkRows_congr
    intro r hr i hi
    apply MLDSA.makeHintSpec_congr
    · exact Int.ModEq.neg (hct r hr i hi)
    · exact Int.ModEq.add (hwc r hr i hi) (hct r hr i hi)
  unfold MLDSA.signAttemptSpec
  simp only [mkRows_map]
  by_cases c12 : MLDSA.infNormGe (mkRows l z') (γ1 - β) ∨
      MLDSA.infNormGe (mkRows k fun r i => MLDSA.lowBits γ2 (w' r i - cs' r i)) (γ2 - β)
  · rw [ite_eq_left c12, ite_eq_left (by rwa [e1, e2])]; rfl
  · rw [ite_eq_right c12, ite_eq_right (by rwa [e1, e2]), e4]
    by_cases c34 : MLDSA.infNormGe (mkRows k ct') γ2 ∨
        ((mkRows k fun r i => MLDSA.makeHintSpec γ2 (-ct' r i) (w' r i - cs' r i + ct' r i)).map
          fun row => row.sum).sum > ω
    · rw [ite_eq_left c34, ite_eq_left (by rwa [e3])]; rfl
    · rw [ite_eq_right c34, ite_eq_right (by rwa [e3])]; rfl

/-- `signAttemptSpec` returns its `z` input. -/
theorem signAttemptSpec_fst (γ1 γ2 β ω : ℤ) (l k : ℕ) (z w cs ct : ℕ → ℕ → ℤ) :
    MLDSA.signAttemptSpec γ1 γ2 β ω (mkRows l z) (mkRows k fun r i => (w r i, cs r i, ct r i)) =
      (MLDSA.signAttemptSpec γ1 γ2 β ω (mkRows l z)
        (mkRows k fun r i => (w r i, cs r i, ct r i))).map fun zh => (mkRows l z, zh.2) :=
  signAttemptSpec_congr γ1 γ2 β ω l k z z w w cs cs ct ct (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

/-! ## The OCaml candidate -/

/-- One row of `cs1`, `cs2` or `ct0` in the code:
    `Array.map center (inverse_ntt (pointwise challenge_ntt v_ntt))`
    (lines 755–759, 767–771, 778–782). -/
def ocamlCenteredProduct (cHat vHat : Poly) : Poly :=
  fun i => MLDSA.center (MLDSA.inverseNtt (MLDSA.pointwise cHat vHat) i)

/-- Lines 766–798 of `sign_mu_with_randomness`, from `z` on: the four
    rejection flags (`vector_norm_violation_flag` on `z`, `r0 = center (w0 −
    cs2)` and `ct0`, and `hint_count > ω`) ORed together, and the hints
    `make_hint (center (r0 + ct0)) w1`. Each row entry is
    `(w0, w1, cs2, ct0)`. -/
def codeTail (γ1 γ2 β ω : ℤ) (z : List (List ℤ)) (rows : List (List (ℤ × ℤ × ℤ × ℤ))) :
    Option (List (List ℤ) × List (List ℤ)) :=
  let rejection := MLDSA.vectorNormViolationFlag z (γ1 - β)
  let r0 := rows.map (List.map fun e => MLDSA.center (e.1 - e.2.2.1))
  let rejection := rejection ||| MLDSA.vectorNormViolationFlag r0 (γ2 - β)
  let ct0 := rows.map (List.map fun e => e.2.2.2)
  let rejection := rejection ||| MLDSA.vectorNormViolationFlag ct0 γ2
  let hints := rows.map (List.map fun e =>
    MLDSA.makeHint γ2 (MLDSA.center (MLDSA.center (e.1 - e.2.2.1) + e.2.2.2)) e.2.1)
  let hintCount := (hints.map fun row => row.foldl (· + ·) 0).foldl (· + ·) 0
  let tooManyHints := if hintCount > ω then 1 else 0
  let rejection := rejection ||| tooManyHints
  if rejection ≠ 0 then none else some (z, hints)

/-- **The OCaml candidate** (`SignOps.candidate`): lines 747–797 of
    `sign_mu_with_randomness` for the key `key` (`s1_ntt = Array.map ntt
    key.s1`, …), on the mask `y`, `(w1, w0) = decompose w` and the challenge
    `ĉ`. Returns `Some (z, hints)` for `Ok (encode_signature c̃ z hints)` and
    `none` when `!rejection <> 0`. -/
def ocamlCandidate (P : Params) (key : ExpandedKey) (y w0 w1 : PolyVec) (cHat : Poly) :
    Option (PolyVec × PolyVec) :=
  let cs1 : PolyVec := fun r => ocamlCenteredProduct cHat (MLDSA.ntt (key.s1 r))
  let z := mkRows P.l fun r i => y r i + cs1 r i
  let cs2 : PolyVec := fun r => ocamlCenteredProduct cHat (MLDSA.ntt (key.s2 r))
  let ct0 : PolyVec := fun r => ocamlCenteredProduct cHat (MLDSA.ntt (key.t0 r))
  let rows := mkRows P.k fun r i => (w0 r i, w1 r i, cs2 r i, ct0 r i)
  (codeTail P.gamma1 P.gamma2 P.beta P.omega z rows).map fun zh => (listsToVec zh.1, listsToVec zh.2)

/-- With `(w1, w0) = decompose w`, `codeTail` is the arithmetic area's
    `signAttempt` on the `(w, cs2, ct0)` triples. -/
theorem codeTail_eq_signAttempt (γ1 γ2 β ω : ℤ) (z : List (List ℤ)) (k : ℕ)
    (w cs ct : ℕ → ℕ → ℤ) :
    codeTail γ1 γ2 β ω z (mkRows k fun r i =>
        ((MLDSA.decompose γ2 (w r i)).2, (MLDSA.decompose γ2 (w r i)).1, cs r i, ct r i)) =
      MLDSA.signAttempt γ1 γ2 β ω z (mkRows k fun r i => (w r i, cs r i, ct r i)) := by
  unfold codeTail MLDSA.signAttempt
  simp only [mkRows_map, MLDSA.codeR0, MLDSA.codeHint]

/-! ## FIPS 204 Algorithm 7, lines 15–30 -/

/-- `⟨⟨c·v⟩⟩ = NTT⁻¹(ĉ ∘ v̂)` (Algorithm 7 lines 16, 17, 22; Algorithms 42,
    45). -/
def fipsProduct (cHat vHat : Poly) : Poly := fipsNTTinv (fipsMulNTT cHat vHat)

/-- **FIPS 204 Algorithm 7, lines 15–30 (and the `z mod± q` of line 33)**
    for the decoded key `key` (`ŝ1 = NTT(s1)`, `ŝ2 = NTT(s2)`, `t̂0 = NTT(t0)`,
    line 5): `z ← y + ⟨⟨cs1⟩⟩`, then the arithmetic area's transcription
    `signAttemptSpec` of lines 17–29. Returns `(z mod± q, h)` or `none` for
    `⊥`. (`SignFips.finish`.) -/
def fipsFinish (P : Params) (key : ExpandedKey) (y w : PolyVec) (cHat : Poly) :
    Option (PolyVec × PolyVec) :=
  let cs1 : PolyVec := fun r => fipsProduct cHat (fipsNTT (key.s1 r))
  let cs2 : PolyVec := fun r => fipsProduct cHat (fipsNTT (key.s2 r))
  let ct0 : PolyVec := fun r => fipsProduct cHat (fipsNTT (key.t0 r))
  let z := mkRows P.l fun r i => y r i + cs1 r i
  let rows := mkRows P.k fun r i => (w r i, cs2 r i, ct0 r i)
  (MLDSA.signAttemptSpec P.gamma1 P.gamma2 P.beta P.omega z rows).map fun zh =>
    (listsToVec (zh.1.map (List.map fun x => MLDSA.modPM x MLDSA.q)), listsToVec zh.2)

/-- `fipsFinish` only depends on `w` modulo `q` (on rows `< k`). -/
theorem fipsFinish_congr_w (P : Params) (key : ExpandedKey) (y w w' : PolyVec) (cHat : Poly)
    (hw : ∀ r < P.k, ∀ i < 256, w r i % MLDSA.q = w' r i % MLDSA.q) :
    fipsFinish P key y w cHat = fipsFinish P key y w' cHat := by
  unfold fipsFinish
  simp only
  rw [signAttemptSpec_congr _ _ _ _ P.l P.k _ _ w w' _ _ _ _ (fun _ _ _ _ => rfl) hw
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl), Option.map_map]
  conv_rhs => rw [signAttemptSpec_fst, Option.map_map]

/-- `fipsFinish` only reads rows `< ℓ` of `y` and `< k` of `w`. -/
theorem fipsFinish_local (P : Params) (key : ExpandedKey) (y y' w w' : PolyVec) (cHat : Poly)
    (hy : ∀ s < P.l, y s = y' s) (hw : ∀ r < P.k, w r = w' r) :
    fipsFinish P key y w cHat = fipsFinish P key y' w' cHat := by
  unfold fipsFinish
  simp only
  rw [mkRows_congr (f := fun r i => y r i + fipsProduct cHat (fipsNTT (key.s1 r)) i)
      (fun r hr i _ => by rw [hy r hr]),
    mkRows_congr (f := fun r i => (w r i, fipsProduct cHat (fipsNTT (key.s2 r)) i,
      fipsProduct cHat (fipsNTT (key.t0 r)) i)) (fun r hr i _ => by rw [hw r hr])]

/-! ## The challenge -/

/-- The FIPS `SampleInBall` value has FIPS shape: coefficients in
    `{−1, 0, 1}`, at most `τ` of them nonzero (exactly `τ` when the sampler
    terminates; `0` otherwise, by the convention of `sampleInBall`). -/
theorem sampleInBall_ball {tau : ℕ} (htau : tau ≤ 256) (s : ℕ → Byte) :
    (∀ i < 256, sampleInBall tau s i = -1 ∨ sampleInBall tau s i = 0 ∨ sampleInBall tau s i = 1) ∧
    ((((Finset.range 256).filter fun i => sampleInBall tau s i ≠ 0).card : ℕ) : ℤ) ≤ tau := by
  unfold sampleInBall
  split
  · rename_i h
    obtain ⟨hcard, hv, -⟩ := sampleInBall_output htau (Classical.choose_spec h)
    refine ⟨fun i _ => ?_, by rw [hcard]⟩
    rcases hv i with h' | h' | h' <;> simp [h']
  · simp

/-! ## The code's candidate is FIPS 204's -/

/-- `cs = center (inverse_ntt (pointwise (ntt c) (ntt s)))` is congruent to
    FIPS's `⟨⟨c·s⟩⟩` modulo `q`. -/
theorem ocamlCenteredProduct_emod (c s : Poly) (i : ℕ) (hi : i < 256) :
    ocamlCenteredProduct (MLDSA.ntt c) (MLDSA.ntt s) i % MLDSA.q =
      fipsProduct (fipsNTT c) (fipsNTT s) i % MLDSA.q := by
  unfold ocamlCenteredProduct fipsProduct
  rw [MLDSA.center_emod, ← ntt_eq_fips, ← pointwise_eq_fips, ← inverseNtt_eq_fips,
    ocamlInverseNtt, trunc_of_lt hi]

/-- **The OCaml candidate equals FIPS 204 Algorithm 7 lines 15–30** for the
    `(w1, w0) = decompose w` it is given, when the mask is in `(−γ1, γ1]`, the
    challenge `c` has FIPS shape and the key's `s1`, `s2` are in `[−η, η]`. -/
theorem ocamlCandidate_eq_fipsFinish {P : Params} (hP : P.Valid) (key : ExpandedKey)
    (hs1 : ∀ r < P.l, ∀ i < 256, -(P.eta : ℤ) ≤ key.s1 r i ∧ key.s1 r i ≤ P.eta)
    (hs2 : ∀ r < P.k, ∀ i < 256, -(P.eta : ℤ) ≤ key.s2 r i ∧ key.s2 r i ≤ P.eta)
    (y w : PolyVec) (hy : ∀ r < P.l, ∀ i < 256, -(P.gamma1 : ℤ) < y r i ∧ y r i ≤ P.gamma1)
    (c : Poly) (hc : ∀ i < 256, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hcτ : ((((Finset.range 256).filter fun i => c i ≠ 0).card : ℕ) : ℤ) ≤ P.tau) :
    ocamlCandidate P key y (fun r i => (MLDSA.decompose P.gamma2 (w r i)).2)
        (fun r i => (MLDSA.decompose P.gamma2 (w r i)).1) (MLDSA.ntt c) =
      fipsFinish P key y w (fipsNTT c) := by
  have hf := e2eFacts hP
  -- `‖c·s‖∞ ≤ τη` for the code's centered products
  have hsmall : (P.tau : ℤ) * P.eta ≤ 4190208 := by
    rcases hf.tauEta with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> norm_num
  have hcs : ∀ (s : Poly), (∀ j < 256, -(P.eta : ℤ) ≤ s j ∧ s j ≤ P.eta) → ∀ i < 256,
      |ocamlCenteredProduct (MLDSA.ntt c) (MLDSA.ntt s) i| ≤ (P.beta : ℤ) := by
    intro s hs i hi
    have := (MLDSA.center_cs c s P.tau P.eta hc hcτ (fun j hj => abs_le.mpr (hs j hj)) hsmall i hi).2
    unfold ocamlCenteredProduct; unfold Params.beta; push_cast; exact this
  unfold ocamlCandidate
  simp only
  rw [codeTail_eq_signAttempt]
  rw [MLDSA.signAttempt_eq_spec (by exact_mod_cast hf.paramOk)]
  · -- the code's inputs are congruent to FIPS's
    unfold fipsFinish
    simp only
    rw [signAttemptSpec_congr _ _ _ _ P.l P.k _
        (fun r i => y r i + fipsProduct (fipsNTT c) (fipsNTT (key.s1 r)) i) w w _
        (fun r i => fipsProduct (fipsNTT c) (fipsNTT (key.s2 r)) i) _
        (fun r i => fipsProduct (fipsNTT c) (fipsNTT (key.t0 r)) i)
        (fun r _ i hi => by rw [Int.add_emod, ocamlCenteredProduct_emod _ _ i hi, ← Int.add_emod])
        (fun _ _ _ _ => rfl)
        (fun r _ i hi => ocamlCenteredProduct_emod _ _ i hi)
        (fun r _ i hi => ocamlCenteredProduct_emod _ _ i hi),
      Option.map_map]
    conv_rhs => rw [signAttemptSpec_fst, Option.map_map]
    congr 1
    funext zh
    simp only [Function.comp, Prod.mk.injEq, and_true]
    rw [mkRows_map]
    congr 1
    apply mkRows_congr
    intro r hr i hi
    -- `z = y + cs1` is small, hence its own `mod± q` representative
    have hzs := hcs (key.s1 r) (hs1 r hr) i hi
    have hyr := hy r hr i hi
    have hb : (P.beta : ℤ) ≤ 196 := by unfold Params.beta; exact_mod_cast hf.beta_small
    have hg : (P.gamma1 : ℤ) ≤ 2 ^ 19 := by rcases hf.gamma1 with h | h <;> rw [h] <;> norm_num
    have hcong : (y r i + fipsProduct (fipsNTT c) (fipsNTT (key.s1 r)) i) % MLDSA.q =
        (y r i + ocamlCenteredProduct (MLDSA.ntt c) (MLDSA.ntt (key.s1 r)) i) % MLDSA.q := by
      rw [Int.add_emod, ← ocamlCenteredProduct_emod _ _ i hi, ← Int.add_emod]
    rw [abs_le] at hzs
    rw [modPM_congr hcong, MLDSA.modPM_q_of_small (by omega) (by omega)]
  · -- `‖cs2‖∞ ≤ β`
    intro row hrow e he
    obtain ⟨r, hr, rfl⟩ := mem_mkRows.mp hrow
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    rw [List.mem_range] at hi
    simp only
    unfold ocamlCenteredProduct
    rw [MLDSA.center_center]
    exact hcs (key.s2 r) (hs2 r hr) i hi

/-- Consequences of acceptance by FIPS 204 Algorithm 7: the returned `z` is
    in `(−γ1, γ1]` (on the `ℓ × 256` entries) and the hint has entries in
    `{0, 1}` and at most `ω` ones. -/
theorem fipsFinish_accepted {P : Params} (hP : P.Valid) {key : ExpandedKey} {y w : PolyVec}
    {cHat : Poly} {z h : PolyVec} (hacc : fipsFinish P key y w cHat = some (z, h)) :
    (∀ r < P.l, ∀ i < 256, -(P.gamma1 : ℤ) < z r i ∧ z r i ≤ P.gamma1) ∧
    Encoding.Hint.weight P.k (hintToVec P.k h) ≤ P.omega := by
  have hf := e2eFacts hP
  unfold fipsFinish at hacc
  simp only at hacc
  set zL := mkRows P.l fun r i => y r i + fipsProduct cHat (fipsNTT (key.s1 r)) i with hzL
  obtain ⟨zh, hs, he⟩ := Option.map_eq_some_iff.mp hacc
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  unfold MLDSA.signAttemptSpec at hs
  simp only [mkRows_map] at hs
  split_ifs at hs with h1 h2
  cases hs
  simp only [not_or] at h1 h2
  refine ⟨fun r hr i hi => ?_, ?_⟩
  · -- `|z mod± q| < γ1 − β`
    have hn := h1.1
    rw [infNormGe_mkRows] at hn
    have hlt : ¬ MLDSA.coeffNorm (y r i + fipsProduct cHat (fipsNTT (key.s1 r)) i) ≥
        P.gamma1 - P.beta := fun hc => hn ⟨r, hr, i, hi, hc⟩
    unfold MLDSA.coeffNorm at hlt
    rw [mkRows_map, listsToVec_mkRows _ _ r i hr hi]
    have hb : (0 : ℤ) ≤ P.beta := by positivity
    have hlt' := lt_of_not_ge hlt
    rw [abs_lt] at hlt'
    constructor <;> linarith [hlt'.1, hlt'.2]
  · -- the hint weight is the hint count
    have h01 : ∀ r < P.k, ∀ c < 256, listsToVec (mkRows P.k fun r i =>
        MLDSA.makeHintSpec (P.gamma2 : ℤ) (-fipsProduct cHat (fipsNTT (key.t0 r)) i)
          (w r i - fipsProduct cHat (fipsNTT (key.s2 r)) i +
            fipsProduct cHat (fipsNTT (key.t0 r)) i)) r c = 0 ∨
        listsToVec (mkRows P.k fun r i =>
        MLDSA.makeHintSpec (P.gamma2 : ℤ) (-fipsProduct cHat (fipsNTT (key.t0 r)) i)
          (w r i - fipsProduct cHat (fipsNTT (key.s2 r)) i +
            fipsProduct cHat (fipsNTT (key.t0 r)) i)) r c = 1 := by
      intro r hr c hc
      rw [listsToVec_mkRows _ _ r c hr hc]
      unfold MLDSA.makeHintSpec; split_ifs <;> simp
    have hw := weight_hintToVec P.k _ h01
    rw [← sum_mkRows] at hw
    have h3 := h2.2
    push Not at h3
    have h4 := hw.trans_le h3
    exact_mod_cast h4

end OcamlPq.EndToEnd.MLDSA
