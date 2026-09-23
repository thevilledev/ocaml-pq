import OcamlPq.MLDSAAlg.RejNTT
import OcamlPq.MLDSAAlg.RejBounded
import OcamlPq.MLDSAAlg.SampleInBall

/-!
# ExpandA, ExpandS, ExpandMask (FIPS 204 Algorithms 32–34)

`expand_matrix`, `expand_secret` and `mask_polynomial` (`mldsa_engine.ml`,
lines 408–424 and 369–373) are modelled on top of the sampler models:
the OCaml `Array.init` calls are pure, so "the OCaml expression returns the
array `A`" means "every element's sampler call returns `A[i]`".

The FIPS samplers are also packaged as total functions (`rejNTTPoly`,
`rejBoundedPoly`, `sampleInBall`: the unique output when the algorithm
terminates, `0` otherwise) for use in the composition proofs; the lemmas
`*_returns_eq` say that any value the OCaml sampler returns is that total
function's value.
-/

namespace OcamlPq.MLDSAAlg

open Classical in
/-- FIPS 204 `RejNTTPoly` as a total function of the stream. -/
noncomputable def rejNTTPoly (s : ℕ → Byte) : Poly :=
  if h : ∃ a, RejNTTPolyReturns s a then Classical.choose h else fun _ => 0

open Classical in
/-- FIPS 204 `RejBoundedPoly` as a total function of the stream. -/
noncomputable def rejBoundedPoly (eta : ℕ) (s : ℕ → Byte) : Poly :=
  if h : ∃ a, RejBoundedReturns eta s a then Classical.choose h else fun _ => 0

open Classical in
/-- FIPS 204 `SampleInBall` as a total function of the stream. -/
noncomputable def sampleInBall (tau : ℕ) (s : ℕ → Byte) : Poly :=
  if h : ∃ a, SampleInBallReturns tau s a then Classical.choose h else fun _ => 0

theorem RejNTTPolyReturns.eq {s : ℕ → Byte} {a : Poly} (h : RejNTTPolyReturns s a) :
    a = rejNTTPoly s := by
  have hex : ∃ a, RejNTTPolyReturns s a := ⟨a, h⟩
  rw [rejNTTPoly, dite_eq_left hex]
  exact RejNTTPolyReturns.unique h (Classical.choose_spec hex)

theorem RejBoundedReturns.eq {eta : ℕ} {s : ℕ → Byte} {a : Poly} (h : RejBoundedReturns eta s a) :
    a = rejBoundedPoly eta s := by
  have hex : ∃ a, RejBoundedReturns eta s a := ⟨a, h⟩
  rw [rejBoundedPoly, dite_eq_left hex]
  exact RejBoundedReturns.unique h (Classical.choose_spec hex)

theorem SampleInBallReturns.eq {tau : ℕ} {s : ℕ → Byte} {a : Poly}
    (h : SampleInBallReturns tau s a) : a = sampleInBall tau s := by
  have hex : ∃ a, SampleInBallReturns tau s a := ⟨a, h⟩
  rw [sampleInBall, dite_eq_left hex]
  exact SampleInBallReturns.unique h (Classical.choose_spec hex)

/-- Whatever `uniform_polynomial seed nonce 840` returns is
    `RejNTTPoly(seed ‖ IntegerToBytes(nonce, 2))`. -/
theorem uniform_returns_eq {G : XOF} {seed : Bytes} {nonce : ℕ} {p : Poly}
    (h : UniformReturns G seed nonce 840 p) :
    p = rejNTTPoly (G (seed ++ integerToBytes nonce 2)) :=
  RejNTTPolyReturns.eq ((uniformPolynomial_returns_iff (by norm_num) p).mp h)

/-- Whatever `eta_polynomial seed nonce 272` returns is
    `RejBoundedPoly(seed ‖ IntegerToBytes(nonce, 2))`. -/
theorem eta_returns_eq {eta : ℕ} (heta : eta = 2 ∨ eta = 4) {H : XOF} {seed : Bytes} {nonce : ℕ}
    {p : Poly} (h : EtaReturns eta H seed nonce 272 p) :
    p = rejBoundedPoly eta (H (seed ++ integerToBytes nonce 2)) :=
  RejBoundedReturns.eq ((etaPolynomial_returns_iff heta (by norm_num) p).mp h)

/-- Whatever `challenge_polynomial seed 136` returns is `SampleInBall(seed)`. -/
theorem challenge_returns_eq {tau : ℕ} (htau : tau ≤ 64) {H : XOF} {seed : Bytes} {c : Poly}
    (h : ChallengeReturns tau H seed 136 c) : c = sampleInBall tau (H seed) :=
  SampleInBallReturns.eq ((challengePolynomial_returns_iff htau (by norm_num) c).mp h)

/-! ## Nonce encodings -/

/-- `u16_le ((row lsl 8) + column)` is `IntegerToBytes(column, 1) ‖
    IntegerToBytes(row, 1)`, the ExpandA domain separator (column first). -/
theorem u16le_matrix_nonce {row column : ℕ} (hc : column < 256) :
    integerToBytes ((row <<< 8) + column) 2 = integerToBytes column 1 ++ integerToBytes row 1 := by
  simp only [integerToBytes, Nat.shiftLeft_eq, List.cons_append, List.nil_append,
    List.cons.injEq, and_true]
  constructor
  · congr 1; omega
  · congr 1; omega

/-- `(row lsl 8) + column` is `Portable` and below `2^16`. -/
theorem matrix_nonce_portable {row column : ℕ} (hr : row < 256) (hc : column < 256) :
    (row <<< 8) + column < 2 ^ 16 ∧ Portable (((row <<< 8) + column : ℕ) : ℤ) := by
  rw [Nat.shiftLeft_eq]
  exact ⟨by omega, Portable.of_nat_lt (by omega)⟩

/-! ## ExpandA (Algorithm 32) -/

/-- FIPS 204 Algorithm 32, `ExpandA(ρ)`: `Â[r, s] ← RejNTTPoly(ρ ‖
    IntegerToBytes(s, 1) ‖ IntegerToBytes(r, 1))`. -/
noncomputable def expandA (G : XOF) (rho : Bytes) (r s : ℕ) : Poly :=
  rejNTTPoly (G (rho ++ integerToBytes s 1 ++ integerToBytes r 1))

/-- `expand_matrix rho` (`mldsa_engine.ml`, lines 408–411) returns the
    `k × ℓ` matrix `A`: `Array.init P.k (fun row -> Array.init P.l (fun column
    -> uniform_polynomial rho ((row lsl 8) + column) 840))`. -/
def ExpandMatrixReturns (G : XOF) (P : Params) (rho : Bytes) (A : ℕ → ℕ → Poly) : Prop :=
  ∀ row < P.k, ∀ column < P.l, UniformReturns G rho ((row <<< 8) + column) 840 (A row column)

/-- **Obligation 5 (ExpandA).** Whatever `expand_matrix` returns is FIPS 204
    `ExpandA(ρ)` (on all `k × ℓ` entries), and `expand_matrix` returns
    whenever every `RejNTTPoly` call of `ExpandA` terminates. -/
theorem expandMatrix_spec (G : XOF) {P : Params} (hP : P.Valid) (rho : Bytes) :
    (∀ A, ExpandMatrixReturns G P rho A → ∀ r < P.k, ∀ s < P.l, A r s = expandA G rho r s) ∧
    ((∀ r < P.k, ∀ s < P.l,
        ∃ a, RejNTTPolyReturns (G (rho ++ integerToBytes s 1 ++ integerToBytes r 1)) a) →
      ExpandMatrixReturns G P rho (expandA G rho)) := by
  obtain ⟨-, -, hk, hl, -⟩ := hP.facts
  constructor
  · intro A hA r hr s hs
    have := uniform_returns_eq (hA r hr s hs)
    rw [this, u16le_matrix_nonce (by omega), ← List.append_assoc]
    rfl
  · intro hterm row hr column hc
    obtain ⟨a, ha⟩ := hterm row hr column hc
    have ha' := ha
    rw [List.append_assoc, ← u16le_matrix_nonce (by omega)] at ha'
    have := (uniformPolynomial_returns_iff (L := 840) (by norm_num) a).mpr ha'
    unfold expandA
    rw [← RejNTTPolyReturns.eq ha]
    exact this

/-! ## ExpandS (Algorithm 33) -/

/-- FIPS 204 Algorithm 33, `ExpandS(ρ)`: `s1[r] ← RejBoundedPoly(ρ ‖
    IntegerToBytes(r, 2))` for `r < ℓ`, `s2[r] ← RejBoundedPoly(ρ ‖
    IntegerToBytes(r + ℓ, 2))` for `r < k`. -/
noncomputable def expandS (H : XOF) (P : Params) (rho : Bytes) : (ℕ → Poly) × (ℕ → Poly) :=
  (fun r => rejBoundedPoly P.eta (H (rho ++ integerToBytes r 2)),
   fun r => rejBoundedPoly P.eta (H (rho ++ integerToBytes (r + P.l) 2)))

/-- `expand_secret seed` (`mldsa_engine.ml`, lines 413–416) returns
    `(s1, s2)`: `s1 = Array.init P.l (fun index -> eta_polynomial seed index
    272)`, `s2 = Array.init P.k (fun index -> eta_polynomial seed (P.l + index)
    272)`. -/
def ExpandSecretReturns (H : XOF) (P : Params) (seed : Bytes) (s1 s2 : ℕ → Poly) : Prop :=
  (∀ index < P.l, EtaReturns P.eta H seed index 272 (s1 index)) ∧
  (∀ index < P.k, EtaReturns P.eta H seed (P.l + index) 272 (s2 index))

/-- **Obligation 5 (ExpandS).** Whatever `expand_secret` returns is FIPS 204
    `ExpandS(ρ′)` with nonces `r` and `r + ℓ`. -/
theorem expandSecret_spec (H : XOF) {P : Params} (hP : P.Valid) (seed : Bytes)
    (s1 s2 : ℕ → Poly) (h : ExpandSecretReturns H P seed s1 s2) :
    (∀ r < P.l, s1 r = (expandS H P seed).1 r) ∧ (∀ r < P.k, s2 r = (expandS H P seed).2 r) := by
  obtain ⟨-, -, -, -, -, -, heta, -⟩ := hP.facts
  refine ⟨fun r hr => eta_returns_eq heta (h.1 r hr), fun r hr => ?_⟩
  rw [eta_returns_eq heta (h.2 r hr), Nat.add_comm]
  rfl

/-- Conversely `expand_secret` returns whenever every `RejBoundedPoly` call
    of `ExpandS` terminates. -/
theorem expandSecret_complete (H : XOF) {P : Params} (hP : P.Valid) (seed : Bytes)
    (hterm : (∀ r < P.l, ∃ a, RejBoundedReturns P.eta (H (seed ++ integerToBytes r 2)) a) ∧
      (∀ r < P.k, ∃ a, RejBoundedReturns P.eta (H (seed ++ integerToBytes (r + P.l) 2)) a)) :
    ExpandSecretReturns H P seed (expandS H P seed).1 (expandS H P seed).2 := by
  obtain ⟨-, -, -, -, -, -, heta, -⟩ := hP.facts
  constructor
  · intro r hr
    obtain ⟨a, ha⟩ := hterm.1 r hr
    have := (etaPolynomial_returns_iff heta (by norm_num : 0 < 272) a).mpr ha
    simp only [expandS]
    rwa [← RejBoundedReturns.eq ha]
  · intro r hr
    obtain ⟨a, ha⟩ := hterm.2 r hr
    have := (etaPolynomial_returns_iff heta (by norm_num : 0 < 272) a).mpr
      (by rwa [Nat.add_comm] at ha)
    simp only [expandS]
    rw [← RejBoundedReturns.eq ha]; exact this

/-! ## ExpandMask (Algorithm 34) -/

/-- `mask_polynomial seed nonce` (`mldsa_engine.ml`, lines 369–373):
    `unpack_z (shake256 ~output_length:z_packed_bytes (seed ^ u16_le nonce))`.
    `unpackZ` is the OCaml `unpack_z` (another module's subject). -/
def maskPolynomial (H : XOF) (P : Params) (unpackZ : Bytes → Poly) (seed : Bytes) (nonce : ℕ) :
    Poly :=
  unpackZ (H.squeeze (seed ++ u16le nonce) P.zPackedBytes)

/-- FIPS 204 Algorithm 34, `ExpandMask(ρ, μ)`, entry `r`:
    `c ← 1 + bitlen(γ1 − 1)`; `x ← IntegerToBytes(μ + r, 2)`;
    `v ← H(ρ ‖ x, 32c)`; `y[r] ← BitUnpack(v, γ1 − 1, γ1)`. -/
def expandMask (H : XOF) (P : Params) (bitUnpack : Bytes → ℕ → ℕ → Poly) (rho : Bytes)
    (mu r : ℕ) : Poly :=
  let c := 1 + bitlen (P.gamma1 - 1)
  let x := integerToBytes (mu + r) 2
  let v := H.squeeze (rho ++ x) (32 * c)
  bitUnpack v (P.gamma1 - 1) P.gamma1

/-- **Obligation 4.** For a valid parameter set, if `unpack_z` agrees with
    `BitUnpack(·, γ1 − 1, γ1)` on inputs of the FIPS length `32c`, then the
    `r`-th mask polynomial the signer computes with nonce `κ + r` is
    `ExpandMask(ρ″, κ)[r]`: the output length `z_packed_bytes` is `32c` and
    the nonce encoding is `IntegerToBytes(κ + r, 2)`. -/
theorem maskPolynomial_eq (H : XOF) {P : Params} (hP : P.Valid) (unpackZ : Bytes → Poly)
    (bitUnpack : Bytes → ℕ → ℕ → Poly)
    (hunpack : ∀ v : Bytes, v.length = 32 * (1 + bitlen (P.gamma1 - 1)) →
      unpackZ v = bitUnpack v (P.gamma1 - 1) P.gamma1)
    (rho : Bytes) (kappa r : ℕ) :
    maskPolynomial H P unpackZ rho (kappa + r) = expandMask H P bitUnpack rho kappa r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hz⟩ := hP.facts
  unfold maskPolynomial expandMask
  rw [hz, u16le_eq_integerToBytes]
  exact hunpack _ (by simp)

end OcamlPq.MLDSAAlg
