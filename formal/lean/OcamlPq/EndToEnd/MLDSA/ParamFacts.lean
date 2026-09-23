import OcamlPq.EndToEnd.MLDSA.Arith

/-!
# Facts about the three parameter sets used across the areas

Each area states its hypotheses in its own terms (`MLDSA.ParamOk γ2 β`,
`Encoding.Mldsa.Params.Valid`, `MLDSAAlg.Params.Valid`, bit widths via
`MLDSAAlg.bitlen` or `Encoding.Spec.bitlen`, …). `encParams` is the Encoding
area's record of `Mldsa_engine.Make`'s parameters for an `MLDSAAlg.Params`;
`e2eFacts` collects every per-parameter fact the bridge needs, each
checked by evaluation on ML-DSA-44/65/87.
-/

namespace OcamlPq.EndToEnd.MLDSA

open OcamlPq.MLDSAAlg

/-- The Encoding area's parameter record for `P`. -/
def encParams (P : Params) : Encoding.Mldsa.Params :=
  ⟨P.k, P.l, P.eta, P.gamma1, P.gamma2, P.omega, P.cTildeBytes⟩

/-- `(q − 1)/(2γ2)`, the number of `w1` values (FIPS 204 §7.4). -/
def w1Count (P : Params) : ℕ := (q - 1) / (2 * P.gamma2)

/-- Everything the bridge needs about a valid parameter set. -/
structure E2EFacts (P : Params) : Prop where
  paramOk : MLDSA.ParamOk (P.gamma2 : ℤ) ((P.tau * P.eta : ℕ) : ℤ)
  gamma2Ok : MLDSA.Gamma2Ok (P.gamma2 : ℤ)
  tauEta : ((P.tau : ℤ) = 39 ∧ (P.eta : ℤ) = 2) ∨ ((P.tau : ℤ) = 49 ∧ (P.eta : ℤ) = 4) ∨
    ((P.tau : ℤ) = 60 ∧ (P.eta : ℤ) = 2)
  eta : P.eta = 2 ∨ P.eta = 4
  gamma1 : P.gamma1 = 2 ^ 17 ∨ P.gamma1 = 2 ^ 19
  gamma2 : P.gamma2 = (Encoding.Mldsa.q - 1) / 88 ∨ P.gamma2 = (Encoding.Mldsa.q - 1) / 32
  encValid : (encParams P).Valid
  t1Bound : 2 ^ (bitlen (q - 1) - d) - 1 = 2 ^ 10 - 1
  t1Bits : bitlen (q - 1) - d = 10
  t0a : 2 ^ (d - 1) - 1 = 2 ^ 12 - 1
  t0b : 2 ^ (d - 1) = 2 ^ 12
  zBits : 32 * (1 + bitlen (P.gamma1 - 1)) = 32 * Encoding.Mldsa.zBits P.gamma1
  zPacked : P.zPackedBytes = 32 * Encoding.Mldsa.zBits P.gamma1
  zPackedEnc : (encParams P).zPackedBytes = P.zPackedBytes
  etaBits : Encoding.Mldsa.etaBits P.eta = P.etaBits
  w1Bits : Encoding.Mldsa.w1Bits P.gamma2 = P.w1Bits
  w1Count_pos : 0 < w1Count P
  w1Count_le : w1Count P ≤ 2 ^ Encoding.Mldsa.w1Bits P.gamma2
  w1Count_int : (((q - 1) / (2 * P.gamma2) : ℕ) : ℤ) = (MLDSA.q - 1) / (2 * (P.gamma2 : ℤ))
  w1Bound : (q - 1) / (2 * P.gamma2) - 1 = (Encoding.Mldsa.q - 1) / (2 * P.gamma2) - 1
  sigSize : (encParams P).sigSize = P.signatureSize
  vkSize : (encParams P).vkSize = P.verificationKeySize
  tau_le : P.tau ≤ 64
  beta_small : P.tau * P.eta ≤ 196
  gamma1_big : 2 * (P.tau * P.eta) < P.gamma1
  k_pos : 0 < P.k
  l_pos : 0 < P.l
  gamma2_beta : P.tau * P.eta < P.gamma2

theorem e2eFacts {P : Params} (hP : P.Valid) : E2EFacts P := by
  rcases hP with rfl | rfl | rfl <;>
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | decide
    | (simp only [MLDSA.ParamOk, MLDSA.Gamma2Ok]; norm_num [mldsa44, mldsa65, mldsa87])
    | (simp only [Encoding.Mldsa.Params.Valid, encParams]; norm_num [mldsa44, mldsa65, mldsa87])

end OcamlPq.EndToEnd.MLDSA
