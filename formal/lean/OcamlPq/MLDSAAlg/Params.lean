import Mathlib
import OcamlPq.Common.Int

/-!
# ML-DSA parameter sets

`Params` mirrors the OCaml `PARAMETERS` signature (`mldsa_engine.ml`,
lines 17–27) and the three instances `Mldsa44`, `Mldsa65`, `Mldsa87`
(lines 910–944). The derived constants of `Make` (lines 107–137) are
transcribed literally. `FipsParams` is FIPS 204 Table 1 (and the sizes of
Table 2), written independently; the theorems check that the two agree.
-/

namespace OcamlPq.MLDSAAlg

/-- The OCaml `PARAMETERS` module type (`mldsa_engine.ml`, lines 17–27). -/
structure Params where
  k : ℕ
  l : ℕ
  eta : ℕ
  tau : ℕ
  gamma1 : ℕ
  gamma2 : ℕ
  omega : ℕ
  cTildeBytes : ℕ
  deriving DecidableEq, Repr

/-- `q` (`mldsa_engine.ml`, line 107). -/
def q : ℕ := 8380417
/-- `n` (line 108). -/
def n : ℕ := 256
/-- `d` (line 109). -/
def d : ℕ := 13

/-- `Mldsa44` (`mldsa_engine.ml`, lines 910–920). -/
def mldsa44 : Params where
  k := 4; l := 4; eta := 2; tau := 39; gamma1 := 1 <<< 17
  gamma2 := (8380417 - 1) / 88; omega := 80; cTildeBytes := 32

/-- `Mldsa65` (`mldsa_engine.ml`, lines 922–932). -/
def mldsa65 : Params where
  k := 6; l := 5; eta := 4; tau := 49; gamma1 := 1 <<< 19
  gamma2 := (8380417 - 1) / 32; omega := 55; cTildeBytes := 48

/-- `Mldsa87` (`mldsa_engine.ml`, lines 934–944). -/
def mldsa87 : Params where
  k := 8; l := 7; eta := 2; tau := 60; gamma1 := 1 <<< 19
  gamma2 := (8380417 - 1) / 32; omega := 75; cTildeBytes := 64

/-- The three parameter sets the library instantiates. -/
def Params.Valid (P : Params) : Prop := P = mldsa44 ∨ P = mldsa65 ∨ P = mldsa87

instance (P : Params) : Decidable P.Valid := by unfold Params.Valid; infer_instance

namespace Params
variable (P : Params)

/-- `beta = P.tau * P.eta` (line 110). -/
def beta : ℕ := P.tau * P.eta
/-- `seed_size` (line 111). -/
def seedSize : ℕ := 32
/-- `tr_bytes` (line 112). -/
def trBytes : ℕ := 64
/-- `eta_bits` (line 113). -/
def etaBits : ℕ := if P.eta = 2 then 3 else 4
/-- `eta_packed_bytes` (line 114). -/
def etaPackedBytes : ℕ := n * P.etaBits / 8
/-- `t0_packed_bytes` (line 115). -/
def t0PackedBytes : ℕ := 416
/-- `t1_packed_bytes` (line 116). -/
def t1PackedBytes : ℕ := 320
/-- `z_bits` (line 117). -/
def zBits : ℕ := if P.gamma1 = 1 <<< 17 then 18 else 20
/-- `z_packed_bytes` (line 118). -/
def zPackedBytes : ℕ := n * P.zBits / 8
/-- `w1_bits` (line 119). -/
def w1Bits : ℕ := if P.gamma2 = (q - 1) / 88 then 6 else 4
/-- `verification_key_size` (line 120). -/
def verificationKeySize : ℕ := 32 + P.k * 320
/-- `signing_key_size` (lines 122–125). -/
def signingKeySize : ℕ :=
  (2 * 32) + 64 + ((P.l + P.k) * P.etaPackedBytes) + (P.k * 416)
/-- `signature_size` (lines 127–128). -/
def signatureSize : ℕ := P.cTildeBytes + (P.l * P.zPackedBytes) + P.omega + P.k

end Params

/-- `bitlen x` (FIPS 204 §2.3): the number of bits in the binary
    representation of `x` (fuel-bounded so the kernel can evaluate it; exact
    for `x < 2^64`). -/
def bitlenAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, x => if x = 0 then 0 else bitlenAux f (x / 2) + 1

/-- `bitlen` of FIPS 204. -/
def bitlen (x : ℕ) : ℕ := bitlenAux 64 x

/-- FIPS 204 Table 1 (and Table 2), transcribed independently of the code. -/
structure FipsParams where
  q : ℕ
  zeta : ℕ
  d : ℕ
  tau : ℕ
  lambda : ℕ
  gamma1 : ℕ
  gamma2 : ℕ
  k : ℕ
  l : ℕ
  eta : ℕ
  beta : ℕ
  omega : ℕ
  pkSize : ℕ
  skSize : ℕ
  sigSize : ℕ

/-- FIPS 204 Table 1 / Table 2, ML-DSA-44. -/
def fips44 : FipsParams :=
  { q := 8380417, zeta := 1753, d := 13, tau := 39, lambda := 128, gamma1 := 2 ^ 17,
    gamma2 := (8380417 - 1) / 88, k := 4, l := 4, eta := 2, beta := 78, omega := 80,
    pkSize := 1312, skSize := 2560, sigSize := 2420 }

/-- FIPS 204 Table 1 / Table 2, ML-DSA-65. -/
def fips65 : FipsParams :=
  { q := 8380417, zeta := 1753, d := 13, tau := 49, lambda := 192, gamma1 := 2 ^ 19,
    gamma2 := (8380417 - 1) / 32, k := 6, l := 5, eta := 4, beta := 196, omega := 55,
    pkSize := 1952, skSize := 4032, sigSize := 3309 }

/-- FIPS 204 Table 1 / Table 2, ML-DSA-87. -/
def fips87 : FipsParams :=
  { q := 8380417, zeta := 1753, d := 13, tau := 60, lambda := 256, gamma1 := 2 ^ 19,
    gamma2 := (8380417 - 1) / 32, k := 8, l := 7, eta := 2, beta := 120, omega := 75,
    pkSize := 2592, skSize := 4896, sigSize := 4627 }

/-- The OCaml parameter record `P` implements the FIPS 204 parameter set `F`:
    every Table 1 entry agrees (λ via `c_tilde_bytes = λ/4`), the derived
    bit widths are the FIPS ones (`bitlen(2η)`, `1 + bitlen(γ1 − 1)`,
    `bitlen((q − 1)/(2γ2) − 1)`), and the three byte sizes agree with both
    Table 2 and the FIPS 204 size formulas (§7.2, Algorithms 22, 24, 26). -/
def Implements (P : Params) (F : FipsParams) : Prop :=
  q = F.q ∧ d = F.d ∧ P.tau = F.tau ∧ P.cTildeBytes * 4 = F.lambda ∧
  P.gamma1 = F.gamma1 ∧ P.gamma2 = F.gamma2 ∧ P.k = F.k ∧ P.l = F.l ∧
  P.eta = F.eta ∧ P.beta = F.beta ∧ P.beta = F.tau * F.eta ∧ P.omega = F.omega ∧
  P.etaBits = bitlen (2 * F.eta) ∧
  P.zBits = 1 + bitlen (F.gamma1 - 1) ∧
  P.w1Bits = bitlen ((F.q - 1) / (2 * F.gamma2) - 1) ∧
  bitlen (F.q - 1) - F.d = 10 ∧ Params.t1PackedBytes = 32 * 10 ∧ Params.t0PackedBytes = 32 * F.d ∧
  P.zPackedBytes = 32 * (1 + bitlen (F.gamma1 - 1)) ∧
  P.verificationKeySize = F.pkSize ∧
  P.verificationKeySize = 32 + 32 * F.k * (bitlen (F.q - 1) - F.d) ∧
  P.signingKeySize = F.skSize ∧
  P.signingKeySize = 32 + 32 + 64 + 32 * ((F.l + F.k) * bitlen (2 * F.eta) + F.d * F.k) ∧
  P.signatureSize = F.sigSize ∧
  P.signatureSize = F.lambda / 4 + F.l * 32 * (1 + bitlen (F.gamma1 - 1)) + F.omega + F.k

theorem mldsa44_implements : Implements mldsa44 fips44 := by unfold Implements; decide
theorem mldsa65_implements : Implements mldsa65 fips65 := by unfold Implements; decide
theorem mldsa87_implements : Implements mldsa87 fips87 := by unfold Implements; decide

/-- Facts about every valid parameter set used by the other modules. -/
theorem Params.Valid.facts {P : Params} (hP : P.Valid) :
    P.l ∈ ({4, 5, 7} : Finset ℕ) ∧ P.k ∈ ({4, 6, 8} : Finset ℕ) ∧
    P.k < 256 ∧ P.l < 256 ∧ P.tau ≤ 60 ∧ 0 < P.tau ∧
    (P.eta = 2 ∨ P.eta = 4) ∧ P.cTildeBytes * 4 ∈ ({128, 192, 256} : Finset ℕ) ∧
    (P.gamma1 = 2 ^ 17 ∨ P.gamma1 = 2 ^ 19) ∧ P.zPackedBytes = 32 * (1 + bitlen (P.gamma1 - 1)) := by
  rcases hP with rfl | rfl | rfl <;> decide

end OcamlPq.MLDSAAlg
