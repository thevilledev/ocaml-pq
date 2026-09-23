import OcamlPq.MLKEMAlg.Basic

/-!
# ML-KEM parameter sets and sizes

Models the functor argument and size constants of lib/mlkem_engine.ml
(lines 10-16, 58-75, 527-549) and checks them against FIPS 203 Table 2
(parameter sets) and Table 3 (sizes of keys and ciphertexts).
-/

namespace OcamlPq.MLKEMAlg

/-- The functor argument `P : PARAMETERS` (lib/mlkem_engine.ml:10-16). -/
structure Params where
  k : ℕ
  eta1 : ℕ
  eta2 : ℕ
  du : ℕ
  dv : ℕ
  deriving DecidableEq, Repr

/-- `Mlkem512 = Make (struct let k = 2 ... end)` (lib/mlkem_engine.ml:527-533). -/
def mlkem512 : Params := ⟨2, 3, 2, 10, 4⟩

/-- `Mlkem768` (lib/mlkem_engine.ml:535-541). -/
def mlkem768 : Params := ⟨3, 2, 2, 10, 4⟩

/-- `Mlkem1024` (lib/mlkem_engine.ml:543-549). -/
def mlkem1024 : Params := ⟨4, 2, 2, 11, 5⟩

namespace Params

variable (P : Params)

/-- `encoding_size_12` (lib/mlkem_engine.ml:67). -/
def encodingSize12 : ℕ := 384

/-- `encoding_size_u = n * du / 8` (lib/mlkem_engine.ml:68). -/
def encodingSizeU : ℕ := n * P.du / 8

/-- `encoding_size_v = n * dv / 8` (lib/mlkem_engine.ml:69). -/
def encodingSizeV : ℕ := n * P.dv / 8

/-- `seed_size` (lib/mlkem_engine.ml:70). -/
def seedSize : ℕ := 64

/-- `encapsulation_key_size` (lib/mlkem_engine.ml:71). -/
def ekSize : ℕ := P.k * encodingSize12 + 32

/-- `expanded_decapsulation_key_size` (lib/mlkem_engine.ml:72-73). -/
def dkSize : ℕ := P.k * encodingSize12 + P.ekSize + 64

/-- `ciphertext_size` (lib/mlkem_engine.ml:74). -/
def ctSize : ℕ := P.k * P.encodingSizeU + P.encodingSizeV

/-- `shared_secret_size` (lib/mlkem_engine.ml:75). -/
def ssSize : ℕ := 32

/-- The parameter sets the library instantiates. -/
def Valid : Prop := P = mlkem512 ∨ P = mlkem768 ∨ P = mlkem1024

/-- The facts about a valid parameter set that the proofs use. -/
structure Bounds : Prop where
  k_pos : 1 ≤ P.k
  k_le : P.k ≤ 4
  eta1 : P.eta1 = 2 ∨ P.eta1 = 3
  eta2 : P.eta2 = 2 ∨ P.eta2 = 3
  du_pos : 1 ≤ P.du
  du_le : P.du ≤ 11
  dv_pos : 1 ≤ P.dv
  dv_le : P.dv ≤ 11

theorem Valid.bounds {P : Params} (h : P.Valid) : P.Bounds := by
  rcases h with rfl | rfl | rfl <;> constructor <;> decide

end Params

/-! ## FIPS 203 Table 2 and Table 3 -/

/-- A row of FIPS 203 Table 2. -/
structure FipsParamSet where
  k : ℕ
  eta1 : ℕ
  eta2 : ℕ
  du : ℕ
  dv : ℕ

/-- FIPS 203 Table 2, ML-KEM-512. -/
def fips512 : FipsParamSet := { k := 2, eta1 := 3, eta2 := 2, du := 10, dv := 4 }
/-- FIPS 203 Table 2, ML-KEM-768. -/
def fips768 : FipsParamSet := { k := 3, eta1 := 2, eta2 := 2, du := 10, dv := 4 }
/-- FIPS 203 Table 2, ML-KEM-1024. -/
def fips1024 : FipsParamSet := { k := 4, eta1 := 2, eta2 := 2, du := 11, dv := 5 }

/-- FIPS 203 Table 3: encapsulation key size `384k + 32`. -/
def FipsParamSet.ekSize (F : FipsParamSet) : ℕ := 384 * F.k + 32
/-- FIPS 203 Table 3: decapsulation key size `768k + 96`. -/
def FipsParamSet.dkSize (F : FipsParamSet) : ℕ := 768 * F.k + 96
/-- FIPS 203 Table 3: ciphertext size `32(du·k + dv)`. -/
def FipsParamSet.ctSize (F : FipsParamSet) : ℕ := 32 * (F.du * F.k + F.dv)

def Params.fips (P : Params) : FipsParamSet := ⟨P.k, P.eta1, P.eta2, P.du, P.dv⟩

theorem params_table2 :
    mlkem512.fips = fips512 ∧ mlkem768.fips = fips768 ∧ mlkem1024.fips = fips1024 := by
  refine ⟨rfl, rfl, rfl⟩

/-- For every parameter set, the code's size formulas agree with FIPS 203
    Table 3 (the divisions `n * d / 8` are exact). -/
theorem sizes_eq_fips (P : Params) :
    P.encodingSizeU = 32 * P.du ∧ P.encodingSizeV = 32 * P.dv ∧
    P.ekSize = P.fips.ekSize ∧ P.dkSize = P.fips.dkSize ∧ P.ctSize = P.fips.ctSize := by
  simp only [Params.encodingSizeU, Params.encodingSizeV, Params.ekSize, Params.dkSize,
    Params.ctSize, Params.encodingSize12, FipsParamSet.ekSize, FipsParamSet.dkSize,
    FipsParamSet.ctSize, Params.fips, n]
  refine ⟨by omega, by omega, by ring, by ring, ?_⟩
  have h1 : 256 * P.du / 8 = 32 * P.du := by omega
  have h2 : 256 * P.dv / 8 = 32 * P.dv := by omega
  rw [h1, h2]; ring

/-- The concrete sizes (bytes) of FIPS 203 Table 3. -/
theorem sizes_concrete :
    (mlkem512.ekSize, mlkem512.dkSize, mlkem512.ctSize) = (800, 1632, 768) ∧
    (mlkem768.ekSize, mlkem768.dkSize, mlkem768.ctSize) = (1184, 2400, 1088) ∧
    (mlkem1024.ekSize, mlkem1024.dkSize, mlkem1024.ctSize) = (1568, 3168, 1568) ∧
    fips512.ekSize = 800 ∧ fips512.dkSize = 1632 ∧ fips512.ctSize = 768 ∧
    fips768.ekSize = 1184 ∧ fips768.dkSize = 2400 ∧ fips768.ctSize = 1088 ∧
    fips1024.ekSize = 1568 ∧ fips1024.dkSize = 3168 ∧ fips1024.ctSize = 1568 := by
  decide

/-- Every size constant is a portable `int`. -/
theorem sizes_portable (P : Params) (h : P.Bounds) :
    Portable (P.ekSize : ℤ) ∧ Portable (P.dkSize : ℤ) ∧ Portable (P.ctSize : ℤ) ∧
    Portable ((n * P.du : ℕ) : ℤ) ∧ Portable ((n * P.dv : ℕ) : ℤ) := by
  obtain ⟨-, hk, -, -, -, hdu, -, hdv⟩ := h
  obtain ⟨h1, h2, -, -, -⟩ := sizes_eq_fips P
  simp only [Params.ctSize, Params.dkSize, Params.ekSize, Params.encodingSize12, h1, h2]
  refine ⟨Portable.of_nat_lt ?_, Portable.of_nat_lt ?_, Portable.of_nat_lt ?_,
    Portable.of_nat_lt ?_, Portable.of_nat_lt ?_⟩ <;> nlinarith

theorem Params.ekSize_eq (P : Params) : P.ekSize = 384 * P.k + 32 := by
  simp [Params.ekSize, Params.encodingSize12]; ring

theorem Params.dkSize_eq (P : Params) : P.dkSize = 768 * P.k + 96 := by
  simp [Params.dkSize, Params.ekSize, Params.encodingSize12]; ring

theorem Params.encodingSizeU_eq (P : Params) : P.encodingSizeU = 32 * P.du := (sizes_eq_fips P).1

theorem Params.encodingSizeV_eq (P : Params) : P.encodingSizeV = 32 * P.dv := (sizes_eq_fips P).2.1

theorem Params.ctSize_eq (P : Params) : P.ctSize = P.k * (32 * P.du) + 32 * P.dv := by
  simp [Params.ctSize, Params.encodingSizeU_eq, Params.encodingSizeV_eq]

end OcamlPq.MLKEMAlg
