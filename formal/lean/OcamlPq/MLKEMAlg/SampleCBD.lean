import OcamlPq.MLKEMAlg.Params

/-!
# `sample_cbd` refines FIPS 203 Algorithm 8

`sample_cbd eta seed nonce` (lib/mlkem_engine.ml:292-307) computes
`SamplePolyCBD_η(PRF_η(seed, nonce))`.
-/

namespace OcamlPq.MLKEMAlg

/-! ## Specification -/

namespace Spec

/-- The bits of a byte `c`, least significant first: the inner loop of FIPS
    203 Algorithm 4 (`b[8i + j] ← C[i] mod 2; C[i] ← ⌊C[i]/2⌋`). -/
def bitsOfByte : ℕ → ℕ → List ℕ
  | _, 0 => []
  | c, m + 1 => (c % 2) :: bitsOfByte (c / 2) m

/-- FIPS 203 Algorithm 4, `BytesToBits`. -/
def bytesToBits (B : Bytes) : List ℕ := B.flatMap (fun c => bitsOfByte c.val 8)

/-- FIPS 203 Algorithm 8, `SamplePolyCBD_η(B)` for `B ∈ 𝔹^{64η}`:
    `f[i] = (Σ_{j<η} b[2iη + j]) − (Σ_{j<η} b[2iη + η + j]) mod q`. -/
def samplePolyCBD (η : ℕ) (B : Bytes) : Poly :=
  let b := bytesToBits B
  fun i =>
    let x := ∑ j ∈ Finset.range η, b.getD (2 * i.val * η + j) 0
    let y := ∑ j ∈ Finset.range η, b.getD (2 * i.val * η + η + j) 0
    (x : ZMod q) - (y : ZMod q)

/-- FIPS 203 eq. (4.3), `PRF_η(s, b) := SHAKE256(s ‖ b, 8 · 64 · η)`. -/
def prf (K : Keccak) (η : ℕ) (s : Bytes) (b : Byte) : Bytes :=
  List.ofFn (fun i : Fin (64 * η) => K.shake256 (s ++ [b]) i)

end Spec

/-! ## Model -/

/-- The `bit offset` closure of `sample_cbd` (lib/mlkem_engine.ml:297-300). -/
def cbdBit (stream : Bytes) (eta i offset : ℕ) : ℕ :=
  let index := 2 * eta * i + offset
  (getU8 stream (index >>> 3) >>> (index &&& 7)) &&& 1

/-- The `for j = 0 to eta - 1` loop of `sample_cbd` (lib/mlkem_engine.ml:301-304),
    returning the final `(!a, !b)`. -/
def cbdCounts (stream : Bytes) (eta i : ℕ) : ℕ × ℕ :=
  (List.range eta).foldl
    (fun ab j => (ab.1 + cbdBit stream eta i j, ab.2 + cbdBit stream eta i (eta + j))) (0, 0)

/-- `sample_cbd eta seed nonce` (lib/mlkem_engine.ml:292-307). The nonce is an
    OCaml `int`; the callers pass values of a counter starting at 0, so it is
    modelled as `ℕ`. -/
def sampleCbd (K : Keccak) (eta : ℕ) (seed : Bytes) (nonce : ℕ) : IPoly :=
  let stream := K.shake256Out (64 * eta) (seed ++ byteString nonce)
  (List.finRange 256).foldl
    (fun out i =>
      let ab := cbdCounts stream eta i.val
      Function.update out i (fieldSub ab.1 ab.2))
    polyZero

/-! ## Proofs -/

theorem bitsOfByte_length (c m : ℕ) : (Spec.bitsOfByte c m).length = m := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih => simp [Spec.bitsOfByte, ih]

theorem bitsOfByte_getD (c m r : ℕ) (hr : r < m) :
    (Spec.bitsOfByte c m).getD r 0 = c / 2 ^ r % 2 := by
  induction m generalizing c r with
  | zero => omega
  | succ m ih =>
    cases r with
    | zero => simp [Spec.bitsOfByte]
    | succ r =>
      simp only [Spec.bitsOfByte, List.getD_cons_succ]
      rw [ih _ _ (by omega), Nat.div_div_eq_div_mul, pow_succ']

/-- Bit `8a + r` of `BytesToBits(B)` is bit `r` of byte `a`. -/
theorem bytesToBits_getD (B : Bytes) (a r : ℕ) (ha : a < B.length) (hr : r < 8) :
    (Spec.bytesToBits B).getD (8 * a + r) 0 = (B[a]'ha).val / 2 ^ r % 2 := by
  induction B generalizing a with
  | nil => simp at ha
  | cons c B ih =>
    simp only [Spec.bytesToBits, List.flatMap_cons] at ih ⊢
    cases a with
    | zero =>
      simp only [List.getD_eq_getElem?_getD, mul_zero, zero_add, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by rw [bitsOfByte_length]; omega)]
      rw [← List.getD_eq_getElem?_getD, bitsOfByte_getD _ _ _ hr]
    | succ a =>
      simp only [List.getD_eq_getElem?_getD, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [bitsOfByte_length]; omega), bitsOfByte_length,
        show 8 * (a + 1) + r - 8 = 8 * a + r by omega]
      rw [← List.getD_eq_getElem?_getD]
      exact ih a (by simp at ha; omega)

theorem land7 (x : ℕ) : x &&& 7 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3
theorem land1 (x : ℕ) : x &&& 1 = x % 2 := Nat.and_two_pow_sub_one_eq_mod x 1

/-- The implementation's bit extraction reads bit `index` of `BytesToBits`. -/
theorem cbdBit_eq (B : Bytes) (eta i offset : ℕ) (h : (2 * eta * i + offset) / 8 < B.length) :
    cbdBit B eta i offset = (Spec.bytesToBits B).getD (2 * i * eta + offset) 0 := by
  have hidx : 2 * i * eta + offset = 8 * ((2 * eta * i + offset) / 8) + (2 * eta * i + offset) % 8 := by
    rw [show 2 * i * eta = 2 * eta * i by ring]; omega
  rw [hidx, bytesToBits_getD B _ _ h (Nat.mod_lt _ (by norm_num))]
  simp only [cbdBit, Nat.shiftRight_eq_div_pow, land7, land1]
  rw [getU8_of_lt h]

theorem cbdBit_le (B : Bytes) (eta i offset : ℕ) : cbdBit B eta i offset ≤ 1 := by
  simp only [cbdBit, land1]
  omega

theorem cbdCounts_eq_aux (f g : ℕ → ℕ) (m : ℕ) (a0 b0 : ℕ) :
    (List.range m).foldl (fun ab j => (ab.1 + f j, ab.2 + g j)) (a0, b0) =
      (a0 + ∑ j ∈ Finset.range m, f j, b0 + ∑ j ∈ Finset.range m, g j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [Finset.sum_range_succ, Nat.add_assoc]

theorem cbdCounts_eq (stream : Bytes) (eta i : ℕ) :
    cbdCounts stream eta i =
      (∑ j ∈ Finset.range eta, cbdBit stream eta i j,
       ∑ j ∈ Finset.range eta, cbdBit stream eta i (eta + j)) := by
  simp only [cbdCounts]
  rw [cbdCounts_eq_aux]; simp

theorem cbdCounts_le (stream : Bytes) (eta i : ℕ) :
    (cbdCounts stream eta i).1 ≤ eta ∧ (cbdCounts stream eta i).2 ≤ eta := by
  rw [cbdCounts_eq]
  constructor
  · calc _ ≤ ∑ _j ∈ Finset.range eta, 1 := Finset.sum_le_sum fun j _ => cbdBit_le _ _ _ _
      _ = eta := by simp
  · calc _ ≤ ∑ _j ∈ Finset.range eta, 1 := Finset.sum_le_sum fun j _ => cbdBit_le _ _ _ _
      _ = eta := by simp

/-- The coefficient written by iteration `i` of `sample_cbd`. -/
theorem sampleCbd_apply (K : Keccak) (eta : ℕ) (seed : Bytes) (nonce : ℕ) (i : Fin 256) :
    sampleCbd K eta seed nonce i =
      fieldSub (cbdCounts (K.shake256Out (64 * eta) (seed ++ byteString nonce)) eta i.val).1
        (cbdCounts (K.shake256Out (64 * eta) (seed ++ byteString nonce)) eta i.val).2 := by
  unfold sampleCbd
  rw [foldl_update_finRange (fun i : Fin 256 => fieldSub
      (cbdCounts (K.shake256Out (64 * eta) (seed ++ byteString nonce)) eta i.val).1
      (cbdCounts (K.shake256Out (64 * eta) (seed ++ byteString nonce)) eta i.val).2)]

/-- **Obligation 1.** For `η ∈ {2, 3}` and a nonce that fits in a byte,
    `sample_cbd η seed nonce` has canonical coefficients and equals FIPS 203
    `SamplePolyCBD_η(PRF_η(seed, nonce))`. -/
theorem sampleCbd_spec (K : Keccak) (eta : ℕ) (heta : eta = 2 ∨ eta = 3) (seed : Bytes)
    (nonce : ℕ) (hnonce : nonce < 256) :
    Canonical (sampleCbd K eta seed nonce) ∧
      toSpec (sampleCbd K eta seed nonce) =
        Spec.samplePolyCBD eta (Spec.prf K eta seed ⟨nonce, hnonce⟩) := by
  have heta3 : eta ≤ 3 := by omega
  set stream := K.shake256Out (64 * eta) (seed ++ byteString nonce) with hstream
  have hprf : Spec.prf K eta seed ⟨nonce, hnonce⟩ = stream := by
    have hc : unsafeChr (nonce : ℤ) = ⟨nonce, hnonce⟩ := Fin.ext (unsafeChr_val_nat hnonce)
    simp only [Spec.prf, hstream, Keccak.shake256Out, byteString, hc]
  constructor
  · intro i
    rw [sampleCbd_apply]
    obtain ⟨h1, h2⟩ := cbdCounts_le stream eta i.val
    obtain ⟨-, h3, h4, -, -⟩ := fieldSub_small (cbdCounts stream eta i.val).1
      (cbdCounts stream eta i.val).2 (by omega) (by omega)
    exact ⟨h3, h4⟩
  · funext i
    rw [hprf]
    simp only [toSpec, sampleCbd_apply, ← hstream]
    obtain ⟨h1, h2⟩ := cbdCounts_le stream eta i.val
    obtain ⟨hs, -⟩ := fieldSub_small (cbdCounts stream eta i.val).1
      (cbdCounts stream eta i.val).2 (by omega) (by omega)
    rw [hs, ZMod.intCast_mod]
    simp only [Int.cast_sub, Int.cast_natCast, cbdCounts_eq, Spec.samplePolyCBD]
    have hlen : stream.length = 64 * eta := by simp [hstream]
    have hbit : ∀ j < 2 * eta, cbdBit stream eta i.val j =
        (Spec.bytesToBits stream).getD (2 * i.val * eta + j) 0 := by
      intro j hj
      apply cbdBit_eq
      rw [hlen]; have := i.isLt; nlinarith [Nat.div_mul_le_self (2 * eta * i.val + j) 8]
    congr 2
    · exact Finset.sum_congr rfl fun j hj => by
        rw [hbit j (by simp at hj; omega)]
    · exact Finset.sum_congr rfl fun j hj => by
        rw [hbit (eta + j) (by simp at hj; omega), Nat.add_assoc]

/-- **Obligation 7 (sample_cbd).** Every `int` intermediate of `sample_cbd`
    is portable and every string access is in bounds, for `η ≤ 3`, `i < 256`,
    `j < 2η` and `nonce < 256`: the output length `64η`, the nonce passed to
    `Char.unsafe_chr`, the bit index and its byte offset (which is below the
    stream length), the counts and the argument of `field_sub`. -/
theorem sampleCbd_portable (eta i j nonce : ℕ) (heta : eta ≤ 3) (hi : i < 256) (hj : j < 2 * eta)
    (hnonce : nonce < 256) (stream : Bytes) :
    Portable ((64 * eta : ℕ) : ℤ) ∧ (0 ≤ (nonce : ℤ) ∧ (nonce : ℤ) < 256) ∧
    Portable ((2 * eta * i + j : ℕ) : ℤ) ∧ (2 * eta * i + j) >>> 3 < 64 * eta ∧
    Portable ((cbdCounts stream eta i).1 : ℤ) ∧ Portable ((cbdCounts stream eta i).2 : ℤ) ∧
    Portable (((cbdCounts stream eta i).1 : ℤ) - (cbdCounts stream eta i).2 + q) := by
  obtain ⟨h1, h2⟩ := cbdCounts_le stream eta i
  refine ⟨Portable.of_nat_lt (by omega), ⟨by omega, by omega⟩, Portable.of_nat_lt (by nlinarith),
    ?_, Portable.of_nat_lt (by omega), Portable.of_nat_lt (by omega),
    (fieldSub_small (cbdCounts stream eta i).1 (cbdCounts stream eta i).2
      (by omega) (by omega)).2.2.2.1⟩
  rw [Nat.shiftRight_eq_div_pow]
  have : 2 * eta * i + j < 8 * (64 * eta) := by nlinarith
  omega

end OcamlPq.MLKEMAlg
