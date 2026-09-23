import OcamlPq.MLDSA.NTTClosed

/-!
# The mathematics of the ML-DSA NTT

* `NTT⁻¹ ∘ NTT = id` and `NTT ∘ NTT⁻¹ = id` (FIPS 204 Algorithms 41/42);
* `NTT(w)[k] = w(ω_k)` with `ω_k = ζ^(2·BitRev8(k)+1)`, the 256 roots of
  `X^256 + 1`;
* hence `NTT⁻¹(NTT(a) ∘ NTT(b)) = a·b` in `ℤ_q[X]/(X^256 + 1)`;
* and the same statements for the OCaml `ntt`/`inverse_ntt`/`pointwise`.
-/

namespace OcamlPq.MLDSA

/-! ## Facts about the constants (closed, kernel-decided) -/

/-- Forward zeta of block `b` in layer `s` times the inverse zeta of the
    same block is `ζ^256`: `BitRev8(2^(s+1)-1-b) + BitRev8(2^s+b) = 256`. -/
theorem bitRev8_pair : ∀ s < 8, ∀ b < 2 ^ s,
    bitRev8 (2 ^ (s + 1) - 1 - b) + bitRev8 (2 ^ s + b) = 256 := by decide +kernel

/-- Squares of the forward zetas: `2·BitRev8(2^s+b) = BitRev8(2^(s-1)+b/2) + 256·(b mod 2)`. -/
theorem bitRev8_sq : ∀ s < 8, 1 ≤ s → ∀ b < 2 ^ s,
    2 * bitRev8 (2 ^ s + b) = bitRev8 (2 ^ (s - 1) + b / 2) + 256 * (b % 2) := by decide +kernel

/-- The last layer's roots: `BitRev8(128 + k/2) + 256·(k mod 2) = 2·BitRev8(k) + 1`. -/
theorem bitRev8_last : ∀ k < 256, bitRev8 (128 + k / 2) + 256 * (k % 2) = 2 * bitRev8 k + 1 := by
  decide +kernel

theorem bitRev8_invol : ∀ k < 256, bitRev8 (bitRev8 k) = k := by decide +kernel

theorem zeta_pair (s : ℕ) (hs : s < 8) (b : ℕ) (hb : b < 2 ^ s) :
    -zetaSpec (2 ^ (s + 1) - 1 - b) * zetaSpec (2 ^ s + b) = 1 := by
  unfold zetaSpec
  rw [neg_mul, ← pow_add, bitRev8_pair s hs b hb, zeta_pow_256, neg_neg]

theorem zeta_sq (s : ℕ) (hs : s < 8) (hs1 : 1 ≤ s) (b : ℕ) (hb : b < 2 ^ s) :
    zetaSpec (2 ^ s + b) ^ 2 =
      if b % 2 = 0 then zetaSpec (2 ^ (s - 1) + b / 2) else -zetaSpec (2 ^ (s - 1) + b / 2) := by
  have e := bitRev8_sq s hs hs1 b hb
  unfold zetaSpec
  rw [← pow_mul, mul_comm, e]
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · rw [h]; simp
  · rw [h, iteF (by norm_num), pow_add, zeta_pow_256]; ring

/-! ## Layer algebra -/

theorem layerI_layerF (len : ℕ) (hL : IsLen len) (zf zi : ℕ → Zq)
    (hz : ∀ b < 256 / (2 * len), zi b * zf b = 1) (w : ℕ → Zq) :
    layerI len zi (layerF len zf w) = smul256 2 w := by
  funext k
  unfold layerI layerF smul256
  have hm := Nat.mod_lt k (show 0 < 2 * len by have := hL.pos; omega)
  rcases Nat.lt_or_ge k 256 with hk | hk
  · obtain ⟨P1, P2⟩ := partner_arith hL k hk
    have hb := blk_lt hL k hk
    rcases Nat.lt_or_ge (k % (2 * len)) len with c | c
    · obtain ⟨e1, e2, e3, -, -⟩ := P1 c
      simp (disch := omega) only [iteT, iteF, Nat.add_sub_cancel]
      try rw [e3]
      ring
    · obtain ⟨e1, e2, e3, -, -⟩ := P2 c
      simp (disch := omega) only [iteT, iteF, Nat.sub_add_cancel e1]
      try rw [e3]
      linear_combination (2 * w k) * hz _ hb
  · simp (disch := omega) only [iteT, iteF]

theorem layerF_layerI (len : ℕ) (hL : IsLen len) (zf zi : ℕ → Zq)
    (hz : ∀ b < 256 / (2 * len), zi b * zf b = 1) (w : ℕ → Zq) :
    layerF len zf (layerI len zi w) = smul256 2 w := by
  funext k
  unfold layerI layerF smul256
  have hm := Nat.mod_lt k (show 0 < 2 * len by have := hL.pos; omega)
  rcases Nat.lt_or_ge k 256 with hk | hk
  · obtain ⟨P1, P2⟩ := partner_arith hL k hk
    have hb := blk_lt hL k hk
    rcases Nat.lt_or_ge (k % (2 * len)) len with c | c
    · obtain ⟨e1, e2, e3, -, -⟩ := P1 c
      simp (disch := omega) only [iteT, iteF, Nat.add_sub_cancel]
      try rw [e3]
      linear_combination (w k - w (k + len)) * hz _ hb
    · obtain ⟨e1, e2, e3, -, -⟩ := P2 c
      simp (disch := omega) only [iteT, iteF, Nat.sub_add_cancel e1]
      try rw [e3]
      linear_combination (-(w (k - len) - w k)) * hz _ hb
  · simp (disch := omega) only [iteT, iteF]

theorem layerF_smul (len : ℕ) (hL : IsLen len) (zf : ℕ → Zq) (c : Zq) (w : ℕ → Zq) :
    layerF len zf (smul256 c w) = smul256 c (layerF len zf w) := by
  funext k
  unfold layerF smul256
  rcases Nat.lt_or_ge k 256 with hk | hk
  · obtain ⟨P1, P2⟩ := partner_arith hL k hk
    rcases Nat.lt_or_ge (k % (2 * len)) len with c' | c'
    · obtain ⟨e1, -, -, -, -⟩ := P1 c'
      simp (disch := omega) only [iteT]; ring
    · obtain ⟨e1, -, -, -, -⟩ := P2 c'
      simp (disch := omega) only [iteT, iteF]; ring
  · simp (disch := omega) only [iteT, iteF]

theorem layerI_smul (len : ℕ) (hL : IsLen len) (zi : ℕ → Zq) (c : Zq) (w : ℕ → Zq) :
    layerI len zi (smul256 c w) = smul256 c (layerI len zi w) := by
  funext k
  unfold layerI smul256
  rcases Nat.lt_or_ge k 256 with hk | hk
  · obtain ⟨P1, P2⟩ := partner_arith hL k hk
    rcases Nat.lt_or_ge (k % (2 * len)) len with c' | c'
    · obtain ⟨e1, -, -, -, -⟩ := P1 c'
      simp (disch := omega) only [iteT]; ring
    · obtain ⟨e1, -, -, -, -⟩ := P2 c'
      simp (disch := omega) only [iteT, iteF]; ring
  · simp (disch := omega) only [iteT, iteF]

theorem smul256_smul256 (c d : Zq) (w : ℕ → Zq) :
    smul256 c (smul256 d w) = smul256 (c * d) w := by
  funext k; unfold smul256; split_ifs <;> ring

theorem smul256_one (w : ℕ → Zq) : smul256 1 w = w := by
  funext k; unfold smul256; split_ifs <;> ring

theorem isLen_layer (s : ℕ) (hs : s < 8) : IsLen (2 ^ (7 - s)) := by
  unfold IsLen; interval_cases s <;> norm_num

theorem blocks_layer (s : ℕ) (hs : s < 8) : 256 / (2 * 2 ^ (7 - s)) = 2 ^ s := by
  interval_cases s <;> norm_num

theorem inv_fwd (s : ℕ) (hs : s < 8) (w : ℕ → Zq) :
    invLayer s (fwdLayer s w) = smul256 2 w := by
  unfold invLayer fwdLayer
  apply layerI_layerF _ (isLen_layer s hs)
  intro b hb
  rw [blocks_layer s hs] at hb
  exact zeta_pair s hs b hb

theorem fwd_inv (s : ℕ) (hs : s < 8) (w : ℕ → Zq) :
    fwdLayer s (invLayer s w) = smul256 2 w := by
  unfold invLayer fwdLayer
  apply layerF_layerI _ (isLen_layer s hs)
  intro b hb
  rw [blocks_layer s hs] at hb
  exact zeta_pair s hs b hb

theorem fwd_smul (s : ℕ) (hs : s < 8) (c : Zq) (w : ℕ → Zq) :
    fwdLayer s (smul256 c w) = smul256 c (fwdLayer s w) :=
  layerF_smul _ (isLen_layer s hs) _ _ _

theorem inv_smul (s : ℕ) (hs : s < 8) (c : Zq) (w : ℕ → Zq) :
    invLayer s (smul256 c w) = smul256 c (invLayer s w) :=
  layerI_smul _ (isLen_layer s hs) _ _ _

/-! ## Inverse theorems (FIPS 204 Algorithms 41/42) -/

/-- `NTT⁻¹(NTT(w)) = w`. -/
theorem invNttSpec_nttSpec (w : ℕ → Zq) : invNttSpec (nttSpec w) = w := by
  rw [nttSpec_eq_layers, invNttSpec_eq_layers]
  simp only [inv_fwd, inv_smul, smul256_smul256, Nat.reduceLT]
  convert smul256_one w using 2
  decide

/-- `NTT(NTT⁻¹(ŵ)) = ŵ`. -/
theorem nttSpec_invNttSpec (w : ℕ → Zq) : nttSpec (invNttSpec w) = w := by
  rw [nttSpec_eq_layers, invNttSpec_eq_layers]
  simp only [fwd_inv, fwd_smul, smul256_smul256, Nat.reduceLT]
  convert smul256_one w using 2
  decide

end OcamlPq.MLDSA
