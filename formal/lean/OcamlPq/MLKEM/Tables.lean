import OcamlPq.MLKEM.Field

/-!
# ML-KEM NTT constant tables

The `zetas` and `gammas` tables of `lib/mlkem_engine.ml` (lines 147–169)
checked against FIPS 203 §4.3: `zetas.(i) = ζ^BitRev7(i) mod q` and
`gammas.(i) = ζ^(2·BitRev7(i)+1) mod q` with `ζ = 17`, together with the
facts about `ζ` that the NTT proofs need: `ζ` is a primitive 256-th root of
unity and `3303 = 128⁻¹` in `ℤ_q`.

All finite checks are by kernel evaluation (`decide` / `decide +kernel`).
-/

namespace OcamlPq.MLKEM

/-- FIPS 203 §2.3: `BitRev7(r) = r₆ + 2r₅ + 4r₄ + 8r₃ + 16r₂ + 32r₁ + 64r₀` for
    `r = r₀ + 2r₁ + ⋯ + 64r₆`. -/
def bitRev7 (r : ℕ) : ℕ :=
  (r / 64) % 2 + 2 * ((r / 32) % 2) + 4 * ((r / 16) % 2) + 8 * ((r / 8) % 2) +
    16 * ((r / 4) % 2) + 32 * ((r / 2) % 2) + 64 * (r % 2)

/-- `ζ = 17`, the primitive 256-th root of unity of FIPS 203 §4.3. -/
def zeta : Zq := 17

/-- The table `zetas` (`lib/mlkem_engine.ml` lines 147–157), copied verbatim. -/
def zetasTable : Array ℤ := #[
    1, 1729, 2580, 3289, 2642, 630, 1897, 848, 1062, 1919, 193, 797, 2786, 3260, 569, 1746,
    296, 2447, 1339, 1476, 3046, 56, 2240, 1333, 1426, 2094, 535, 2882, 2393, 2879, 1974, 821,
    289, 331, 3253, 1756, 1197, 2304, 2277, 2055, 650, 1977, 2513, 632, 2865, 33, 1320, 1915,
    2319, 1435, 807, 452, 1438, 2868, 1534, 2402, 2647, 2617, 1481, 648, 2474, 3110, 1227, 910,
    17, 2761, 583, 2649, 1637, 723, 2288, 1100, 1409, 2662, 3281, 233, 756, 2156, 3015, 3050,
    1703, 1651, 2789, 1789, 1847, 952, 1461, 2687, 939, 2308, 2437, 2388, 733, 2337, 268, 641,
    1584, 2298, 2037, 3220, 375, 2549, 2090, 1645, 1063, 319, 2773, 757, 2099, 561, 2466, 2594,
    2804, 1092, 403, 1026, 1143, 2150, 2775, 886, 1722, 1212, 1874, 1029, 2110, 2935, 885, 2154]

/-- The table `gammas` (`lib/mlkem_engine.ml` lines 159–169), copied verbatim. -/
def gammasTable : Array ℤ := #[
    17, 3312, 2761, 568, 583, 2746, 2649, 680, 1637, 1692, 723, 2606, 2288, 1041, 1100, 2229,
    1409, 1920, 2662, 667, 3281, 48, 233, 3096, 756, 2573, 2156, 1173, 3015, 314, 3050, 279,
    1703, 1626, 1651, 1678, 2789, 540, 1789, 1540, 1847, 1482, 952, 2377, 1461, 1868, 2687, 642,
    939, 2390, 2308, 1021, 2437, 892, 2388, 941, 733, 2596, 2337, 992, 268, 3061, 641, 2688,
    1584, 1745, 2298, 1031, 2037, 1292, 3220, 109, 375, 2954, 2549, 780, 2090, 1239, 1645, 1684,
    1063, 2266, 319, 3010, 2773, 556, 757, 2572, 2099, 1230, 561, 2768, 2466, 863, 2594, 735,
    2804, 525, 1092, 2237, 403, 2926, 1026, 2303, 1143, 2186, 2150, 1179, 2775, 554, 886, 2443,
    1722, 1607, 1212, 2117, 1874, 1455, 1029, 2300, 2110, 1219, 2935, 394, 885, 2444, 2154, 1175]

theorem zetasTable_size : zetasTable.size = 128 := by decide +kernel

theorem gammasTable_size : gammasTable.size = 128 := by decide +kernel

theorem bitRev7_lt : ∀ i < 128, bitRev7 i < 128 := by decide +kernel

/-- `BitRev7` is an involution on `[0, 128)`. -/
theorem bitRev7_bitRev7 : ∀ i < 128, bitRev7 (bitRev7 i) = i := by decide +kernel

/-- Each table entry is `17^BitRev7(i) mod q`. -/
theorem zetasTable_eq : ∀ i < 128, zetasTable[i]? = some ((17 ^ bitRev7 i % 3329 : ℕ) : ℤ) := by
  decide +kernel

/-- Each table entry is `17^(2·BitRev7(i)+1) mod q`. -/
theorem gammasTable_eq :
    ∀ i < 128, gammasTable[i]? = some ((17 ^ (2 * bitRev7 i + 1) % 3329 : ℕ) : ℤ) := by
  decide +kernel

theorem natCast_pow_mod_zq (k : ℕ) : ((((17 ^ k % 3329 : ℕ) : ℤ)) : Zq) = zeta ^ k := by
  rw [Int.cast_natCast, ZMod.natCast_mod]; push_cast; rfl

theorem canon_natCast_mod (m : ℕ) : Canon ((m % 3329 : ℕ) : ℤ) := by
  unfold Canon q; omega

/-- `zetas.(i)` is in bounds, canonical, and equal to `ζ^BitRev7(i)` in `ℤ_q`. -/
theorem zetasTable_get {i : ℕ} (hi : i < 128) :
    ∃ v, zetasTable[i]? = some v ∧ Canon v ∧ (v : Zq) = zeta ^ bitRev7 i :=
  ⟨_, zetasTable_eq i hi, canon_natCast_mod _, natCast_pow_mod_zq _⟩

/-- `gammas.(i)` is in bounds, canonical, and equal to `ζ^(2·BitRev7(i)+1)`. -/
theorem gammasTable_get {i : ℕ} (hi : i < 128) :
    ∃ v, gammasTable[i]? = some v ∧ Canon v ∧ (v : Zq) = zeta ^ (2 * bitRev7 i + 1) :=
  ⟨_, gammasTable_eq i hi, canon_natCast_mod _, natCast_pow_mod_zq _⟩

/-- `3303 = 128⁻¹` in `ℤ_q` (the scaling constant of `inverse_ntt`, line 214). -/
theorem inv128 : (3303 : Zq) * 128 = 1 := by decide

theorem zeta_pow_128 : zeta ^ 128 = -1 := by unfold zeta; decide +kernel

theorem zeta_pow_256 : zeta ^ 256 = 1 := by unfold zeta; decide +kernel

/-- `ζ = 17` has multiplicative order exactly 256 in `ℤ_q`. -/
theorem zeta_orderOf : orderOf zeta = 256 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 7) (x := zeta)
    (by rw [show 2 ^ 7 = 128 by rfl, zeta_pow_128]; decide)
    (by rw [show 2 ^ (7 + 1) = 256 by rfl]; exact zeta_pow_256)
  simpa using h

/-- `ζ = 17` is a primitive 256-th root of unity in `ℤ_q` (FIPS 203 §4.3). -/
theorem zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 256 := by
  have := IsPrimitiveRoot.orderOf zeta
  rwa [zeta_orderOf] at this

end OcamlPq.MLKEM
