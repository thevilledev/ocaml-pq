import OcamlPq.Hash.Sha2Spec
import OcamlPq.Hash.Sha2Model

/-!
# SHA-2 constants, derived

`sha256Constants_eq`, `sha512Constants_eq`, `sha256H0_eq`, `sha512H0_eq`:
the OCaml tables are FIPS 180-4's `K` and `H(0)` as defined in `Sha2Spec`
(fractional parts of real cube/square roots of `Nat.nth Nat.Prime t`).

Method: `fracRootBits_eq` shows that if an integer `r` satisfies
`r^k ≤ p·2^(k·bits) < (r+1)^k` (so `r = ⌊p^(1/k)·2^bits⌋`), then the first
`bits` bits of the fractional part of `p^(1/k)` are `r mod 2^bits`. The
inequalities for `r = ⌊p^(1/k)⌋·2^bits + c` are then checked in the kernel for
every table entry `c`, and `Nat.nth Nat.Prime t` is identified with an
explicit list of the first 80 primes by counting primes (`nth_prime_eq`).
-/

namespace OcamlPq.Hash.Sha2

open FIPS180

/-! ## Real roots -/

/-- If `r^k ≤ p·2^(k·bits) < (r+1)^k` then `⌊frac(p^(1/k))·2^bits⌋ = r mod 2^bits`. -/
theorem fracRootBits_eq (k bits p r : ℕ) (hk : 0 < k)
    (h1 : r ^ k ≤ p * 2 ^ (k * bits)) (h2 : p * 2 ^ (k * bits) < (r + 1) ^ k) :
    fracRootBits k bits p = r % 2 ^ bits := by
  unfold fracRootBits
  set c : ℝ := (p : ℝ) ^ ((1 : ℝ) / k) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hck : c ^ k = p := by
    rw [hc, one_div]; exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)
  set X : ℝ := c * 2 ^ bits with hX
  have hX0 : 0 ≤ X := by positivity
  have hXk : X ^ k = ((p * 2 ^ (k * bits) : ℕ) : ℝ) := by
    rw [hX, mul_pow, hck]; push_cast; ring
  have hlo : (r : ℝ) ≤ X := by
    by_contra h
    rw [not_le] at h
    have h' := pow_lt_pow_left₀ h hX0 (by omega : k ≠ 0)
    rw [hXk] at h'
    have : p * 2 ^ (k * bits) < r ^ k := by exact_mod_cast h'
    omega
  have hhi : X < (r : ℝ) + 1 := by
    by_contra h
    rw [not_lt] at h
    have h' := pow_le_pow_left₀ (by positivity) h k
    rw [hXk] at h'
    have : (r + 1) ^ k ≤ p * 2 ^ (k * bits) := by exact_mod_cast h'
    omega
  have hfloorX : ⌊X⌋₊ = r := (Nat.floor_eq_iff hX0).mpr ⟨hlo, hhi⟩
  have hpow : (0 : ℝ) < 2 ^ bits := by positivity
  have hc_eq : c = X / ((2 ^ bits : ℕ) : ℝ) := by
    rw [hX]; push_cast; field_simp
  have hfloorc : ⌊c⌋₊ = r / 2 ^ bits := by
    rw [hc_eq, Nat.floor_div_natCast, hfloorX]
  have hIntfloor : ((⌊c⌋ : ℤ) : ℝ) = ((r / 2 ^ bits : ℕ) : ℝ) := by
    rw [← hfloorc, ← Int.natCast_floor_eq_floor hc0]; rfl
  have hfr : Int.fract c * 2 ^ bits = X - ((r / 2 ^ bits * 2 ^ bits : ℕ) : ℝ) := by
    rw [Int.fract, sub_mul, hIntfloor, hX]; push_cast; ring
  rw [hfr, Nat.floor_sub_natCast, hfloorX]
  have := Nat.div_add_mod r (2 ^ bits)
  rw [Nat.mul_comm] at this
  omega

/-- `⌊p^(1/k)⌋`, by search (only used to build witnesses). -/
def intRoot (k p : ℕ) : ℕ := ((List.range (p + 1)).filter fun n => n ^ k ≤ p).length - 1

/-- The kernel-checkable certificate: with `r = ⌊p^(1/k)⌋·2^bits + c`,
`r^k ≤ p·2^(k·bits) < (r+1)^k` and `c < 2^bits`. -/
def rootOK (k bits p c : ℕ) : Bool :=
  let r := intRoot k p * 2 ^ bits + c
  decide (r ^ k ≤ p * 2 ^ (k * bits)) && decide (p * 2 ^ (k * bits) < (r + 1) ^ k) &&
    decide (c < 2 ^ bits)

theorem fracRootBits_of_rootOK (k bits p c : ℕ) (hk : 0 < k) (h : rootOK k bits p c = true) :
    fracRootBits k bits p = c := by
  simp only [rootOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [fracRootBits_eq k bits p _ hk h1 h2, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
    Nat.mod_mod, Nat.mod_eq_of_lt h3]

/-! ## The first 80 primes -/

/-- The first 80 primes. -/
def primes80 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
  67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163,
  167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269,
  271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383,
  389, 397, 401, 409]

theorem primes80_length : primes80.length = 80 := rfl

set_option maxRecDepth 100000 in
/-- The primes below 410 are exactly `primes80` (kernel-checked primality of
every `n < 410`). -/
theorem primes_below_410 : (List.range 410).filter Nat.Prime = primes80 := by
  decide +kernel

theorem prime_iff_mem (n : ℕ) (hn : n < 410) : Nat.Prime n ↔ n ∈ primes80 := by
  rw [← primes_below_410]; simp [hn]

set_option maxRecDepth 100000 in
theorem primes80_filter_succ : ∀ n < 410,
    (primes80.filter (· < n + 1)).length =
      (primes80.filter (· < n)).length + if n ∈ primes80 then 1 else 0 := by
  decide +kernel

theorem count_prime_eq (n : ℕ) (hn : n ≤ 410) :
    Nat.count Nat.Prime n = (primes80.filter (· < n)).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.count_succ, ih (by omega), primes80_filter_succ n (by omega)]
    simp only [prime_iff_mem n (by omega)]

set_option maxRecDepth 100000 in
theorem primes80_index : ∀ t : Fin 80,
    (primes80.filter (· < primes80[t.val]'(by rw [primes80_length]; omega))).length = t := by
  decide +kernel

/-- `Nat.nth Nat.Prime t` is the `t`-th entry of `primes80`. -/
theorem nth_prime_eq (t : Fin 80) :
    Nat.nth Nat.Prime t = primes80[t.val]'(by rw [primes80_length]; omega) := by
  have hp : Nat.Prime (primes80[t.val]'(by rw [primes80_length]; omega)) := by
    rw [prime_iff_mem _ (by fin_cases t <;> decide)]; exact List.getElem_mem _
  have hc : Nat.count Nat.Prime (primes80[t.val]'(by rw [primes80_length]; omega)) = t := by
    rw [count_prime_eq _ (by fin_cases t <;> decide), primes80_index]
  have h := Nat.nth_count hp
  rw [hc] at h
  exact h

/-! ## The tables -/

set_option maxRecDepth 100000 in
theorem sha256K_ok : ∀ t : Fin 64,
    rootOK 3 32 (primes80[t.val]'(by rw [primes80_length]; omega)) (sha256Constants[t.val]!).toNat = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sha512K_ok : ∀ t : Fin 80,
    rootOK 3 64 (primes80[t.val]'(by rw [primes80_length]; omega)) (sha512Constants[t.val]!).toNat = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sha256H0_ok : ∀ j : Fin 8,
    rootOK 2 32 (primes80[j.val]'(by rw [primes80_length]; omega)) (sha256H0[j.val]!).toNat = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sha512H0_ok : ∀ j : Fin 8,
    rootOK 2 64 (primes80[j.val]'(by rw [primes80_length]; omega)) (sha512H0[j.val]!).toNat = true := by
  decide +kernel

/-- **SHA-256 `K`.** `sha256_constants.(t)` is FIPS 180-4 `K_t^{256}`: the first
32 bits of the fractional part of the cube root of the `t`-th prime. -/
theorem sha256Constants_eq (t : ℕ) (ht : t < 64) : sha256Constants[t]! = K256 t := by
  have h := fracRootBits_of_rootOK 3 32 _ _ (by norm_num) (sha256K_ok ⟨t, ht⟩)
  rw [K256, nth_prime_eq ⟨t, by omega⟩]
  simp only at h ⊢
  rw [h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- **SHA-512 `K`.** `sha512_constants.(t)` is FIPS 180-4 `K_t^{512}`. -/
theorem sha512Constants_eq (t : ℕ) (ht : t < 80) : sha512Constants[t]! = K512 t := by
  have h := fracRootBits_of_rootOK 3 64 _ _ (by norm_num) (sha512K_ok ⟨t, ht⟩)
  rw [K512, nth_prime_eq ⟨t, ht⟩]
  simp only at h ⊢
  rw [h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- **SHA-256 `H(0)`.** The initial `h` array of `sha256` is FIPS 180-4 §5.3.3:
the first 32 bits of the fractional parts of the square roots of the first 8
primes. -/
theorem sha256H0_eq (j : Fin 8) : sha256H0[j.val]! = H0_256 j := by
  have h := fracRootBits_of_rootOK 2 32 _ _ (by norm_num) (sha256H0_ok j)
  rw [H0_256, nth_prime_eq ⟨j, by omega⟩]
  simp only at h ⊢
  rw [h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- **SHA-512 `H(0)`.** The initial `h` array of `sha512` is FIPS 180-4 §5.3.5. -/
theorem sha512H0_eq (j : Fin 8) : sha512H0[j.val]! = H0_512 j := by
  have h := fracRootBits_of_rootOK 2 64 _ _ (by norm_num) (sha512H0_ok j)
  rw [H0_512, nth_prime_eq ⟨j, by omega⟩]
  simp only at h ⊢
  rw [h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end OcamlPq.Hash.Sha2
