import OcamlPq.Hash.KeccakModel
import OcamlPq.Hash.KeccakSpec

/-!
# Keccak constants, derived

* `roundConstants_eq_RC`: every bit of `round_constants.(ir)`
  (`lib/keccak.ml` lines 1–15) is the FIPS 202 `RC[z]` of Algorithm 6, computed
  from the `rc(t)` LFSR of Algorithm 5.
* `rho_eq`: FIPS 202 ρ (Algorithm 2, transcribed as its `t`-loop) rotates
  lane `(x, y)` by `rotation.(x + 5y)` (`lib/keccak.ml` lines 17–24). In
  particular Algorithm 2 writes every lane.
* `rotation_from_walk`: the same fact as a table: walking
  `(x, y) ← (y, (2x + 3y) mod 5)` from `(1, 0)`, the `t`-th position gets
  offset `(t+1)(t+2)/2 mod 64`.
* `pi_position`: the OCaml π writes lane `(x, y)` to
  `(y, (2x + 3y) mod 5)`, which is exactly the lane that FIPS 202 π
  (`A′[x, y] = A[(x + 3y) mod 5, x]`) fills from `(x, y)`.
-/

namespace OcamlPq.Hash.Keccak

open FIPS202

theorem roundConstants_size : roundConstants.size = 24 := rfl
theorem rotation_size : rotation.size = 25 := rfl

/-- Every rotation amount is a valid `Int64` shift, `0 ≤ n < 64`. -/
theorem rotation_lt (i : ℕ) (hi : i < 25) : rotation[i]! < 64 := by
  interval_cases i <;> decide

/-- `round_constants.(ir)` bit `z` is FIPS 202's `RC[z]` for round `ir`
(Algorithm 6 from `rc(t)`, Algorithm 5). Kernel-checked over all 24 × 64
bits. -/
theorem roundConstants_eq_RC : ∀ ir : Fin 24, ∀ z : Fin 64,
    (roundConstants[ir.val]!).getLsbD z.val = RC ir.val z := by
  decide +kernel

/-- FIPS 202 ρ (Algorithm 2 as written) rotates lane `(x, y)` towards
higher `z` by `rotation.(x + 5y)`: `A′[x, y, z] = A[x, y, z − rotation(x+5y)]`. -/
theorem rho_eq (A : State) (x y : Fin 5) (z : Fin 64) :
    rho A x y z = A x y (z - Fin.ofNat 64 (rotation[x.val + 5 * y.val]!)) := by
  fin_cases x <;> fin_cases y
  case «0».«0» =>
    simp only [Fin.zero_eta, Fin.isValue]
    rw [show Fin.ofNat 64 (rotation[0 + 5 * 0]!) = 0 from rfl, sub_zero]
    rfl
  all_goals rfl

/-- The `(x, y)` walk of Algorithm 2 step 3, with the step number `t`. -/
def rhoWalk : List (ℕ × ℕ × ℕ) :=
  ((List.range 24).foldl (fun (acc : List (ℕ × ℕ × ℕ) × ℕ × ℕ) t =>
    let (l, x, y) := acc
    (l ++ [(x, y, t)], y, (2 * x + 3 * y) % 5)) ([], 1, 0)).1

/-- The walk visits all 24 lanes other than `(0, 0)`, each once, and
`rotation.(x + 5y) = (t+1)(t+2)/2 mod 64` at step `t`; `rotation.(0) = 0`. -/
theorem rotation_from_walk :
    (rhoWalk.map fun p => (p.1, p.2.1)).Nodup ∧
    (∀ x : Fin 5, ∀ y : Fin 5, (x.val, y.val) ≠ (0, 0) →
      (x.val, y.val) ∈ rhoWalk.map fun p => (p.1, p.2.1)) ∧
    (∀ p ∈ rhoWalk, rotation[p.1 + 5 * p.2.1]! = (p.2.2 + 1) * (p.2.2 + 2) / 2 % 64) ∧
    rotation[0]! = 0 := by
  refine ⟨by decide, by decide, ?_, rfl⟩
  simp only [List.forall_mem_iff_forall_getElem]
  decide

/-- The OCaml π step stores lane `(x, y)` at `(new_x, new_y) = (y, (2x+3y) mod 5)`;
FIPS 202 π fills lane `(X, Y)` from `((X + 3Y) mod 5, X)`. These agree. -/
theorem pi_position (x y : Fin 5) :
    let X := y
    let Y := 2 * x + 3 * y
    X + 3 * Y = x ∧ X = y := by
  revert x y; decide

end OcamlPq.Hash.Keccak
