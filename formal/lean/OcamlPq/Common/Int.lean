import Mathlib

/-!
# OCaml integer semantics

The OCaml sources use three integer types:

* `int` is two's complement with a platform-dependent width: 63 bits in
  64-bit native code, 32 bits under `js_of_ocaml`, and 31 bits in 32-bit
  native code and under `wasm_of_ocaml`.
* `Int32.t` is 32-bit two's complement on every platform.
* `Int64.t` is 64-bit two's complement on every platform.

The models in this project evaluate `int` expressions over `ℤ`. A result
proved that way holds on a platform only if no intermediate value wraps
around, so every module also proves that the intermediates of the code it
models are `Portable`: they fit in the narrowest `int`, and therefore in
every one. `wrap_eq_self` is the bridge from that bound to each platform.

`Int32.t` and `Int64.t` code is modelled with `UInt32`, `UInt64`, or
`BitVec`, whose arithmetic wraps exactly as two's complement does.

OCaml's `/` and `mod` on `int` truncate toward zero, unlike Lean's `/` and
`%` on `ℤ`, which round toward negative infinity. `ocamlDiv` and `ocamlMod`
model the OCaml operators.
-/

namespace OcamlPq

/-- A platform on which the OCaml code can run. -/
inductive Platform
  | native64
  | jsOfOcaml
  | native32
  | wasmOfOcaml
  deriving DecidableEq, Repr

/-- The width in bits of OCaml's `int` on a platform. -/
def Platform.intBits : Platform → ℕ
  | .native64 => 63
  | .jsOfOcaml => 32
  | .native32 => 31
  | .wasmOfOcaml => 31

theorem Platform.intBits_ge (p : Platform) : 31 ≤ p.intBits := by
  cases p <;> decide

/-- Two's complement wrap-around of an integer to `w` bits: the value that
    OCaml's `int` holds after an operation whose exact result is `x`. -/
def wrap (w : ℕ) (x : ℤ) : ℤ := (x + 2 ^ (w - 1)) % 2 ^ w - 2 ^ (w - 1)

/-- `x` fits in the narrowest OCaml `int` (31 bits), and hence in the `int`
    of every platform. -/
def Portable (x : ℤ) : Prop := -(2 ^ 30) ≤ x ∧ x < 2 ^ 30

instance (x : ℤ) : Decidable (Portable x) := by
  unfold Portable; infer_instance

theorem Portable.of_bounds {x lo hi : ℤ} (hlo : -(2 ^ 30) ≤ lo) (hhi : hi ≤ 2 ^ 30)
    (h1 : lo ≤ x) (h2 : x < hi) : Portable x :=
  ⟨le_trans hlo h1, lt_of_lt_of_le h2 hhi⟩

theorem Portable.of_nat_lt {n : ℕ} (h : n < 2 ^ 30) : Portable (n : ℤ) := by
  constructor
  · have : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    linarith [show (0 : ℤ) < 2 ^ 30 by norm_num]
  · exact_mod_cast h

/-- A portable value is unaffected by wrapping to any width of at least 31
    bits. -/
theorem wrap_eq_self {w : ℕ} (hw : 31 ≤ w) {x : ℤ} (hx : Portable x) : wrap w x = x := by
  obtain ⟨hlo, hhi⟩ := hx
  unfold wrap
  have hpow : (2 : ℤ) ^ 30 ≤ 2 ^ (w - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hw' : (2 : ℤ) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [Int.emod_eq_of_lt (by linarith) (by rw [hw']; linarith)]
  ring

/-- A portable value is the same on every platform. -/
theorem Portable.wrap_platform {x : ℤ} (hx : Portable x) (p : Platform) :
    wrap p.intBits x = x :=
  wrap_eq_self p.intBits_ge hx

/-- OCaml's `/` on `int`, which truncates toward zero. -/
def ocamlDiv (a b : ℤ) : ℤ := a.tdiv b

/-- OCaml's `mod` on `int`, whose result has the sign of the dividend. -/
def ocamlMod (a b : ℤ) : ℤ := a.tmod b

theorem ocamlDiv_of_nonneg {a b : ℤ} (ha : 0 ≤ a) : ocamlDiv a b = a / b := by
  unfold ocamlDiv; exact Int.tdiv_eq_ediv_of_nonneg ha

theorem ocamlMod_of_nonneg {a b : ℤ} (ha : 0 ≤ a) : ocamlMod a b = a % b := by
  unfold ocamlMod; exact Int.tmod_eq_emod_of_nonneg ha

end OcamlPq
