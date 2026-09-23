import Mathlib

/-!
# FIPS 202 (SHA-3 Standard), transcribed

An independent transcription of the parts of FIPS 202 (August 2015) that the
OCaml library implements, written from the standard and not from the code:

* §3.1 the state array `A[x, y, z]` and its conversion to and from strings,
* §3.2 the step mappings θ (Algorithm 1), ρ (Algorithm 2), π (Algorithm 3),
  χ (Algorithm 4), ι with `rc` (Algorithms 5 and 6),
* §3.3 `Keccak-p[b, nr]` (Algorithm 7) and §3.4 `Keccak-f`,
* §4 `SPONGE` (Algorithm 8), §5.1 `pad10*1` (Algorithm 9),
* §5.2 `KECCAK[c]`, §6.1 `SHA3-256`, `SHA3-512`, §6.2 `SHAKE128`, `SHAKE256`,
* Appendix B.1 byte-string to bit-string conversion.

Strings are `List Bool`, with `S[0]` the head. Only `b = 1600` (`w = 64`,
`ℓ = 6`) is needed. The coordinates `x, y` live in `Fin 5` and `z` in
`Fin 64`, so the standard's "`mod 5`" and "`mod w`" are the arithmetic of
those types.
-/

namespace OcamlPq.Hash.FIPS202

/-- A FIPS 202 bit string. -/
abbrev Bits := List Bool

/-- `b = 1600` (Table 1). -/
def b : ℕ := 1600
/-- `w = b / 25 = 64` (Table 1). -/
def w : ℕ := 64
/-- `ℓ = log₂(b/25) = 6` (Table 1). -/
def ℓ : ℕ := 6

/-- A state array `A[x, y, z]` (§3.1.1). -/
abbrev State := Fin 5 → Fin 5 → Fin 64 → Bool

/-- §3.1.2: `A[x, y, z] = S[w(5y + x) + z]`. -/
def ofString (S : Bits) : State :=
  fun x y z => S.getD (w * (5 * y.val + x.val) + z.val) false

/-- §3.1.3: `Lane(i, j) = A[i, j, 0] ‖ … ‖ A[i, j, w−1]`. -/
def lane (A : State) (i j : Fin 5) : Bits := (List.finRange 64).map fun k => A i j k

/-- §3.1.3: `Plane(j) = Lane(0, j) ‖ … ‖ Lane(4, j)`. -/
def plane (A : State) (j : Fin 5) : Bits := (List.finRange 5).flatMap fun i => lane A i j

/-- §3.1.3: `S = Plane(0) ‖ … ‖ Plane(4)`. -/
def toString (A : State) : Bits := (List.finRange 5).flatMap fun j => plane A j

/-- Algorithm 1, θ(A). -/
def theta (A : State) : State :=
  let C : Fin 5 → Fin 64 → Bool := fun x z =>
    A x 0 z ^^ A x 1 z ^^ A x 2 z ^^ A x 3 z ^^ A x 4 z
  let D : Fin 5 → Fin 64 → Bool := fun x z => C (x - 1) z ^^ C (x + 1) (z - 1)
  fun x y z => A x y z ^^ D x z

/-- Algorithm 2, ρ(A), transcribed as the loop it is: step 1 fills lane
`(0, 0)`, then step 3 runs `t = 0, …, 23`, filling lane `(x, y)` with the
lane of `A` rotated by `(t+1)(t+2)/2`, and moving `(x, y) ← (y, (2x+3y) mod 5)`.
Lanes that the loop never writes would read `false`; `Keccak.rho_eq` in
`KeccakConstants` shows there are none (every lane equals a rotation of `A`). -/
def rho (A : State) : State :=
  let A' : State := fun x y z => if x = 0 ∧ y = 0 then A 0 0 z else false
  let step : State × Fin 5 × Fin 5 → ℕ → State × Fin 5 × Fin 5 := fun s t =>
    let (A', x, y) := s
    (fun x' y' z => if x' = x ∧ y' = y then A x y (z - Fin.ofNat 64 ((t + 1) * (t + 2) / 2))
                    else A' x' y' z,
     y, 2 * x + 3 * y)
  ((List.range 24).foldl step (A', 1, 0)).1

/-- Algorithm 3, π(A): `A′[x, y, z] = A[(x + 3y) mod 5, x, z]`. -/
def pi (A : State) : State := fun x y z => A (x + 3 * y) x z

/-- Algorithm 4, χ(A): `A′[x, y, z] = A[x, y, z] ⊕ ((A[(x+1) mod 5, y, z] ⊕ 1) · A[(x+2) mod 5, y, z])`. -/
def chi (A : State) : State :=
  fun x y z => A x y z ^^ ((A (x + 1) y z ^^ true) && A (x + 2) y z)

/-- Algorithm 5, rc(t). `R` is the 8-bit (and transiently 9-bit) register
`R[0] R[1] …` as a list. -/
def rc (t : ℕ) : Bool :=
  if t % 255 = 0 then true
  else
    let R : Bits := [true, false, false, false, false, false, false, false]
    let R := (List.range (t % 255)).foldl (fun R _ =>
      let R := false :: R
      let R := R.set 0 (R[0]! ^^ R[8]!)
      let R := R.set 4 (R[4]! ^^ R[8]!)
      let R := R.set 5 (R[5]! ^^ R[8]!)
      let R := R.set 6 (R[6]! ^^ R[8]!)
      R.take 8) R
    R[0]!

/-- Algorithm 6 steps 2–3: the round constant `RC` for round index `ir`, as a
lane. `RC[2^j − 1] = rc(j + 7 ir)` for `0 ≤ j ≤ ℓ`, all other bits 0. -/
def RC (ir : ℕ) : Fin 64 → Bool :=
  (List.range (ℓ + 1)).foldl
    (fun RC j => fun z => if z.val = 2 ^ j - 1 then rc (j + 7 * ir) else RC z)
    (fun _ => false)

/-- Algorithm 6, ι(A, ir). -/
def iota (A : State) (ir : ℕ) : State :=
  fun x y z => if x = 0 ∧ y = 0 then A 0 0 z ^^ RC ir z else A x y z

/-- §3.3, `Rnd(A, ir) = ι(χ(π(ρ(θ(A)))), ir)`. -/
def Rnd (A : State) (ir : ℕ) : State := iota (chi (pi (rho (theta A)))) ir

/-- Algorithm 7, `KECCAK-p[1600, nr](S)` for `nr ≤ 24`: the round index runs
from `12 + 2ℓ − nr` to `12 + 2ℓ − 1`. -/
def KeccakP (nr : ℕ) (S : Bits) : Bits :=
  let A := ofString S
  let A := (List.range' (12 + 2 * ℓ - nr) nr).foldl Rnd A
  toString A

/-- §3.4, `KECCAK-f[1600] = KECCAK-p[1600, 24]`. -/
def KeccakF (S : Bits) : Bits := KeccakP 24 S

/-- Algorithm 9, `pad10*1(x, m) = 1 ‖ 0^j ‖ 1` with `j = (−m − 2) mod x`. -/
def pad101 (x m : ℕ) : Bits :=
  let j := ((-(m : ℤ) - 2) % (x : ℤ)).toNat
  [true] ++ List.replicate j false ++ [true]

/-- `Trunc_s(X)`. -/
def trunc (s : ℕ) (X : Bits) : Bits := X.take s

/-- `S ⊕ T` for equal-length strings. -/
def xorBits (S T : Bits) : Bits := List.zipWith (· ^^ ·) S T

/-- Algorithm 8 steps 7–10 (squeezing): `Z ← Z ‖ Trunc_r(S)`; if `d ≤ |Z|`
return `Trunc_d(Z)`, else `S ← f(S)` and repeat. `fuel` bounds the number of
iterations (`SPONGE` passes `d + 1`, which suffices because each iteration
lengthens `Z` by `r ≥ 1`). -/
def squeeze (f : Bits → Bits) (r d : ℕ) : ℕ → Bits → Bits → Bits
  | 0, _, Z => Z
  | fuel + 1, S, Z =>
    let Z := Z ++ trunc r S
    if d ≤ Z.length then trunc d Z else squeeze f r d fuel (f S) Z

/-- Algorithm 8, `SPONGE[f, pad, r](N, d)` with `b = 1600`. -/
def sponge (f : Bits → Bits) (pad : ℕ → ℕ → Bits) (r : ℕ) (N : Bits) (d : ℕ) : Bits :=
  let P := N ++ pad r N.length
  let n := P.length / r
  let c := b - r
  let block : ℕ → Bits := fun i => (P.drop (i * r)).take r
  let S := (List.range n).foldl
    (fun S i => f (xorBits S (block i ++ List.replicate c false))) (List.replicate b false)
  squeeze f r d (d + 1) S []

/-- §5.2, `KECCAK[c](N, d) = SPONGE[KECCAK-p[1600, 24], pad10*1, 1600 − c](N, d)`. -/
def Keccak (c : ℕ) (N : Bits) (d : ℕ) : Bits := sponge (KeccakP 24) pad101 (1600 - c) N d

/-- §6.1, `SHA3-256(M) = KECCAK[512](M ‖ 01, 256)`. -/
def SHA3_256 (M : Bits) : Bits := Keccak 512 (M ++ [false, true]) 256
/-- §6.1, `SHA3-512(M) = KECCAK[1024](M ‖ 01, 512)`. -/
def SHA3_512 (M : Bits) : Bits := Keccak 1024 (M ++ [false, true]) 512
/-- §6.2, `SHAKE128(M, d) = KECCAK[256](M ‖ 1111, d)`. -/
def SHAKE128 (M : Bits) (d : ℕ) : Bits := Keccak 256 (M ++ [true, true, true, true]) d
/-- §6.2, `SHAKE256(M, d) = KECCAK[512](M ‖ 1111, d)`. -/
def SHAKE256 (M : Bits) (d : ℕ) : Bits := Keccak 512 (M ++ [true, true, true, true]) d

/-- Appendix B.1: a byte string as a bit string, each byte contributing its
bits in order of increasing significance (`h2b` without the hex step). -/
def bytesToBits (bs : List UInt8) : Bits :=
  bs.flatMap fun byte => (List.range 8).map fun i => byte.toNat.testBit i

end OcamlPq.Hash.FIPS202
