import Mathlib

/-!
# FIPS 180-4 (SHA-256, SHA-512), FIPS 198-1 (HMAC), RFC 8017 (MGF1), transcribed

Written from the standards, independently of the OCaml code.

* Messages are bit strings (`List Bool`, first bit first). A `w`-bit word is
  written as a string most significant bit first (FIPS 180-4 §3.1, §2.2.1).
* §3.2 `ROTR`, `SHR`; §4.1.2/§4.1.3 `Ch`, `Maj`, `Σ`, `σ`; §4.2.2/§4.2.3
  the constants `K`; §5.1.1/§5.1.2 padding; §5.2.1/§5.2.2 parsing; §5.3.3/§5.3.5
  the initial hash values; §6.2.2/§6.4.2 the hash computations.
* The constants are *defined* as FIPS 180-4 states them — the first 32/64
  bits of the fractional parts of the cube roots (for `K`) or square roots (for
  `H(0)`) of the first primes — using real roots and `Nat.nth Nat.Prime`.
  `Sha2Constants` proves the OCaml tables equal them.

SHA-256 and SHA-512 share one algorithm (§6.2.2 and §6.4.2 differ only in the
word size, number of rounds, constants and the functions of §4.1); it is
written once, parametrised by `Params`, and instantiated with the §4.1.2/§4.1.3
values.
-/

namespace OcamlPq.Hash.FIPS180

/-- A bit string. -/
abbrev Bits := List Bool

/-! ## §3.2 operations and §4.1 functions -/

/-- §3.2 (4): `ROTR^n(x) = (x >> n) ∨ (x << w − n)`. -/
def ROTR {w : ℕ} (n : ℕ) (x : BitVec w) : BitVec w := (x >>> n) ||| (x <<< (w - n))
/-- §3.2 (3): `SHR^n(x) = x >> n`. -/
def SHR {w : ℕ} (n : ℕ) (x : BitVec w) : BitVec w := x >>> n

/-- (4.2)/(4.8): `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)`. -/
def Ch {w : ℕ} (x y z : BitVec w) : BitVec w := (x &&& y) ^^^ (~~~x &&& z)
/-- (4.3)/(4.9): `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. -/
def Maj {w : ℕ} (x y z : BitVec w) : BitVec w := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- (4.4) -/ def Sigma0_256 (x : BitVec 32) : BitVec 32 := ROTR 2 x ^^^ ROTR 13 x ^^^ ROTR 22 x
/-- (4.5) -/ def Sigma1_256 (x : BitVec 32) : BitVec 32 := ROTR 6 x ^^^ ROTR 11 x ^^^ ROTR 25 x
/-- (4.6) -/ def sigma0_256 (x : BitVec 32) : BitVec 32 := ROTR 7 x ^^^ ROTR 18 x ^^^ SHR 3 x
/-- (4.7) -/ def sigma1_256 (x : BitVec 32) : BitVec 32 := ROTR 17 x ^^^ ROTR 19 x ^^^ SHR 10 x

/-- (4.10) -/ def Sigma0_512 (x : BitVec 64) : BitVec 64 := ROTR 28 x ^^^ ROTR 34 x ^^^ ROTR 39 x
/-- (4.11) -/ def Sigma1_512 (x : BitVec 64) : BitVec 64 := ROTR 14 x ^^^ ROTR 18 x ^^^ ROTR 41 x
/-- (4.12) -/ def sigma0_512 (x : BitVec 64) : BitVec 64 := ROTR 1 x ^^^ ROTR 8 x ^^^ SHR 7 x
/-- (4.13) -/ def sigma1_512 (x : BitVec 64) : BitVec 64 := ROTR 19 x ^^^ ROTR 61 x ^^^ SHR 6 x

/-! ## Constants -/

/-- "The first `bits` bits of the fractional part of the `k`-th root of `p`":
`⌊frac(p^(1/k)) · 2^bits⌋`. -/
noncomputable def fracRootBits (k bits p : ℕ) : ℕ :=
  ⌊Int.fract ((p : ℝ) ^ ((1 : ℝ) / k)) * 2 ^ bits⌋₊

/-- §4.2.2: `K_t^{256}`, the first 32 bits of the fractional part of the cube
root of the `t`-th prime (`t` counted from 0). -/
noncomputable def K256 (t : ℕ) : BitVec 32 := BitVec.ofNat 32 (fracRootBits 3 32 (Nat.nth Nat.Prime t))
/-- §4.2.3: `K_t^{512}`, the first 64 bits of the fractional part of the cube
root of the `t`-th prime. -/
noncomputable def K512 (t : ℕ) : BitVec 64 := BitVec.ofNat 64 (fracRootBits 3 64 (Nat.nth Nat.Prime t))
/-- §5.3.3: `H_j^{(0)}` for SHA-256, the first 32 bits of the fractional part
of the square root of the `j`-th prime. -/
noncomputable def H0_256 (j : Fin 8) : BitVec 32 := BitVec.ofNat 32 (fracRootBits 2 32 (Nat.nth Nat.Prime j))
/-- §5.3.5: `H_j^{(0)}` for SHA-512, the first 64 bits of the fractional part
of the square root of the `j`-th prime. -/
noncomputable def H0_512 (j : Fin 8) : BitVec 64 := BitVec.ofNat 64 (fracRootBits 2 64 (Nat.nth Nat.Prime j))

/-! ## Words and bit strings -/

/-- A `w`-bit word as a bit string, most significant bit first. -/
def wordToBits {w : ℕ} (x : BitVec w) : Bits := (List.range w).map fun i => x.getMsbD i

/-- The `w`-bit word whose binary representation (most significant bit first)
is `bs` (`|bs| = w`). -/
def wordOfBits (w : ℕ) (bs : Bits) : BitVec w := (BitVec.ofBoolListBE bs).setWidth w

/-- The integer `n` as a `w`-bit big-endian bit string. -/
def natToBits (w n : ℕ) : Bits := wordToBits (BitVec.ofNat w n)

/-- A byte string as a bit string, each byte most significant bit first. -/
def bytesToBitsBE (bs : List UInt8) : Bits :=
  bs.flatMap fun byte => (List.range 8).map fun i => byte.toNat.testBit (7 - i)

/-! ## §5.1 padding and §5.2 parsing -/

/-- §5.1.1 (`blockLen = 512`, `lenBits = 64`) and §5.1.2 (`1024`, `128`):
`M ‖ 1 ‖ 0^k ‖ ⟨ℓ⟩_lenBits` with `k` the smallest non-negative solution of
`ℓ + 1 + k ≡ blockLen − lenBits (mod blockLen)`. -/
def pad (blockLen lenBits : ℕ) (M : Bits) : Bits :=
  let ℓ := M.length
  let k := ((((blockLen - lenBits : ℕ) : ℤ) - (ℓ + 1)) % (blockLen : ℤ)).toNat
  M ++ [true] ++ List.replicate k false ++ natToBits lenBits ℓ

/-- §5.2.1/§5.2.2: the padded message as `N` blocks of sixteen `w`-bit words;
word `j` of block `i` is bits `16w·i + w·j … + w − 1`. -/
def parse (w : ℕ) (P : Bits) : List (Fin 16 → BitVec w) :=
  (List.range (P.length / (16 * w))).map fun i => fun j =>
    wordOfBits w ((P.drop (16 * w * i + w * j.val)).take w)

/-! ## §6.2.2 / §6.4.2 hash computation -/

/-- The parameters that distinguish SHA-256 from SHA-512. -/
structure Params (w : ℕ) where
  rounds : ℕ
  K : ℕ → BitVec w
  H0 : Fin 8 → BitVec w
  bigSigma0 : BitVec w → BitVec w
  bigSigma1 : BitVec w → BitVec w
  smallSigma0 : BitVec w → BitVec w
  smallSigma1 : BitVec w → BitVec w
  blockLen : ℕ
  lenBits : ℕ

/-- Step 1: the message schedule `W_t`. -/
def schedule {w : ℕ} (p : Params w) (Mi : Fin 16 → BitVec w) (t : ℕ) : BitVec w :=
  if h : t < 16 then Mi ⟨t, h⟩
  else p.smallSigma1 (schedule p Mi (t - 2)) + schedule p Mi (t - 7) +
    p.smallSigma0 (schedule p Mi (t - 15)) + schedule p Mi (t - 16)
termination_by t
decreasing_by all_goals omega

/-- The eight working variables `a, …, h`. -/
structure Work (w : ℕ) where
  a : BitVec w
  b : BitVec w
  c : BitVec w
  d : BitVec w
  e : BitVec w
  f : BitVec w
  g : BitVec w
  h : BitVec w

/-- Step 3, one value of `t`. -/
def step {w : ℕ} (p : Params w) (W : ℕ → BitVec w) (v : Work w) (t : ℕ) : Work w :=
  let T1 := v.h + p.bigSigma1 v.e + Ch v.e v.f v.g + p.K t + W t
  let T2 := p.bigSigma0 v.a + Maj v.a v.b v.c
  { h := v.g, g := v.f, f := v.e, e := v.d + T1, d := v.c, c := v.b, b := v.a, a := T1 + T2 }

/-- Steps 1–4 for one message block: `H^{(i)}` from `H^{(i−1)}` and `M^{(i)}`. -/
def compress {w : ℕ} (p : Params w) (H : Fin 8 → BitVec w) (Mi : Fin 16 → BitVec w) :
    Fin 8 → BitVec w :=
  let W := schedule p Mi
  let v0 : Work w := ⟨H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7⟩
  let v := (List.range p.rounds).foldl (step p W) v0
  ![v.a + H 0, v.b + H 1, v.c + H 2, v.d + H 3, v.e + H 4, v.f + H 5, v.g + H 6, v.h + H 7]

/-- The hash of `M`: pad, parse, compress every block, output
`H_0^{(N)} ‖ … ‖ H_7^{(N)}`. -/
def hash {w : ℕ} (p : Params w) (M : Bits) : Bits :=
  let blocks := parse w (pad p.blockLen p.lenBits M)
  let H := blocks.foldl (compress p) p.H0
  (List.finRange 8).flatMap fun j => wordToBits (H j)

/-- SHA-256 parameters (§4.1.2, §4.2.2, §5.1.1, §5.3.3, §6.2). -/
noncomputable def sha256Params : Params 32 where
  rounds := 64
  K := K256
  H0 := H0_256
  bigSigma0 := Sigma0_256
  bigSigma1 := Sigma1_256
  smallSigma0 := sigma0_256
  smallSigma1 := sigma1_256
  blockLen := 512
  lenBits := 64

/-- SHA-512 parameters (§4.1.3, §4.2.3, §5.1.2, §5.3.5, §6.4). -/
noncomputable def sha512Params : Params 64 where
  rounds := 80
  K := K512
  H0 := H0_512
  bigSigma0 := Sigma0_512
  bigSigma1 := Sigma1_512
  smallSigma0 := sigma0_512
  smallSigma1 := sigma1_512
  blockLen := 1024
  lenBits := 128

/-- §6.2: SHA-256 of a message of `ℓ < 2^64` bits. -/
noncomputable def SHA256 (M : Bits) : Bits := hash sha256Params M
/-- §6.4: SHA-512 of a message of `ℓ < 2^128` bits. -/
noncomputable def SHA512 (M : Bits) : Bits := hash sha512Params M

end OcamlPq.Hash.FIPS180

/-! # FIPS 198-1 HMAC and RFC 8017 MGF1

Both are byte-oriented and generic in the hash function. -/

namespace OcamlPq.Hash.FIPS198

/-- FIPS 198-1 §4, steps 1–3: the key `K0` of `B` bytes. If `|K| = B`,
`K0 = K`; if `|K| > B`, `K0 = H(K) ‖ 0^(B−L)`; if `|K| < B`, `K0 = K ‖ 0^(B−|K|)`. -/
def K0 (H : List UInt8 → List UInt8) (B : ℕ) (K : List UInt8) : List UInt8 :=
  if K.length = B then K
  else if K.length > B then H K ++ List.replicate (B - (H K).length) 0
  else K ++ List.replicate (B - K.length) 0

/-- FIPS 198-1 §4, steps 4–9:
`HMAC(K, text) = H((K0 ⊕ opad) ‖ H((K0 ⊕ ipad) ‖ text))`, `ipad = 0x36…`,
`opad = 0x5c…`. -/
def HMAC (H : List UInt8 → List UInt8) (B : ℕ) (K text : List UInt8) : List UInt8 :=
  let k0 := K0 H B K
  let ipad := List.replicate B (0x36 : UInt8)
  let opad := List.replicate B (0x5c : UInt8)
  H (List.zipWith (· ^^^ ·) k0 opad ++ H (List.zipWith (· ^^^ ·) k0 ipad ++ text))

end OcamlPq.Hash.FIPS198

namespace OcamlPq.Hash.RFC8017

/-- RFC 8017 §4.1 I2OSP(x, xLen): `x` as `xLen` bytes, big-endian. -/
def I2OSP (x xLen : ℕ) : List UInt8 :=
  (List.range xLen).map fun i => UInt8.ofNat (x / 256 ^ (xLen - 1 - i) % 256)

/-- RFC 8017 Appendix B.2.1, MGF1 with a hash of output length `hLen`:
`none` is "mask too long" (step 1); otherwise the leading `maskLen` octets of
`T = Hash(seed ‖ I2OSP(0, 4)) ‖ … ‖ Hash(seed ‖ I2OSP(⌈maskLen/hLen⌉ − 1, 4))`. -/
def MGF1 (Hash : List UInt8 → List UInt8) (hLen : ℕ) (mgfSeed : List UInt8) (maskLen : ℕ) :
    Option (List UInt8) :=
  if maskLen > 2 ^ 32 * hLen then none
  else
    let T := (List.range ((maskLen + hLen - 1) / hLen)).foldl
      (fun T counter => T ++ Hash (mgfSeed ++ I2OSP counter 4)) []
    some (T.take maskLen)

end OcamlPq.Hash.RFC8017
