import OcamlPq.MLKEMAlg.Interface

/-!
# FIPS 203 Algorithms 13-18 and the input checks of §7

A transcription of K-PKE (Algorithms 13-15), the internal ML-KEM algorithms
(16-18) and the input checks of FIPS 203 §7.2-7.3. It is written from the
standard, independently of lib/mlkem_engine.ml, over byte strings and
polynomials in `ℤ_q^256`. The building blocks are `SpecPrims`; sampling is
`samplePolyCBD` / `sampleNTT` from `SampleCBD.lean` / `SampleNTT.lean`.

`SampleNTT` (Algorithm 7) is partial, since its loop need not terminate. The
algorithms here use its total extension `sampleNTTTotal` (0 on
non-termination). `sampleNtt_spec` shows that the implementation diverges on
exactly the same inputs, so every terminating run of the implementation is
described.

Byte-string notation: `slice B a b` is `B[a : b]` (bytes `a, …, b - 1`), `++`
is concatenation `‖`.
-/

namespace OcamlPq.MLKEMAlg.Spec

variable (P : Params) (K : Keccak) (S : SpecPrims)

/-- `B[a : b]`. -/
def slice (B : Bytes) (a b : ℕ) : Bytes := (B.take b).drop a

/-- A natural number below 256 as one byte (FIPS 203 writes `d‖k`, `ρ‖j‖i`,
    `PRF(σ, N)` with single-byte `k`, `i`, `j`, `N`). -/
def byte (x : ℕ) : Byte := ⟨x % 256, Nat.mod_lt _ (by norm_num)⟩

/-- `H(s) := SHA3-256(s)` (eq. 4.4). -/
def H (s : Bytes) : Bytes := K.sha3_256 s

/-- `G(c) := SHA3-512(c)` split into its two 32-byte halves (eq. 4.5). -/
def G (c : Bytes) : Bytes × Bytes := (slice (K.sha3_512 c) 0 32, slice (K.sha3_512 c) 32 64)

/-- `J(s) := SHAKE256(s, 8 · 32)` (eq. 4.4). -/
def J (s : Bytes) : Bytes := List.ofFn (fun i : Fin 32 => K.shake256 s i)

/-- `ByteEncode₁₂` applied to a vector: the concatenation of the encodings of
    its entries (FIPS 203 §2.4.8). -/
def encodeVec12 (v : Fin P.k → Poly) : Bytes := (List.ofFn fun i => S.byteEncode12 (v i)).flatten

/-- `ByteDecode₁₂` applied to `384k` bytes: entry `i` decodes `B[384i : 384(i+1)]`. -/
def decodeVec12 (B : Bytes) : Fin P.k → Poly :=
  fun i => S.byteDecode12 (slice B (384 * i.val) (384 * (i.val + 1)))

/-- The matrix `Â` with `Â[i, j] ← SampleNTT(ρ‖j‖i)` (Algorithm 13 lines 3-7,
    Algorithm 14 lines 4-8). -/
noncomputable def matrixA (ρ : Bytes) (i j : Fin P.k) : Poly :=
  sampleNTTTotal K (ρ ++ [byte j.val, byte i.val])

/-- Algorithm 13, `K-PKE.KeyGen(d)`: returns `(ek_PKE, dk_PKE)`. The counter `N`
    runs over `0, …, k - 1` for `s` and `k, …, 2k - 1` for `e`. -/
noncomputable def kpkeKeyGen (d : Bytes) : Bytes × Bytes :=
  let ρ := (G K (d ++ [byte P.k])).1
  let σ := (G K (d ++ [byte P.k])).2
  let AHat := matrixA P K ρ
  let s : Fin P.k → Poly := fun i => samplePolyCBD P.eta1 (prf K P.eta1 σ (byte i.val))
  let e : Fin P.k → Poly := fun i => samplePolyCBD P.eta1 (prf K P.eta1 σ (byte (P.k + i.val)))
  let sHat : Fin P.k → Poly := fun i => S.NTT (s i)
  let eHat : Fin P.k → Poly := fun i => S.NTT (e i)
  let tHat : Fin P.k → Poly := fun i => (∑ j, S.multiplyNTTs (AHat i j) (sHat j)) + eHat i
  (encodeVec12 P S tHat ++ ρ, encodeVec12 P S sHat)

/-- Algorithm 14, `K-PKE.Encrypt(ek_PKE, m, r)`. The counter `N` runs over
    `0, …, k - 1` for `y`, `k, …, 2k - 1` for `e₁`, and is `2k` for `e₂`. -/
noncomputable def kpkeEncrypt (ek m r : Bytes) : Bytes :=
  let tHat := decodeVec12 P S (slice ek 0 (384 * P.k))
  let ρ := slice ek (384 * P.k) (384 * P.k + 32)
  let AHat := matrixA P K ρ
  let y : Fin P.k → Poly := fun i => samplePolyCBD P.eta1 (prf K P.eta1 r (byte i.val))
  let e₁ : Fin P.k → Poly := fun i => samplePolyCBD P.eta2 (prf K P.eta2 r (byte (P.k + i.val)))
  let e₂ : Poly := samplePolyCBD P.eta2 (prf K P.eta2 r (byte (2 * P.k)))
  let yHat : Fin P.k → Poly := fun i => S.NTT (y i)
  -- `u ← NTT⁻¹(Âᵀ ∘ ŷ) + e₁`, where `(Âᵀ ∘ ŷ)[i] = Σ_j Â[j, i] ∘ ŷ[j]` (eq. 2.13)
  let u : Fin P.k → Poly := fun i => S.invNTT (∑ j, S.multiplyNTTs (AHat j i) (yHat j)) + e₁ i
  let μ := S.decodeDecompress 1 m
  -- `v ← NTT⁻¹(t̂ᵀ ∘ ŷ) + e₂ + μ` (eq. 2.14)
  let v : Poly := S.invNTT (∑ j, S.multiplyNTTs (tHat j) (yHat j)) + e₂ + μ
  let c₁ := (List.ofFn fun i => S.compressEncode P.du (u i)).flatten
  let c₂ := S.compressEncode P.dv v
  c₁ ++ c₂

/-- Algorithm 15, `K-PKE.Decrypt(dk_PKE, c)`. -/
def kpkeDecrypt (dk c : Bytes) : Bytes :=
  let c₁ := slice c 0 (32 * P.du * P.k)
  let c₂ := slice c (32 * P.du * P.k) (32 * (P.du * P.k + P.dv))
  let u' : Fin P.k → Poly :=
    fun i => S.decodeDecompress P.du (slice c₁ (32 * P.du * i.val) (32 * P.du * (i.val + 1)))
  let v' := S.decodeDecompress P.dv c₂
  let sHat := decodeVec12 P S dk
  let w := v' - S.invNTT (∑ i, S.multiplyNTTs (sHat i) (S.NTT (u' i)))
  S.compressEncode 1 w

/-- Algorithm 16, `ML-KEM.KeyGen_internal(d, z)`: returns `(ek, dk)`. -/
noncomputable def keyGenInternal (d z : Bytes) : Bytes × Bytes :=
  let (ekPKE, dkPKE) := kpkeKeyGen P K S d
  (ekPKE, dkPKE ++ ekPKE ++ H K ekPKE ++ z)

/-- Algorithm 17, `ML-KEM.Encaps_internal(ek, m)`: returns `(K, c)`. -/
noncomputable def encapsInternal (ek m : Bytes) : Bytes × Bytes :=
  let (Kss, r) := G K (m ++ H K ek)
  (Kss, kpkeEncrypt P K S ek m r)

/-- Algorithm 18, `ML-KEM.Decaps_internal(dk, c)` with implicit rejection. -/
noncomputable def decapsInternal (dk c : Bytes) : Bytes :=
  let dkPKE := slice dk 0 (384 * P.k)
  let ekPKE := slice dk (384 * P.k) (768 * P.k + 32)
  let h := slice dk (768 * P.k + 32) (768 * P.k + 64)
  let z := slice dk (768 * P.k + 64) (768 * P.k + 96)
  let m' := kpkeDecrypt P S dkPKE c
  let (K', r') := G K (m' ++ h)
  let Kbar := J K (z ++ c)
  let c' := kpkeEncrypt P K S ekPKE m' r'
  if c ≠ c' then Kbar else K'

/-- FIPS 203 §7.2, encapsulation key check: the type check (length `384k + 32`)
    and the modulus check (`ByteEncode₁₂(ByteDecode₁₂(ek[0 : 384k])) = ek[0 : 384k]`,
    entry by entry). -/
def ekCheck (ek : Bytes) : Prop :=
  ek.length = 384 * P.k + 32 ∧
    ∀ i : Fin P.k, S.byteEncode12 (S.byteDecode12 (slice ek (384 * i.val) (384 * (i.val + 1)))) =
      slice ek (384 * i.val) (384 * (i.val + 1))

/-- FIPS 203 §7.3, decapsulation input check on the key: the type check
    (length `768k + 96`) and the hash check `H(dk[384k : 768k + 32]) = dk[768k + 32 : 768k + 64]`. -/
def dkCheck (dk : Bytes) : Prop :=
  dk.length = 768 * P.k + 96 ∧
    H K (slice dk (384 * P.k) (768 * P.k + 32)) = slice dk (768 * P.k + 32) (768 * P.k + 64)

end OcamlPq.MLKEMAlg.Spec
