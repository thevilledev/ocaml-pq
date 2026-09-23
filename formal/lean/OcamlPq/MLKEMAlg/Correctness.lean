import OcamlPq.MLKEMAlg.Keys

/-!
# Deterministic correctness of K-PKE and ML-KEM (obligation 8)

At the spec level (FIPS 203 Algorithms 13-18):

* `decrypt_encrypt_noise`: `K-PKE.Decrypt(dk, K-PKE.Encrypt(ek, m, r))` equals
  `ByteEncode₁(Compress₁(μ + n))` with `μ = Decompress₁(ByteDecode₁(m))`, for
  an explicit noise term
  `n = e₂ + c_v + NTT⁻¹(êᵀ∘ŷ − ŝᵀ∘NTT(e₁ + c_u))`. Here `c_u`, `c_v` are the
  compression errors of `u` and `v`.
* `kpke_correct`: if every coefficient of `n` has centred absolute value
  below `⌈q/4⌋ = 832`, decryption returns `m`.
* `mlkem_correct`: under the same bound (for the `r` of `G(m‖H(ek))`),
  `Decaps_internal(dk, c) = K` for `(K, c) = Encaps_internal(ek, m)`.
* `impl_mlkem_correct`: the same for the OCaml functions, through the
  refinement theorems.

Assumptions beyond `Refines` and `SpecPrims.Laws`: `SpecPrims.AlgLaws` (NTT is
additive and NTT ∘ NTT⁻¹ = id; `MultiplyNTTs` is commutative, associative and
distributes over `+`), and, for the final decoding step, that
`ByteEncode₁ ∘ Compress₁` and `Decompress₁ ∘ ByteDecode₁` are FIPS 203's
(`Spec.compressEncode1`, `Spec.decodeDecompress1`, transcribed here).
-/

namespace OcamlPq.MLKEMAlg

open Spec Impl

/-! ## Compress₁, Decompress₁, ByteEncode₁, ByteDecode₁ -/

namespace Spec

/-- FIPS 203 eq. (4.7): `Compress_d(x) = ⌈(2^d/q)·x⌋ mod 2^d`, using
    `⌈a/b⌋ = ⌊(2a + b)/(2b)⌋`. -/
def compressD (d : ℕ) (x : ZMod q) : ℕ := ((2 ^ (d + 1) * x.val + q) / (2 * q)) % 2 ^ d

/-- FIPS 203 eq. (4.8): `Decompress_d(y) = ⌈(q/2^d)·y⌋`. -/
def decompressD (d : ℕ) (y : ℕ) : ZMod q := (((2 * q * y + 2 ^ d) / 2 ^ (d + 1) : ℕ) : ZMod q)

/-- FIPS 203 Algorithms 5 and 3 for `d = 1`: bit `i` of the output is `F[i] mod 2`. -/
def byteEncode1 (F : ℕ → ℕ) : Bytes :=
  List.ofFn fun k : Fin 32 =>
    ⟨(∑ j ∈ Finset.range 8, (F (8 * k.val + j) % 2) * 2 ^ j) % 256, Nat.mod_lt _ (by norm_num)⟩

/-- FIPS 203 Algorithm 6 for `d = 1`: `F[i] = b[i]` with `b = BytesToBits(B)`. -/
def byteDecode1 (B : Bytes) : ℕ → ℕ := fun i => (bytesToBits B).getD i 0

/-- `ByteEncode₁(Compress₁(w))`. -/
def compressEncode1 (w : Poly) : Bytes :=
  byteEncode1 (fun i => if h : i < 256 then compressD 1 (w ⟨i, h⟩) else 0)

/-- `Decompress₁(ByteDecode₁(m))`. -/
def decodeDecompress1 (m : Bytes) : Poly := fun i => decompressD 1 (byteDecode1 m i.val)

/-- The centred absolute value `|x mod± q|` of a coefficient. -/
def cabs (x : ZMod q) : ℕ := min x.val (q - x.val)

end Spec

/-- `Compress₁(Decompress₁(b) + n) = b` whenever `|n| < ⌈q/4⌋ = 832`
    (checked over all of `ℤ_q` by kernel evaluation). -/
theorem compress1_robust : ∀ b : Fin 2, ∀ n : ZMod q, cabs n < 832 →
    compressD 1 (decompressD 1 b.val + n) = b.val := by
  decide +kernel

theorem byte_bits_sum (x : ℕ) (h : x < 256) : ∑ j ∈ Finset.range 8, (x / 2 ^ j % 2) * 2 ^ j = x := by
  simp [Finset.sum_range_succ]
  omega

/-- Decoding a 32-byte message, adding noise of centred size below 832 to
    every coefficient, and re-encoding gives the message back. -/
theorem message_robust (m : Bytes) (hm : m.length = 32) (n : Poly) (hn : ∀ i, cabs (n i) < 832) :
    compressEncode1 (decodeDecompress1 m + n) = m := by
  apply List.ext_getElem (by simp [compressEncode1, byteEncode1, hm])
  intro k h1 h2
  simp only [compressEncode1, byteEncode1, List.getElem_ofFn]
  apply Fin.ext
  simp only
  have hk : k < 32 := by omega
  rw [Finset.sum_congr rfl (g := fun j => ((m[k]'h2).val / 2 ^ j % 2) * 2 ^ j)]
  · rw [byte_bits_sum _ (m[k]'h2).isLt, Nat.mod_eq_of_lt (m[k]'h2).isLt]
  · intro j hj
    simp only [Finset.mem_range] at hj
    have hi : 8 * k + j < 256 := by omega
    rw [dite_eq_left hi]
    simp only [Pi.add_apply, decodeDecompress1, byteDecode1]
    rw [bytesToBits_getD m k j h2 hj]
    have := compress1_robust ⟨(m[k]'h2).val / 2 ^ j % 2, Nat.mod_lt _ (by norm_num)⟩ _ (hn ⟨_, hi⟩)
    simp only at this
    rw [this, Nat.mod_mod]

/-! ## The ring laws of `T_q` -/

/-- The algebraic facts about NTT and MultiplyNTTs that FIPS 203 relies on:
    `NTT` is an additive bijection with inverse `NTT⁻¹`, and `(T_q, +, ∘)` is a
    commutative ring (FIPS 203 §4.3). -/
structure SpecPrims.AlgLaws (S : SpecPrims) : Prop where
  NTT_add : ∀ f g, S.NTT (f + g) = S.NTT f + S.NTT g
  NTT_invNTT : ∀ f, S.NTT (S.invNTT f) = f
  mul_comm : ∀ a b, S.multiplyNTTs a b = S.multiplyNTTs b a
  mul_assoc : ∀ a b c, S.multiplyNTTs (S.multiplyNTTs a b) c = S.multiplyNTTs a (S.multiplyNTTs b c)
  mul_add : ∀ a b c, S.multiplyNTTs a (b + c) = S.multiplyNTTs a b + S.multiplyNTTs a c

section Algebra

variable {S : SpecPrims}

/-- `NTT⁻¹` as an additive homomorphism. -/
def invNTTHom (hL : S.Laws) : Poly →+ Poly := AddMonoidHom.mk' S.invNTT hL.invNTT_add

/-- `NTT` as an additive homomorphism. -/
def nttHom (hA : S.AlgLaws) : Poly →+ Poly := AddMonoidHom.mk' S.NTT hA.NTT_add

/-- `a ∘ ·` as an additive homomorphism. -/
def mulLeft (hA : S.AlgLaws) (a : Poly) : Poly →+ Poly := AddMonoidHom.mk' (S.multiplyNTTs a) (hA.mul_add a)

/-- `· ∘ b` as an additive homomorphism. -/
def mulRight (hA : S.AlgLaws) (b : Poly) : Poly →+ Poly :=
  AddMonoidHom.mk' (fun a => S.multiplyNTTs a b) (fun x y => by
    simp only [hA.mul_comm _ b, hA.mul_add])

/-- The decryption identity `w = μ + n`: given `t̂ = Â∘ŝ + ê`,
    `u = NTT⁻¹(Âᵀ∘ŷ) + e₁` and `v = NTT⁻¹(t̂ᵀ∘ŷ) + e₂ + μ`, and received
    `u + c_u`, `v + c_v`, the decryptor's
    `w = (v + c_v) − NTT⁻¹(ŝᵀ∘NTT(u + c_u))` equals
    `μ + (e₂ + c_v + NTT⁻¹(êᵀ∘ŷ − ŝᵀ∘NTT(e₁ + c_u)))`. -/
theorem noise_identity (hL : S.Laws) (hA : S.AlgLaws) {k : ℕ} (A : Fin k → Fin k → Poly)
    (s e y e1 cu : Fin k → Poly) (e2 μ cv : Poly) :
    let t : Fin k → Poly := fun j => (∑ i, S.multiplyNTTs (A j i) (s i)) + e j
    let u : Fin k → Poly := fun i => S.invNTT (∑ j, S.multiplyNTTs (A j i) (y j)) + e1 i
    let v : Poly := S.invNTT (∑ j, S.multiplyNTTs (t j) (y j)) + e2 + μ
    (v + cv) - S.invNTT (∑ i, S.multiplyNTTs (s i) (S.NTT (u i + cu i))) =
      μ + (e2 + cv + S.invNTT ((∑ j, S.multiplyNTTs (e j) (y j)) -
        ∑ i, S.multiplyNTTs (s i) (S.NTT (e1 i + cu i)))) := by
  intro t u v
  -- NTT(u_i + c_u_i) = (Âᵀ∘ŷ)_i + NTT(e₁_i + c_u_i)
  have hNu : ∀ i, S.NTT (u i + cu i) =
      (∑ j, S.multiplyNTTs (A j i) (y j)) + S.NTT (e1 i + cu i) := by
    intro i
    simp only [u, add_assoc, hA.NTT_add, hA.NTT_invNTT]
  -- ŝᵀ∘(Âᵀ∘ŷ) = t̂ᵀ∘ŷ − êᵀ∘ŷ
  have hswap : (∑ i, S.multiplyNTTs (s i) (∑ j, S.multiplyNTTs (A j i) (y j))) =
      (∑ j, S.multiplyNTTs (t j) (y j)) - ∑ j, S.multiplyNTTs (e j) (y j) := by
    have h1 : ∀ i, S.multiplyNTTs (s i) (∑ j, S.multiplyNTTs (A j i) (y j)) =
        ∑ j, S.multiplyNTTs (S.multiplyNTTs (A j i) (s i)) (y j) := by
      intro i
      rw [show S.multiplyNTTs (s i) (∑ j, S.multiplyNTTs (A j i) (y j)) =
        mulLeft hA (s i) (∑ j, S.multiplyNTTs (A j i) (y j)) from rfl, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [mulLeft, AddMonoidHom.mk'_apply]
      rw [← hA.mul_assoc, hA.mul_comm (s i)]
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 : (∑ i, S.multiplyNTTs (S.multiplyNTTs (A j i) (s i)) (y j)) =
        S.multiplyNTTs (∑ i, S.multiplyNTTs (A j i) (s i)) (y j) := by
      rw [show S.multiplyNTTs (∑ i, S.multiplyNTTs (A j i) (s i)) (y j) =
        mulRight hA (y j) (∑ i, S.multiplyNTTs (A j i) (s i)) from rfl, map_sum]
      rfl
    rw [h2]
    have h3 : S.multiplyNTTs (t j) (y j) =
        S.multiplyNTTs (∑ i, S.multiplyNTTs (A j i) (s i)) (y j) + S.multiplyNTTs (e j) (y j) := by
      show mulRight hA (y j) (t j) = mulRight hA (y j) _ + mulRight hA (y j) _
      rw [← map_add]
    rw [h3]; abel
  have hsum : (∑ i, S.multiplyNTTs (s i) (S.NTT (u i + cu i))) =
      (∑ j, S.multiplyNTTs (t j) (y j)) - (∑ j, S.multiplyNTTs (e j) (y j)) +
        ∑ i, S.multiplyNTTs (s i) (S.NTT (e1 i + cu i)) := by
    rw [← hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hNu, hA.mul_add]
  rw [hsum]
  have hinv : ∀ a b c : Poly, S.invNTT (a - b + c) = S.invNTT a - S.invNTT b + S.invNTT c := by
    intro a b c
    show invNTTHom hL _ = invNTTHom hL _ - invNTTHom hL _ + invNTTHom hL _
    rw [map_add, map_sub]
  have hinv2 : ∀ a b : Poly, S.invNTT (a - b) = S.invNTT a - S.invNTT b := by
    intro a b
    show invNTTHom hL _ = invNTTHom hL _ - invNTTHom hL _
    rw [map_sub]
  rw [hinv, hinv2]
  simp only [v]
  abel

end Algebra

/-! ## The spec algorithms in terms of named pieces -/

section Pieces

variable (P : Params) (K : Keccak) (S : SpecPrims)

/-- `ρ` of Algorithm 13. -/
noncomputable def gRho (d : Bytes) : Bytes := (G K (d ++ [byte P.k])).1
/-- `σ` of Algorithm 13. -/
noncomputable def gSigma (d : Bytes) : Bytes := (G K (d ++ [byte P.k])).2
/-- `ŝ` of Algorithm 13. -/
noncomputable def gSHat (d : Bytes) : Fin P.k → Poly :=
  fun i => S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 (gSigma P K d) (byte i.val)))
/-- `ê` of Algorithm 13. -/
noncomputable def gEHat (d : Bytes) : Fin P.k → Poly :=
  fun i => S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 (gSigma P K d) (byte (P.k + i.val))))
/-- `t̂ = Â∘ŝ + ê` of Algorithm 13. -/
noncomputable def gTHat (d : Bytes) : Fin P.k → Poly :=
  fun i => (∑ j, S.multiplyNTTs (matrixA P K (gRho P K d) i j) (gSHat P K S d j)) + gEHat P K S d i
/-- `ŷ` of Algorithm 14. -/
noncomputable def eYHat (r : Bytes) : Fin P.k → Poly :=
  fun i => S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 r (byte i.val)))
/-- `e₁` of Algorithm 14. -/
noncomputable def eE1 (r : Bytes) : Fin P.k → Poly :=
  fun i => samplePolyCBD P.eta2 (prf K P.eta2 r (byte (P.k + i.val)))
/-- `e₂` of Algorithm 14. -/
noncomputable def eE2 (r : Bytes) : Poly := samplePolyCBD P.eta2 (prf K P.eta2 r (byte (2 * P.k)))
/-- `u` of Algorithm 14 for the matrix seed `ρ`. -/
noncomputable def eU (ρ r : Bytes) : Fin P.k → Poly :=
  fun i => S.invNTT (∑ j, S.multiplyNTTs (matrixA P K ρ j i) (eYHat P K S r j)) + eE1 P K r i
/-- `v` of Algorithm 14 for the vector `t̂`. -/
noncomputable def eV (tHat : Fin P.k → Poly) (m r : Bytes) : Poly :=
  S.invNTT (∑ j, S.multiplyNTTs (tHat j) (eYHat P K S r j)) + eE2 P K r + S.decodeDecompress 1 m

theorem kpkeKeyGen_eq (d : Bytes) :
    kpkeKeyGen P K S d = (encodeVec12 P S (gTHat P K S d) ++ gRho P K d, encodeVec12 P S (gSHat P K S d)) :=
  rfl

theorem kpkeEncrypt_eq (ek m r : Bytes) :
    kpkeEncrypt P K S ek m r =
      (List.ofFn fun i => S.compressEncode P.du (eU P K S (slice ek (384 * P.k) (384 * P.k + 32)) r i)).flatten ++
        S.compressEncode P.dv (eV P K S (decodeVec12 P S (slice ek 0 (384 * P.k))) m r) :=
  rfl

/-- The noise term of a K-PKE encryption under the key generated from `d`. -/
noncomputable def kpkeNoise (d m r : Bytes) : Poly :=
  let u := eU P K S (gRho P K d) r
  let v := eV P K S (gTHat P K S d) m r
  let cu : Fin P.k → Poly := fun i => S.decodeDecompress P.du (S.compressEncode P.du (u i)) - u i
  let cv : Poly := S.decodeDecompress P.dv (S.compressEncode P.dv v) - v
  eE2 P K r + cv + S.invNTT ((∑ j, S.multiplyNTTs (gEHat P K S d j) (eYHat P K S r j)) -
    ∑ i, S.multiplyNTTs (gSHat P K S d i) (S.NTT (eE1 P K r i + cu i)))

end Pieces

/-! ## K-PKE correctness -/

section KPKE

variable {P : Params} {K : Keccak} {I : ImplPrims} {S : SpecPrims}

theorem compressEncode_length (hR : Refines I S) {d : ℕ} (hd : d ∈ Widths) (x : Poly) :
    (S.compressEncode d x).length = 32 * d := by
  have hc : Canonical (fun i => ((x i).val : ℤ)) := fun i =>
    ⟨by positivity, by show ((x i).val : ℤ) < (q : ℤ); exact_mod_cast ZMod.val_lt (x i)⟩
  have hx : toSpec (fun i => ((x i).val : ℤ)) = x := by funext i; simp [toSpec]
  rw [← hx, ← (hR.encodeCompressed d hd _ hc).1, (hR.encodeCompressed d hd _ hc).2]

theorem decodeVec12_encodeVec12 (hR : Refines I S) (hL : S.Laws) (v : Fin P.k → Poly) (tail : Bytes) :
    decodeVec12 P S (slice (encodeVec12 P S v ++ tail) 0 (384 * P.k)) = v := by
  funext i
  have hi := i.isLt
  rw [decodeVec12, ← encodeVec12_length hR v, slice_append_left, slice_encodeVec12 hR,
    hL.byteDecode12_byteEncode12]

variable (hR : Refines I S) (hL : S.Laws) (hA : S.AlgLaws) (hP : P.Valid)
include hR hL hA hP

/-- **K-PKE decryption identity.** Decrypting an encryption under a freshly
    generated key computes `ByteEncode₁(Compress₁(μ + n))` for the noise `n`
    of `kpkeNoise`. -/
theorem decrypt_encrypt_noise (d m r : Bytes) :
    kpkeDecrypt P S (kpkeKeyGen P K S d).2 (kpkeEncrypt P K S (kpkeKeyGen P K S d).1 m r) =
      S.compressEncode 1 (S.decodeDecompress 1 m + kpkeNoise P K S d m r) := by
  obtain ⟨hdu, hdv⟩ := hP.widths
  have hρ : (gRho P K d).length = 32 := by simp [gRho, G, slice, K.sha3_512_length]
  rw [kpkeKeyGen_eq, kpkeEncrypt_eq]
  -- the encryptor recovers `t̂` and `ρ` from the encapsulation key
  have htl := encodeVec12_length hR (gTHat P K S d)
  rw [decodeVec12_encodeVec12 hR hL,
    show slice (encodeVec12 P S (gTHat P K S d) ++ gRho P K d) (384 * P.k) (384 * P.k + 32) = gRho P K d by
      rw [← htl, ← hρ, slice_append_right']]
  set u := eU P K S (gRho P K d) r with hu
  set v := eV P K S (gTHat P K S d) m r with hv
  have hc1len : (List.ofFn fun i => S.compressEncode P.du (u i)).flatten.length = 32 * P.du * P.k := by
    rw [flatten_ofFn_length (32 * P.du) _ (fun i => compressEncode_length hR hdu _)]; ring
  have hc2len : (S.compressEncode P.dv v).length = 32 * P.dv := compressEncode_length hR hdv _
  simp only [kpkeDecrypt]
  -- the decryptor recovers `c₁`, `c₂` and `ŝ`
  rw [show 32 * P.du * P.k = (List.ofFn fun i => S.compressEncode P.du (u i)).flatten.length from hc1len.symm,
    slice_append_left]
  rw [show 32 * (P.du * P.k + P.dv) = (List.ofFn fun i => S.compressEncode P.du (u i)).flatten.length +
      (S.compressEncode P.dv v).length by rw [hc1len, hc2len]; ring, slice_append_right']
  have hsd : decodeVec12 P S (encodeVec12 P S (gSHat P K S d)) = gSHat P K S d := by
    have := decodeVec12_encodeVec12 hR hL (gSHat P K S d) []
    rwa [List.append_nil, ← encodeVec12_length hR (gSHat P K S d),
      slice_all] at this
  rw [hsd]
  have hu' : ∀ i : Fin P.k, S.decodeDecompress P.du (slice (List.ofFn fun i => S.compressEncode P.du (u i)).flatten
      (32 * P.du * i.val) (32 * P.du * (i.val + 1))) =
      u i + (S.decodeDecompress P.du (S.compressEncode P.du (u i)) - u i) := by
    intro i
    rw [slice_flatten_ofFn (32 * P.du) _ (fun j => compressEncode_length hR hdu _), add_sub_cancel]
  simp only [hu']
  congr 1
  rw [show S.decodeDecompress P.dv (S.compressEncode P.dv v) =
      v + (S.decodeDecompress P.dv (S.compressEncode P.dv v) - v) by rw [add_sub_cancel]]
  have := noise_identity hL hA (fun i j => matrixA P K (gRho P K d) i j) (gSHat P K S d) (gEHat P K S d)
    (eYHat P K S r) (eE1 P K r) (fun i => S.decodeDecompress P.du (S.compressEncode P.du (u i)) - u i)
    (eE2 P K r) (S.decodeDecompress 1 m) (S.decodeDecompress P.dv (S.compressEncode P.dv v) - v)
  simp only at this
  simp only [hv, hu] at this ⊢
  simp only [eV, eU, gTHat] at this ⊢
  rw [this]
  rfl

/-- **K-PKE correctness.** If every coefficient of the noise has centred
    absolute value below `⌈q/4⌋ = 832`, decryption of an encryption of the
    32-byte message `m` returns `m`. -/
theorem kpke_correct (hC : S.compressEncode 1 = compressEncode1)
    (hD : S.decodeDecompress 1 = decodeDecompress1) (d m r : Bytes) (hm : m.length = 32)
    (hn : ∀ i, cabs (kpkeNoise P K S d m r i) < 832) :
    kpkeDecrypt P S (kpkeKeyGen P K S d).2 (kpkeEncrypt P K S (kpkeKeyGen P K S d).1 m r) = m := by
  rw [decrypt_encrypt_noise hR hL hA hP, hC, hD, message_robust m hm _ hn]

/-- **ML-KEM correctness.** For a 32-byte `m`, if the noise of the
    encryption inside `Encaps_internal(ek, m)` is below `⌈q/4⌋`, then
    `Decaps_internal(dk, c) = K` for `(ek, dk) = KeyGen_internal(d, z)` and
    `(K, c) = Encaps_internal(ek, m)`. -/
theorem mlkem_correct (hC : S.compressEncode 1 = compressEncode1)
    (hD : S.decodeDecompress 1 = decodeDecompress1) (d z m : Bytes) (hm : m.length = 32)
    (hn : ∀ i, cabs (kpkeNoise P K S d m (G K (m ++ H K (keyGenInternal P K S d z).1)).2 i) < 832) :
    decapsInternal P K S (keyGenInternal P K S d z).2
        (encapsInternal P K S (keyGenInternal P K S d z).1 m).2 =
      (encapsInternal P K S (keyGenInternal P K S d z).1 m).1 := by
  have hdk := P.dkSize_eq
  have hek := P.ekSize_eq
  set EK := (kpkeKeyGen P K S d).1 with hEK
  set DKP := (kpkeKeyGen P K S d).2 with hDKP
  have hEKlen : EK.length = 384 * P.k + 32 := by
    rw [hEK, kpkeKeyGen_eq, List.length_append, encodeVec12_length hR]
    simp [gRho, G, slice, K.sha3_512_length]
  have hDKPlen : DKP.length = 384 * P.k := by rw [hDKP, kpkeKeyGen_eq, encodeVec12_length hR]
  have hHlen : (H K EK).length = 32 := K.sha3_256_length _
  have hkg : keyGenInternal P K S d z = (EK, DKP ++ EK ++ H K EK ++ z) := rfl
  rw [hkg] at hn ⊢
  simp only [encapsInternal, decapsInternal] at hn ⊢
  -- the four parts of the expanded key
  have s1 : slice (DKP ++ EK ++ H K EK ++ z) 0 (384 * P.k) = DKP := by
    rw [List.append_assoc, List.append_assoc, ← hDKPlen, slice_append_left]
  have s2 : slice (DKP ++ EK ++ H K EK ++ z) (384 * P.k) (768 * P.k + 32) = EK := by
    rw [List.append_assoc, List.append_assoc, slice_append_of_ge _ _ _ _ (by omega), hDKPlen,
      slice_append_of_le _ _ _ _ (by omega), show 384 * P.k - 384 * P.k = 0 by omega,
      show 768 * P.k + 32 - 384 * P.k = EK.length by omega, slice_all]
  have s3 : slice (DKP ++ EK ++ H K EK ++ z) (768 * P.k + 32) (768 * P.k + 64) = H K EK := by
    rw [List.append_assoc, List.append_assoc, slice_append_of_ge _ _ _ _ (by omega), hDKPlen,
      slice_append_of_ge _ _ _ _ (by omega), slice_append_of_le _ _ _ _ (by omega),
      show 768 * P.k + 32 - 384 * P.k - EK.length = 0 by omega,
      show 768 * P.k + 64 - 384 * P.k - EK.length = (H K EK).length by omega, slice_all]
  rw [s1, s2, s3]
  have hdec := kpke_correct hR hL hA hP hC hD d m (G K (m ++ H K EK)).2 hm hn
  rw [← hEK, ← hDKP] at hdec
  simp only [hdec, ne_eq, not_true_eq_false, ite_false]

end KPKE

/-! ## Correctness of the OCaml functions -/

section Impl

variable {P : Params} {K : Keccak} {I : ImplPrims} {S : SpecPrims}

/-- **ML-KEM correctness of the implementation.** For 32-byte `d`, `z` and
    `m`: `keygen_internal ~d ~z` returns a key `dk`,
    `encapsulate_internal dk.ek ~randomness:m` returns `(c, K)`, and
    `decapsulate dk c = K`, provided the encryption noise is below `⌈q/4⌋`.
    This holds for every initial content of every buffer. -/
theorem impl_mlkem_correct (hR : Refines I S) (hL : S.Laws) (hA : S.AlgLaws) (hP : P.Valid)
    (hC : S.compressEncode 1 = compressEncode1) (hD : S.decodeDecompress 1 = decodeDecompress1)
    (g g₁ g₂ g₃ : ℕ → Byte) (d z m : Bytes) (hd : d.length = 32) (hz : z.length = 32)
    (hm : m.length = 32)
    (hn : ∀ i, cabs (kpkeNoise P K S d m (G K (m ++ H K (keyGenInternal P K S d z).1)).2 i) < 832) :
    ∃ dk c Kss, keygenInternal P K I g d z = .ok dk ∧
      encapsulateInternal P K I g₁ dk.ek m = .ok (c, Kss) ∧
      decapsulate P K I g₂ g₃ dk c = Kss := by
  obtain ⟨dk, hkg, -, -, -, -, hek, hdk⟩ := keygenInternal_refines hR hL hP g d z hd hz
  have henc := encapsulateInternal_refines hR hL hP hek g₁ m hm
  refine ⟨dk, _, _, hkg, henc, ?_⟩
  have hclen : (encapsInternal P K S (keyGenInternal P K S d z).1 m).2.length = P.ctSize := by
    simp only [encapsInternal]
    exact (pkeEncrypt_refines hR hL hP hek g₁ m _ hm).1 ▸ (pkeEncrypt_refines hR hL hP hek g₁ m _ hm).2
  rw [decapsulate_refines hR hL hP hdk g₂ g₃ _ hclen]
  exact mlkem_correct hR hL hA hP hC hD d z m hm hn

end Impl

end OcamlPq.MLKEMAlg
