import OcamlPq.MLKEMAlg.Lemmas

/-!
# K-PKE: `pke_encrypt` and `pke_decrypt` refine FIPS 203 Algorithms 14 and 15

`EkRepr ek EK` is the representation invariant linking an
`encapsulation_key` record to its octets `EK`. `parse_ek` establishes it
(`Keys.lean`), and so does `keygen_internal` (`RefineKEM.lean`).
-/

namespace OcamlPq.MLKEMAlg

open Spec Impl

variable {P : Params} {K : Keccak} {I : ImplPrims} {S : SpecPrims}

/-! ## Generic facts -/

theorem arrayInitST_counter' {α : Type} (g : ℕ → α) (m s : ℕ) :
    arrayInitST m (fun s => (g s, s + 1)) s = (fun i => g (s + i.val), s + m) :=
  arrayInitST_counter g _ (fun _ => rfl) m s

/-- Reading back a buffer after a final blit that ends where the read ends. -/
theorem bufToList_blit_end (src : Bytes) (buf : ℕ → Byte) (off len : ℕ) (h : len ≤ src.length) :
    bufToList (blitString src 0 buf off len) 0 (off + len) = bufToList buf 0 off ++ src.take len := by
  rw [bufToList_add, zero_add, bufToList_blitString h]
  congr 1
  exact bufToList_congr fun p _ hp => blitString_outside (Or.inl (by omega))

/-- `blitChunks` from offset 0 read back. -/
theorem bufToList_blitChunks_zero {k : ℕ} (c : ℕ) (chunk : Fin k → Bytes) (buf : ℕ → Byte)
    (hc : ∀ i, (chunk i).length = c) :
    bufToList (blitChunks c 0 chunk buf) 0 (k * c) = (List.ofFn chunk).flatten :=
  bufToList_blitChunks c 0 chunk buf hc

/-- A sampled noise polynomial: canonical and equal to
    `SamplePolyCBD_η(PRF_η(seed, N))`. -/
theorem sampleCbd_nonce (eta : ℕ) (heta : eta = 2 ∨ eta = 3) (seed : Bytes) (N : ℕ) (hN : N < 256) :
    Canonical (sampleCbd K eta seed N) ∧
      toSpec (sampleCbd K eta seed N) = samplePolyCBD eta (prf K eta seed (byte N)) := by
  rw [byte_eq_mk hN]; exact sampleCbd_spec K eta heta seed N hN

/-- **Matrix index order.** `a.(row).(col) = sample_ntt rho col row` is
    `Â[row, col] = SampleNTT(ρ ‖ col ‖ row)`, i.e. `Â[i, j] = SampleNTT(ρ‖j‖i)`. -/
theorem matrix_spec (hk : P.k ≤ 256) (rho : Bytes) (row col : Fin P.k) :
    Canonical (matrix P K rho row col) ∧ toSpec (matrix P K rho row col) = matrixA P K rho row col := by
  have hr : row.val < 256 := by omega
  have hc : col.val < 256 := by omega
  obtain ⟨h1, h2⟩ := sampleNttTotal_spec K rho col.val row.val hc hr
  refine ⟨h1, ?_⟩
  simp only [matrix, h2, matrixA, byte_eq_mk hc, byte_eq_mk hr]

/-! ## The representation invariant of encapsulation keys -/

variable (P K S) in
/-- The record `ek` represents the octets `EK`: this is what `parse_ek` and
    `keygen_internal` produce. -/
structure EkRepr (ek : EncapsulationKey P.k) (EK : Bytes) : Prop where
  encoded : ek.encoded = EK
  length : EK.length = P.ekSize
  rho : ek.rho = slice EK (384 * P.k) (384 * P.k + 32)
  t_canon : ∀ i, Canonical (ek.t i)
  t_spec : ∀ i, toSpec (ek.t i) = S.byteDecode12 (slice EK (384 * i.val) (384 * (i.val + 1)))
  a : ek.a = matrix P K ek.rho
  h : ek.h = K.sha3_256 EK

/-! ## `pke_encrypt` -/

section Encrypt

variable (P K I)

/-- `r` in `pke_encrypt`: `NTT(SamplePolyCBD_η₁(PRF(r, i)))` for `N = i`. -/
def encY (r : Bytes) : Fin P.k → IPoly := fun i => I.ntt (sampleCbd K P.eta1 r (0 + i.val))
/-- `e1`: nonces `k, …, 2k - 1`. -/
def encE1 (r : Bytes) : Fin P.k → IPoly := fun i => sampleCbd K P.eta2 r (0 + P.k + i.val)
/-- `e2`: nonce `2k`. -/
def encE2 (r : Bytes) : IPoly := sampleCbd K P.eta2 r (0 + P.k + P.k)
/-- `u.(col)`. -/
def encU (ek : EncapsulationKey P.k) (r : Bytes) : Fin P.k → IPoly := fun col =>
  (List.finRange P.k).foldl
    (fun total row => I.polyAdd total (I.inverseNtt (I.nttMul (ek.a row col) (encY P K I r row))))
    (encE1 P K r col)
/-- `!v_ntt`. -/
def encVNtt (ek : EncapsulationKey P.k) (r : Bytes) : IPoly :=
  (List.finRange P.k).foldl (fun acc i => I.polyAdd acc (I.nttMul (ek.t i) (encY P K I r i))) polyZero
/-- `v`. -/
def encV (ek : EncapsulationKey P.k) (m r : Bytes) : IPoly :=
  I.polyAdd (I.polyAdd (I.inverseNtt (encVNtt P K I ek r)) (encE2 P K r)) (decodeMessage I m)

/-- `pke_encrypt` with the nonce counter resolved: `r` uses nonces
    `0, …, k - 1`, `e1` uses `k, …, 2k - 1` and `e2` uses `2k`. -/
theorem pkeEncrypt_unfold (g : ℕ → Byte) (ek : EncapsulationKey P.k) (m r : Bytes) :
    pkeEncrypt P K I g ek m r =
      bufToList (blitString (I.encodeCompressed P.dv (encV P K I ek m r)) 0
        (blitChunks P.encodingSizeU 0 (fun i => I.encodeCompressed P.du (encU P K I ek r i)) g)
        (P.k * P.encodingSizeU) P.encodingSizeV) 0 P.ctSize := by
  simp only [pkeEncrypt, arrayInitST_counter']
  rfl

end Encrypt

section EncryptProof

variable (hR : Refines I S) (hL : S.Laws) (hP : P.Valid)
include hR hP

theorem encY_spec (r : Bytes) (i : Fin P.k) :
    Canonical (encY P K I r i) ∧
      toSpec (encY P K I r i) = S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 r (byte i.val))) := by
  have hB := hP.bounds
  have hk := hB.k_le
  obtain ⟨h1, h2⟩ := sampleCbd_nonce (K := K) P.eta1 hB.eta1 r i.val (by omega)
  obtain ⟨h3, h4⟩ := hR.ntt _ h1
  simp only [encY, zero_add]
  exact ⟨h3, by rw [h4, h2]⟩

omit hR in
theorem encE1_spec (r : Bytes) (i : Fin P.k) :
    Canonical (encE1 P K r i) ∧
      toSpec (encE1 P K r i) = samplePolyCBD P.eta2 (prf K P.eta2 r (byte (P.k + i.val))) := by
  have hB := hP.bounds
  have hk := hB.k_le
  simp only [encE1, zero_add]
  exact sampleCbd_nonce P.eta2 hB.eta2 r _ (by omega)

omit hR in
theorem encE2_spec (r : Bytes) :
    Canonical (encE2 P K r) ∧
      toSpec (encE2 P K r) = samplePolyCBD P.eta2 (prf K P.eta2 r (byte (2 * P.k))) := by
  have hB := hP.bounds
  have hk := hB.k_le
  simp only [encE2, zero_add, show P.k + P.k = 2 * P.k by ring]
  exact sampleCbd_nonce P.eta2 hB.eta2 r _ (by omega)

include hL in
theorem encU_spec {ek : EncapsulationKey P.k} {EK : Bytes} (hek : EkRepr P K S ek EK) (r : Bytes)
    (col : Fin P.k) :
    Canonical (encU P K I ek r col) ∧
      toSpec (encU P K I ek r col) =
        S.invNTT (∑ j, S.multiplyNTTs (matrixA P K (slice EK (384 * P.k) (384 * P.k + 32)) j col)
          (S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 r (byte j.val))))) +
        samplePolyCBD P.eta2 (prf K P.eta2 r (byte (P.k + col.val))) := by
  have hk := hP.bounds.k_le
  have hterm : ∀ row, Canonical (I.inverseNtt (I.nttMul (ek.a row col) (encY P K I r row))) ∧
      toSpec (I.inverseNtt (I.nttMul (ek.a row col) (encY P K I r row))) =
        S.invNTT (S.multiplyNTTs (matrixA P K (slice EK (384 * P.k) (384 * P.k + 32)) row col)
          (S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 r (byte row.val))))) := by
    intro row
    have hmat := matrix_spec (K := K) (by omega) ek.rho row col
    rw [← hek.a, hek.rho] at hmat
    obtain ⟨hy1, hy2⟩ := encY_spec (K := K) hR hP r row
    obtain ⟨hm1, hm2⟩ := hR.nttMul _ _ hmat.1 hy1
    obtain ⟨hi1, hi2⟩ := hR.inverseNtt _ hm1
    refine ⟨hi1, ?_⟩
    rw [hi2, hm2, hy2, hmat.2]
  obtain ⟨he1, he2⟩ := encE1_spec (K := K) hP r col
  obtain ⟨hs1, hs2⟩ := foldl_polyAdd_finRange hR _ (fun row => (hterm row).1) _ he1
  refine ⟨hs1, ?_⟩
  simp only [encU]
  rw [hs2, he2, invNTT_sum hL, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun row _ => (hterm row).2

theorem encVNtt_spec {ek : EncapsulationKey P.k} {EK : Bytes} (hek : EkRepr P K S ek EK)
    (r : Bytes) :
    Canonical (encVNtt P K I ek r) ∧
      toSpec (encVNtt P K I ek r) =
        ∑ j, S.multiplyNTTs (decodeVec12 P S (slice EK 0 (384 * P.k)) j)
          (S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 r (byte j.val)))) := by
  have hterm : ∀ i, Canonical (I.nttMul (ek.t i) (encY P K I r i)) ∧
      toSpec (I.nttMul (ek.t i) (encY P K I r i)) =
        S.multiplyNTTs (decodeVec12 P S (slice EK 0 (384 * P.k)) i)
          (S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 r (byte i.val)))) := by
    intro i
    obtain ⟨hy1, hy2⟩ := encY_spec (K := K) hR hP r i
    obtain ⟨hm1, hm2⟩ := hR.nttMul _ _ (hek.t_canon i) hy1
    refine ⟨hm1, ?_⟩
    rw [hm2, hy2, hek.t_spec, decodeVec12, slice_slice _ _ _ _ _ (by have := i.isLt; nlinarith)]
    simp
  obtain ⟨hs1, hs2⟩ := foldl_polyAdd_finRange hR _ (fun i => (hterm i).1) _ polyZero_canonical
  refine ⟨hs1, ?_⟩
  simp only [encVNtt]
  rw [hs2, toSpec_polyZero, zero_add]
  exact Finset.sum_congr rfl fun i _ => (hterm i).2

theorem encV_spec {ek : EncapsulationKey P.k} {EK : Bytes} (hek : EkRepr P K S ek EK)
    (m r : Bytes) (hm : m.length = 32) :
    Canonical (encV P K I ek m r) ∧
      toSpec (encV P K I ek m r) =
        S.invNTT (∑ j, S.multiplyNTTs (decodeVec12 P S (slice EK 0 (384 * P.k)) j)
          (S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 r (byte j.val))))) +
        samplePolyCBD P.eta2 (prf K P.eta2 r (byte (2 * P.k))) + S.decodeDecompress 1 m := by
  obtain ⟨hv1, hv2⟩ := encVNtt_spec hR hP hek r
  obtain ⟨hi1, hi2⟩ := hR.inverseNtt _ hv1
  obtain ⟨he1, he2⟩ := encE2_spec (K := K) hP r
  obtain ⟨ha1, ha2⟩ := hR.polyAdd _ _ hi1 he1
  obtain ⟨hd1, hd2⟩ := hR.decodeCompressed 1 (by simp [Widths]) m 0 (by omega)
  obtain ⟨hb1, hb2⟩ := hR.polyAdd _ _ ha1 hd1
  refine ⟨hb1, ?_⟩
  simp only [encV, decodeMessage]
  have hmm : stringSub m 0 (32 * 1) = m := by rw [mul_one, ← hm, stringSub_zero_length]
  rw [hb2, ha2, hi2, hv2, he2, hd2, hmm]

include hL in
/-- **Algorithm 14.** On an encapsulation key record representing `EK` and a
    32-byte message, `pke_encrypt` computes `K-PKE.Encrypt(EK, m, r)`, for
    every initial content of its output buffer. The output has
    `ciphertext_size` bytes. -/
theorem pkeEncrypt_refines {ek : EncapsulationKey P.k} {EK : Bytes} (hek : EkRepr P K S ek EK)
    (g : ℕ → Byte) (m r : Bytes) (hm : m.length = 32) :
    pkeEncrypt P K I g ek m r = kpkeEncrypt P K S EK m r ∧
      (pkeEncrypt P K I g ek m r).length = P.ctSize := by
  obtain ⟨hdu, hdv⟩ := hP.widths
  refine ⟨?_, by rw [pkeEncrypt_unfold]; simp⟩
  rw [pkeEncrypt_unfold]
  have hU : ∀ i, (I.encodeCompressed P.du (encU P K I ek r i)).length = P.encodingSizeU := by
    intro i
    rw [(hR.encodeCompressed P.du hdu _ (encU_spec hR hL hP hek r i).1).2, P.encodingSizeU_eq]
  have hVl : (I.encodeCompressed P.dv (encV P K I ek m r)).length = P.encodingSizeV := by
    rw [(hR.encodeCompressed P.dv hdv _ (encV_spec hR hP hek m r hm).1).2, P.encodingSizeV_eq]
  rw [Params.ctSize, bufToList_blit_end _ _ _ _ (by rw [hVl]), List.take_of_length_le (by rw [hVl]),
    bufToList_blitChunks_zero _ _ _ hU]
  simp only [kpkeEncrypt]
  congr 1
  · congr 1
    apply congrArg List.ofFn
    funext i
    rw [(hR.encodeCompressed P.du hdu _ (encU_spec hR hL hP hek r i).1).1,
      (encU_spec hR hL hP hek r i).2]
  · rw [(hR.encodeCompressed P.dv hdv _ (encV_spec hR hP hek m r hm).1).1,
      (encV_spec hR hP hek m r hm).2]

end EncryptProof

/-! ## `pke_decrypt` -/

section DecryptProof

variable (hR : Refines I S) (hP : P.Valid)
include hR hP

/-- **Algorithm 15.** If the secret vector `dk.s` is canonical and decodes the
    chunks of `DKPKE`, then on a ciphertext of `ciphertext_size` bytes
    `pke_decrypt` computes `K-PKE.Decrypt(DKPKE, c)`. The result has 32 bytes. -/
theorem pkeDecrypt_refines (dk : DecapsulationKey P.k) (DKPKE : Bytes)
    (hs : ∀ i, Canonical (dk.s i) ∧
      toSpec (dk.s i) = S.byteDecode12 (slice DKPKE (384 * i.val) (384 * (i.val + 1))))
    (c : Bytes) (hc : c.length = P.ctSize) :
    pkeDecrypt P I dk c = kpkeDecrypt P S DKPKE c ∧ (pkeDecrypt P I dk c).length = 32 := by
  obtain ⟨hdu, hdv⟩ := hP.widths
  have hct := P.ctSize_eq
  have hu : ∀ i : Fin P.k, Canonical (I.decodeCompressed P.du c (i.val * P.encodingSizeU)) ∧
      toSpec (I.decodeCompressed P.du c (i.val * P.encodingSizeU)) =
        S.decodeDecompress P.du (slice (slice c 0 (32 * P.du * P.k))
          (32 * P.du * i.val) (32 * P.du * (i.val + 1))) := by
    intro i
    have hi := i.isLt
    rw [P.encodingSizeU_eq]
    have hle : i.val * (32 * P.du) + 32 * P.du ≤ c.length := by
      rw [hc, hct]; nlinarith
    obtain ⟨h1, h2⟩ := hR.decodeCompressed P.du hdu c _ hle
    refine ⟨h1, ?_⟩
    rw [h2, stringSub_eq_slice, slice_slice _ _ _ _ _ (by nlinarith)]
    congr 2 <;> ring
  have hv : Canonical (I.decodeCompressed P.dv c (P.k * P.encodingSizeU)) ∧
      toSpec (I.decodeCompressed P.dv c (P.k * P.encodingSizeU)) =
        S.decodeDecompress P.dv (slice c (32 * P.du * P.k) (32 * (P.du * P.k + P.dv))) := by
    rw [P.encodingSizeU_eq]
    obtain ⟨h1, h2⟩ := hR.decodeCompressed P.dv hdv c _ (by rw [hc, hct])
    refine ⟨h1, ?_⟩
    rw [h2, stringSub_eq_slice]
    congr 2 <;> ring
  have hterm : ∀ i : Fin P.k,
      Canonical (I.nttMul (dk.s i) (I.ntt (I.decodeCompressed P.du c (i.val * P.encodingSizeU)))) ∧
      toSpec (I.nttMul (dk.s i) (I.ntt (I.decodeCompressed P.du c (i.val * P.encodingSizeU)))) =
        S.multiplyNTTs (decodeVec12 P S DKPKE i)
          (S.NTT (S.decodeDecompress P.du (slice (slice c 0 (32 * P.du * P.k))
            (32 * P.du * i.val) (32 * P.du * (i.val + 1))))) := by
    intro i
    obtain ⟨hn1, hn2⟩ := hR.ntt _ (hu i).1
    obtain ⟨hm1, hm2⟩ := hR.nttMul _ _ (hs i).1 hn1
    exact ⟨hm1, by rw [hm2, hn2, (hu i).2, (hs i).2, decodeVec12]⟩
  obtain ⟨hs1, hs2⟩ := foldl_polyAdd_finRange hR _ (fun i => (hterm i).1) _ polyZero_canonical
  obtain ⟨hi1, hi2⟩ := hR.inverseNtt _ hs1
  obtain ⟨hw1, hw2⟩ := hR.polySub _ _ hv.1 hi1
  obtain ⟨he1, he2⟩ := hR.encodeCompressed 1 (by simp [Widths]) _ hw1
  refine ⟨?_, by simp only [pkeDecrypt, encodeMessage]; rw [he2]⟩
  simp only [pkeDecrypt, encodeMessage, kpkeDecrypt]
  rw [he1, hw2, hi2, hs2, hv.2, toSpec_polyZero, zero_add]
  congr 3
  exact Finset.sum_congr rfl fun i _ => (hterm i).2

end DecryptProof

end OcamlPq.MLKEMAlg
