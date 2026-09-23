import OcamlPq.MLKEMAlg.RefinePKE

/-!
# Key generation, encapsulation and decapsulation refine FIPS 203 Algorithms 13, 16-18

* `keygenInternal_refines`: `keygen_internal ~d ~z` returns a key whose
  `encapsulation_key_to_octets` and `decapsulation_key_to_expanded` are the
  `(ek, dk)` of `ML-KEM.KeyGen_internal(d, z)` (Algorithms 13 and 16).
* `encapsulateInternal_refines`: Algorithm 17.
* `decapsulate_refines`: Algorithm 18 with implicit rejection.
* `decapsulate_select`: `decapsulate` returns `K'` when the re-encryption
  matches the ciphertext and `K̄ = J(z‖c)` otherwise.
-/

namespace OcamlPq.MLKEMAlg

open Spec Impl

variable {P : Params} {K : Keccak} {I : ImplPrims} {S : SpecPrims}

/-! ## More slices -/

theorem slice_append_of_le (x y : Bytes) (a b : ℕ) (h : b ≤ x.length) :
    slice (x ++ y) a b = slice x a b := by
  simp only [slice, List.take_append_of_le_length h]

theorem slice_append_of_ge (x y : Bytes) (a b : ℕ) (h : x.length ≤ a) :
    slice (x ++ y) a b = slice y (a - x.length) (b - x.length) := by
  have := slice_append_right x y (a - x.length) (b - x.length)
  rw [show x.length + (a - x.length) = a by omega] at this
  by_cases hb : x.length ≤ b
  · rw [show x.length + (b - x.length) = b by omega] at this; exact this
  · simp only [slice]
    rw [List.take_append_of_le_length (by omega), List.drop_eq_nil_of_le (by simp; omega),
      show b - x.length = 0 by omega]
    simp

theorem byteEncode12_length (hR : Refines I S) (x : Poly) : (S.byteEncode12 x).length = 384 := by
  have hc : Canonical (fun i => ((x i).val : ℤ)) := fun i =>
    ⟨by positivity, by show ((x i).val : ℤ) < (q : ℤ); exact_mod_cast ZMod.val_lt (x i)⟩
  have hx : toSpec (fun i => ((x i).val : ℤ)) = x := by funext i; simp [toSpec]
  rw [← hx, ← (hR.encode12 _ hc).1, (hR.encode12 _ hc).2]

theorem encodeVec12_length (hR : Refines I S) (v : Fin P.k → Poly) :
    (encodeVec12 P S v).length = 384 * P.k := by
  rw [encodeVec12, flatten_ofFn_length 384 _ (fun i => byteEncode12_length hR (v i)), mul_comm]

theorem slice_encodeVec12 (hR : Refines I S) (v : Fin P.k → Poly) (i : Fin P.k) :
    slice (encodeVec12 P S v) (384 * i.val) (384 * (i.val + 1)) = S.byteEncode12 (v i) :=
  slice_flatten_ofFn 384 _ (fun j => byteEncode12_length hR (v j)) i

/-! ## Buffers written by `encode_ek` and `decapsulation_key_to_expanded` -/

/-- `encode_ek t rho = ByteEncode₁₂(t̂) ‖ ρ` for canonical `t` and 32-byte `rho`. -/
theorem encodeEk_eq (hR : Refines I S) (g : ℕ → Byte) (t : Fin P.k → IPoly)
    (ht : ∀ i, Canonical (t i)) (rho : Bytes) (hrho : rho.length = 32) :
    encodeEk P I g t rho = encodeVec12 P S (fun i => toSpec (t i)) ++ rho := by
  unfold encodeEk
  rw [Params.ekSize]
  simp only [Params.encodingSize12]
  rw [bufToList_blit_end _ _ _ _ (by omega), List.take_of_length_le (by omega),
    bufToList_blitChunks_zero _ _ _ (fun i => (hR.encode12 _ (ht i)).2)]
  congr 1
  unfold encodeVec12
  congr 1
  apply congrArg List.ofFn; funext i
  exact (hR.encode12 _ (ht i)).1

/-- `decapsulation_key_to_expanded dk = ByteEncode₁₂(ŝ) ‖ ek ‖ h ‖ z` for
    every initial content of the buffer. -/
theorem toExpanded_eq (hR : Refines I S) (g : ℕ → Byte) (dk : DecapsulationKey P.k)
    (hs : ∀ i, Canonical (dk.s i)) (he : dk.ek.encoded.length = P.ekSize) (hh : dk.ek.h.length = 32)
    (hz : dk.z.length = 32) :
    decapsulationKeyToExpanded P I g dk =
      encodeVec12 P S (fun i => toSpec (dk.s i)) ++ dk.ek.encoded ++ dk.ek.h ++ dk.z := by
  unfold decapsulationKeyToExpanded
  rw [show P.dkSize = P.k * 384 + P.ekSize + 32 + 32 by simp [Params.dkSize, Params.encodingSize12]]
  rw [show P.k * 384 + P.ekSize + 32 + 32 - 32 = P.k * 384 + P.ekSize + 32 by omega]
  simp only [Params.encodingSize12]
  rw [bufToList_blit_end _ _ _ _ (by omega), List.take_of_length_le (by omega),
    bufToList_blit_end _ _ _ _ (by omega), List.take_of_length_le (by omega),
    bufToList_blit_end _ _ _ _ (by omega), List.take_of_length_le (by omega),
    bufToList_blitChunks_zero _ _ _ (fun i => (hR.encode12 _ (hs i)).2)]
  congr 3
  unfold encodeVec12
  congr 1
  apply congrArg List.ofFn; funext i
  exact (hR.encode12 _ (hs i)).1

/-! ## The representation invariant of decapsulation keys -/

variable (P K S) in
/-- The record `dk` represents the expanded decapsulation key `DK`. -/
structure DkRepr (dk : DecapsulationKey P.k) (DK : Bytes) : Prop where
  length : DK.length = P.dkSize
  s_canon : ∀ i, Canonical (dk.s i)
  s_spec : ∀ i, toSpec (dk.s i) = S.byteDecode12 (slice DK (384 * i.val) (384 * (i.val + 1)))
  ek : EkRepr P K S dk.ek (slice DK (384 * P.k) (768 * P.k + 32))
  h : dk.ek.h = slice DK (768 * P.k + 32) (768 * P.k + 64)
  z : dk.z = slice DK (768 * P.k + 64) (768 * P.k + 96)

/-! ## Key generation -/

section KeyGen

variable (P K I)

/-- `expanded = G(d ‖ k)` in `keygen_internal`. -/
def kgExpanded (d : Bytes) : Bytes := K.sha3_512 (d ++ byteString P.k)
/-- `rho`. -/
def kgRho (d : Bytes) : Bytes := stringSub (kgExpanded P K d) 0 32
/-- `sigma`. -/
def kgSigma (d : Bytes) : Bytes := stringSub (kgExpanded P K d) 32 32
/-- `s`: nonces `0, …, k - 1`. -/
def kgS (d : Bytes) : Fin P.k → IPoly := fun i => I.ntt (sampleCbd K P.eta1 (kgSigma P K d) (0 + i.val))
/-- `e`: nonces `k, …, 2k - 1`. -/
def kgE (d : Bytes) : Fin P.k → IPoly :=
  fun i => I.ntt (sampleCbd K P.eta1 (kgSigma P K d) (0 + P.k + i.val))
/-- `t`. -/
noncomputable def kgT (d : Bytes) : Fin P.k → IPoly := fun row =>
  (List.finRange P.k).foldl
    (fun total col => I.polyAdd total (I.nttMul (matrix P K (kgRho P K d) row col) (kgS P K I d col)))
    (kgE P K I d row)

/-- `keygen_internal` with the nonce counter resolved. -/
theorem keygenInternal_unfold (g : ℕ → Byte) (d z : Bytes) (hd : d.length = 32) (hz : z.length = 32) :
    keygenInternal P K I g d z = .ok
      { seed := some (d ++ z), z, s := kgS P K I d,
        ek := { t := kgT P K I d, a := matrix P K (kgRho P K d), rho := kgRho P K d,
                h := K.sha3_256 (encodeEk P I g (kgT P K I d) (kgRho P K d)),
                encoded := encodeEk P I g (kgT P K I d) (kgRho P K d) } } := by
  simp only [keygenInternal, hd, hz, ne_eq, not_true_eq_false, ite_false, arrayInitST_counter']
  rfl

end KeyGen

section KeyGenProof

variable (hR : Refines I S) (hL : S.Laws) (hP : P.Valid)
include hR hP

omit hR hP in
theorem kgRho_eq (d : Bytes) : kgRho P K d = (G K (d ++ [byte P.k])).1 := by
  simp [kgRho, kgExpanded, G, byteString_eq, stringSub_eq_slice]

omit hR hP in
theorem kgSigma_eq (d : Bytes) : kgSigma P K d = (G K (d ++ [byte P.k])).2 := by
  simp [kgSigma, kgExpanded, G, byteString_eq, stringSub_eq_slice]

omit hR hP in
theorem kgRho_length (d : Bytes) : (kgRho P K d).length = 32 := by
  simp [kgRho, stringSub, kgExpanded, K.sha3_512_length]

theorem kgS_spec (d : Bytes) (i : Fin P.k) :
    Canonical (kgS P K I d i) ∧
      toSpec (kgS P K I d i) =
        S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 (G K (d ++ [byte P.k])).2 (byte i.val))) := by
  have hB := hP.bounds
  have hk := hB.k_le
  obtain ⟨h1, h2⟩ := sampleCbd_nonce (K := K) P.eta1 hB.eta1 (kgSigma P K d) i.val (by omega)
  obtain ⟨h3, h4⟩ := hR.ntt _ h1
  simp only [kgS, zero_add]
  exact ⟨h3, by rw [h4, h2, kgSigma_eq]⟩

theorem kgE_spec (d : Bytes) (i : Fin P.k) :
    Canonical (kgE P K I d i) ∧
      toSpec (kgE P K I d i) =
        S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 (G K (d ++ [byte P.k])).2 (byte (P.k + i.val)))) := by
  have hB := hP.bounds
  have hk := hB.k_le
  obtain ⟨h1, h2⟩ := sampleCbd_nonce (K := K) P.eta1 hB.eta1 (kgSigma P K d) (P.k + i.val) (by omega)
  obtain ⟨h3, h4⟩ := hR.ntt _ h1
  simp only [kgE, zero_add]
  exact ⟨h3, by rw [h4, h2, kgSigma_eq]⟩

theorem kgT_spec (d : Bytes) (row : Fin P.k) :
    Canonical (kgT P K I d row) ∧
      toSpec (kgT P K I d row) =
        (∑ j, S.multiplyNTTs (matrixA P K (G K (d ++ [byte P.k])).1 row j)
          (S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 (G K (d ++ [byte P.k])).2 (byte j.val))))) +
        S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 (G K (d ++ [byte P.k])).2 (byte (P.k + row.val)))) := by
  have hk := hP.bounds.k_le
  have hterm : ∀ col, Canonical (I.nttMul (matrix P K (kgRho P K d) row col) (kgS P K I d col)) ∧
      toSpec (I.nttMul (matrix P K (kgRho P K d) row col) (kgS P K I d col)) =
        S.multiplyNTTs (matrixA P K (G K (d ++ [byte P.k])).1 row col)
          (S.NTT (samplePolyCBD P.eta1 (prf K P.eta1 (G K (d ++ [byte P.k])).2 (byte col.val)))) := by
    intro col
    have hmat := matrix_spec (K := K) (by omega) (kgRho P K d) row col
    obtain ⟨hs1, hs2⟩ := kgS_spec (K := K) hR hP d col
    obtain ⟨hm1, hm2⟩ := hR.nttMul _ _ hmat.1 hs1
    exact ⟨hm1, by rw [hm2, hmat.2, hs2, kgRho_eq]⟩
  obtain ⟨he1, he2⟩ := kgE_spec (K := K) hR hP d row
  obtain ⟨h1, h2⟩ := foldl_polyAdd_finRange hR _ (fun col => (hterm col).1) _ he1
  refine ⟨h1, ?_⟩
  simp only [kgT]
  rw [h2, he2, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun col _ => (hterm col).2

include hL in
/-- **Algorithms 13 and 16.** For 32-byte `d` and `z`, `keygen_internal`
    succeeds. Its encapsulation key serialises to `ek` and its expanded
    decapsulation key to `dk`, where `(ek, dk) = ML-KEM.KeyGen_internal(d, z)`.
    The key records the seed `d ‖ z` and satisfies the representation
    invariants, which `encapsulate_internal` and `decapsulate` rely on. -/
theorem keygenInternal_refines (g : ℕ → Byte) (d z : Bytes) (hd : d.length = 32)
    (hz : z.length = 32) :
    ∃ dk, keygenInternal P K I g d z = .ok dk ∧ dk.seed = some (d ++ z) ∧ dk.z = z ∧
      encapsulationKeyToOctets P dk.ek = (keyGenInternal P K S d z).1 ∧
      (∀ g', decapsulationKeyToExpanded P I g' dk = (keyGenInternal P K S d z).2) ∧
      EkRepr P K S dk.ek (keyGenInternal P K S d z).1 ∧
      DkRepr P K S dk (keyGenInternal P K S d z).2 := by
  have hk := hP.bounds.k_le
  rw [keygenInternal_unfold P K I g d z hd hz]
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  -- the encapsulation key octets
  have hEnc : encodeEk P I g (kgT P K I d) (kgRho P K d) = (kpkeKeyGen P K S d).1 := by
    rw [encodeEk_eq hR g _ (fun i => (kgT_spec hR hP d i).1) _ (kgRho_length d)]
    simp only [kpkeKeyGen]
    rw [kgRho_eq]
    congr 2
    funext i
    rw [(kgT_spec hR hP d i).2]
  have hDkPKE : (kpkeKeyGen P K S d).2 = encodeVec12 P S (fun i => toSpec (kgS P K I d i)) := by
    simp only [kpkeKeyGen]
    congr 1; funext i; rw [(kgS_spec hR hP d i).2]
  have hEKform : (kpkeKeyGen P K S d).1 =
      encodeVec12 P S (fun i => toSpec (kgT P K I d i)) ++ kgRho P K d := by
    rw [← hEnc, encodeEk_eq hR g _ (fun i => (kgT_spec hR hP d i).1) _ (kgRho_length d)]
  have hspec : keyGenInternal P K S d z = ((kpkeKeyGen P K S d).1,
      encodeVec12 P S (fun i => toSpec (kgS P K I d i)) ++ (kpkeKeyGen P K S d).1 ++
        K.sha3_256 (kpkeKeyGen P K S d).1 ++ z) := by
    simp only [keyGenInternal, H]; rw [hDkPKE]
  rw [hspec, ← hEnc]
  rw [← hEnc] at hEKform
  generalize encodeEk P I g (kgT P K I d) (kgRho P K d) = EK at hEKform ⊢
  have hEKlen : EK.length = P.ekSize := by
    rw [hEKform, List.length_append, encodeVec12_length hR, kgRho_length, Params.ekSize_eq]
  -- the representation invariant of the encapsulation key
  have hEkRepr : EkRepr P K S
      { t := kgT P K I d, a := matrix P K (kgRho P K d), rho := kgRho P K d,
        h := K.sha3_256 EK, encoded := EK } EK := by
    have htl := encodeVec12_length hR (P := P) (fun i => toSpec (kgT P K I d i))
    refine ⟨rfl, hEKlen, ?_, fun i => (kgT_spec hR hP d i).1, ?_, rfl, rfl⟩
    · show kgRho P K d = _
      rw [hEKform, slice_append_of_ge _ _ _ _ (by omega), htl,
        show 384 * P.k - 384 * P.k = 0 by omega,
        show 384 * P.k + 32 - 384 * P.k = (kgRho P K d).length by rw [kgRho_length]; omega, slice_all]
    · intro i
      show toSpec (kgT P K I d i) = _
      rw [hEKform, slice_append_of_le _ _ _ _ (by rw [htl]; have := i.isLt; nlinarith),
        slice_encodeVec12 hR, hL.byteDecode12_byteEncode12]
  have hsLen := encodeVec12_length hR (P := P) (fun i => toSpec (kgS P K I d i))
  have hHlen : (K.sha3_256 EK).length = 32 := K.sha3_256_length EK
  refine ⟨?_, ?_, hEkRepr, ?_⟩
  · -- encapsulation_key_to_octets
    show stringSub EK 0 P.ekSize = EK
    rw [← hEKlen, stringSub_zero_length]
  · -- decapsulation_key_to_expanded
    intro g'
    exact toExpanded_eq hR g' _ (fun i => (kgS_spec hR hP d i).1) hEKlen hHlen hz
  · -- the representation invariant of the decapsulation key
    have hdk := P.dkSize_eq
    have hek := P.ekSize_eq
    refine ⟨by simp only [List.length_append]; omega, fun i => (kgS_spec hR hP d i).1, ?_, ?_, ?_, ?_⟩
    · intro i
      have hi := i.isLt
      rw [List.append_assoc, List.append_assoc,
        slice_append_of_le _ _ _ _ (by rw [hsLen]; nlinarith), slice_encodeVec12 hR,
        hL.byteDecode12_byteEncode12]
    · rw [List.append_assoc, List.append_assoc, slice_append_of_ge _ _ _ _ (by omega), hsLen,
        slice_append_of_le _ _ _ _ (by omega), show 384 * P.k - 384 * P.k = 0 by omega,
        show 768 * P.k + 32 - 384 * P.k = EK.length by omega, slice_all]
      exact hEkRepr
    · show K.sha3_256 EK = _
      rw [List.append_assoc, List.append_assoc, slice_append_of_ge _ _ _ _ (by omega), hsLen,
        slice_append_of_ge _ _ _ _ (by omega), slice_append_of_le _ _ _ _ (by omega),
        show 768 * P.k + 32 - 384 * P.k - EK.length = 0 by omega,
        show 768 * P.k + 64 - 384 * P.k - EK.length = (K.sha3_256 EK).length by omega, slice_all]
    · show z = _
      rw [List.append_assoc, List.append_assoc, slice_append_of_ge _ _ _ _ (by omega), hsLen,
        slice_append_of_ge _ _ _ _ (by omega), slice_append_of_ge _ _ _ _ (by omega), hHlen,
        show 768 * P.k + 64 - 384 * P.k - EK.length - 32 = 0 by omega,
        show 768 * P.k + 96 - 384 * P.k - EK.length - 32 = z.length by omega, slice_all]

end KeyGenProof

/-! ## Encapsulation and decapsulation -/

section KEM

variable (hR : Refines I S) (hL : S.Laws) (hP : P.Valid)
include hR hL hP

/-- **Algorithm 17.** On an encapsulation key record representing `EK` and
    32 bytes of randomness `m`, `encapsulate_internal` returns
    `(c, K)` where `(K, c) = ML-KEM.Encaps_internal(EK, m)`. -/
theorem encapsulateInternal_refines {ek : EncapsulationKey P.k} {EK : Bytes}
    (hek : EkRepr P K S ek EK) (g : ℕ → Byte) (m : Bytes) (hm : m.length = 32) :
    encapsulateInternal P K I g ek m =
      .ok ((encapsInternal P K S EK m).2, (encapsInternal P K S EK m).1) := by
  simp only [encapsulateInternal, hm, ne_eq, not_true_eq_false, ite_false, encapsInternal, G, H,
    stringSub_eq_slice, zero_add, show (32 : ℕ) + 32 = 64 by rfl, hek.h]
  rw [(pkeEncrypt_refines hR hL hP hek g m _ hm).1]

/-- **Algorithm 18.** On a decapsulation key record representing `DK` and a
    ciphertext of `ciphertext_size` bytes, `decapsulate` computes
    `ML-KEM.Decaps_internal(DK, c)`, implicit rejection included, for every
    initial content of the two buffers it allocates. -/
theorem decapsulate_refines {dk : DecapsulationKey P.k} {DK : Bytes} (hdk : DkRepr P K S dk DK)
    (g₁ g₂ : ℕ → Byte) (c : Bytes) (hc : c.length = P.ctSize) :
    decapsulate P K I g₁ g₂ dk c = decapsInternal P K S DK c := by
  have hk := P.dkSize_eq
  have hs : ∀ i : Fin P.k, Canonical (dk.s i) ∧
      toSpec (dk.s i) = S.byteDecode12 (slice (slice DK 0 (384 * P.k)) (384 * i.val) (384 * (i.val + 1))) := by
    intro i
    refine ⟨hdk.s_canon i, ?_⟩
    rw [hdk.s_spec, slice_slice _ _ _ _ _ (by have := i.isLt; nlinarith)]
    simp
  obtain ⟨hdec, hmlen⟩ := pkeDecrypt_refines hR hP dk _ hs c hc
  set m' := pkeDecrypt P I dk c with hm'
  have hglen : (K.sha3_512 (m' ++ dk.ek.h)).length = 64 := K.sha3_512_length _
  obtain ⟨henc, henclen⟩ := pkeEncrypt_refines hR hL hP hdk.ek g₁ m'
    (stringSub (K.sha3_512 (m' ++ dk.ek.h)) 32 32) hmlen
  unfold decapsulate
  simp only [← hm']
  rw [select_ctEqual g₂ c _ _ _ (by rw [hc, henclen]) (stringSub_length (by omega))
    (by simp), henc]
  simp only [decapsInternal, G, J, ← hdec, ← hdk.h, ← hdk.z, stringSub_eq_slice, zero_add,
    show (32 : ℕ) + 32 = 64 by rfl, Keccak.shake256Out]
  simp only [ne_eq, ite_not]

/-- **Implicit rejection.** `decapsulate` returns the candidate key `K'` from
    `G(m' ‖ h)` if re-encrypting `m'` reproduces the ciphertext, and
    `K̄ = J(z ‖ c)` otherwise. -/
theorem decapsulate_select {dk : DecapsulationKey P.k} {DK : Bytes} (hdk : DkRepr P K S dk DK)
    (g₁ g₂ : ℕ → Byte) (c : Bytes) (hc : c.length = P.ctSize) :
    let m' := kpkeDecrypt P S (slice DK 0 (384 * P.k)) c
    let h := slice DK (768 * P.k + 32) (768 * P.k + 64)
    let z := slice DK (768 * P.k + 64) (768 * P.k + 96)
    let c' := kpkeEncrypt P K S (slice DK (384 * P.k) (768 * P.k + 32)) m' (G K (m' ++ h)).2
    decapsulate P K I g₁ g₂ dk c = if c = c' then (G K (m' ++ h)).1 else J K (z ++ c) := by
  rw [decapsulate_refines hR hL hP hdk g₁ g₂ c hc]
  simp only [decapsInternal, ne_eq, ite_not]

end KEM

end OcamlPq.MLKEMAlg
