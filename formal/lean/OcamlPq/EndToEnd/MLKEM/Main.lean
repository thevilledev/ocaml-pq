import OcamlPq.EndToEnd.MLKEM.Prims
import OcamlPq.EndToEnd.MLKEM.Keccak

/-!
# ML-KEM end to end

The composition theorems of `MLKEMAlg` instantiated with the concrete
building blocks:

* implementation side: `MLKEMAlg.Impl` (models of `keygen_internal`,
  `parse_ek`, `encapsulate_internal`, `decapsulate`, …) with `I₀ g₁₂` (the
  arithmetic and encoding areas' models of lib/mlkem_engine.ml) and `K₀` (the
  Hash area's model of lib/keccak.ml);
* specification side: `MLKEMAlg.Spec` (FIPS 203 Algorithms 13-18, §7.2, §7.3)
  with `S₀` (the FIPS 203 transcriptions of Algorithms 5, 6, 9, 10, 11 and
  eq. 4.7/4.8 of the arithmetic and encoding areas) and `Kfips` (the Hash
  area's FIPS 202 SHA3-256/SHA3-512/SHAKE128/SHAKE256).

All hypothesis bundles of the `MLKEMAlg` theorems are discharged
(`refines`, `laws`, `algLaws`, `compressEncode_one`, `decodeDecompress_one`,
`K₀_eq_Kfips`). The only hypothesis left is the noise bound of the
correctness theorem, a property of the FIPS 203 algorithms themselves.

`sample_ntt` (FIPS 203 Algorithm 7) may in principle not terminate. As in
`MLKEMAlg`, both sides use its total extension (`sampleNttTotal`,
`Spec.sampleNTTTotal`, 0 on divergence); `MLKEMAlg.sampleNtt_spec` shows that
the OCaml recursion diverges on exactly the inputs on which Algorithm 7 does,
so the theorems describe every terminating run.

Every theorem holds for every content of every uninitialised buffer:
`g₁₂` (`encode_12`), `g` (`encode_ek` in `keygen_internal`, the ciphertext
buffer of `pke_encrypt`), `g₁`, `g₂`, `g₃`.

`KEMResults P` collects the statements for one parameter set;
`mlkem512_endToEnd`, `mlkem768_endToEnd`, `mlkem1024_endToEnd` prove them for
the three parameter sets of the library.
-/

namespace OcamlPq.EndToEnd.MLKEM

open OcamlPq.MLKEMAlg OcamlPq.MLKEMAlg.Spec OcamlPq.MLKEMAlg.Impl

/-! ## For every valid parameter set -/

section Generic

variable {P : Params} (g₁₂ : ℕ → Byte)

/-- **§7.2 encapsulation key check.** `parse_ek` (= `encapsulation_key_of_octets`)
    succeeds exactly on the octet strings that pass the FIPS 203 type and
    modulus checks. -/
theorem parseEk_e2e (EK : Bytes) :
    (∃ ek, parseEk P K₀ (I₀ g₁₂) EK = .ok ek) ↔ ekCheck P S₀ EK :=
  parseEk_ok_iff (refines g₁₂) EK

/-- A record returned by `parse_ek` represents its input octets. -/
theorem parseEk_repr_e2e {EK : Bytes} {ek : EncapsulationKey P.k}
    (h : parseEk P K₀ (I₀ g₁₂) EK = .ok ek) : EkRepr P K₀ S₀ ek EK :=
  parseEk_repr (refines g₁₂) h

/-- **Expanded decapsulation key check.** `decapsulation_key_of_expanded`
    succeeds iff the FIPS 203 §7.3 checks pass (length, `H(ek)`) and, in
    addition, the embedded `ek` passes the §7.2 modulus check and every
    12-bit coefficient of `ŝ` is below `q` (stricter than FIPS 203). -/
theorem ofExpanded_e2e (DK : Bytes) :
    (∃ dk, decapsulationKeyOfExpanded P K₀ (I₀ g₁₂) DK = .ok dk) ↔
      dkCheck P Kfips DK ∧ ekCheck P S₀ (slice DK (384 * P.k) (768 * P.k + 32)) ∧
      ∀ i : Fin P.k, S₀.byteEncode12 (S₀.byteDecode12 (slice DK (384 * i.val) (384 * (i.val + 1)))) =
        slice DK (384 * i.val) (384 * (i.val + 1)) := by
  rw [← K₀_eq_Kfips]
  exact ofExpanded_ok_iff (refines g₁₂) DK

/-- A record returned by `decapsulation_key_of_expanded` represents its input. -/
theorem ofExpanded_repr_e2e {DK : Bytes} {dk : DecapsulationKey P.k}
    (h : decapsulationKeyOfExpanded P K₀ (I₀ g₁₂) DK = .ok dk) : DkRepr P K₀ S₀ dk DK :=
  (ofExpanded_repr (refines g₁₂) h).1

variable (hP : P.Valid)
include hP

/-- **Key generation, FIPS 203 Algorithms 13 and 16.** For 32-byte `d`, `z`,
    `keygen_internal ~d ~z` succeeds; its encapsulation key serialises to
    `ek` and its expanded decapsulation key to `dk`, where
    `(ek, dk) = ML-KEM.KeyGen_internal(d, z)` computed with the FIPS 202 hash
    functions and the FIPS 203 building blocks. The returned records represent
    those octets. -/
theorem keygen_e2e (g : ℕ → Byte) (d z : Bytes) (hd : d.length = 32) (hz : z.length = 32) :
    ∃ dk, keygenInternal P K₀ (I₀ g₁₂) g d z = .ok dk ∧ dk.seed = some (d ++ z) ∧ dk.z = z ∧
      encapsulationKeyToOctets P dk.ek = (keyGenInternal P Kfips S₀ d z).1 ∧
      (∀ g', decapsulationKeyToExpanded P (I₀ g₁₂) g' dk = (keyGenInternal P Kfips S₀ d z).2) ∧
      EkRepr P K₀ S₀ dk.ek (keyGenInternal P Kfips S₀ d z).1 ∧
      DkRepr P K₀ S₀ dk (keyGenInternal P Kfips S₀ d z).2 := by
  rw [← K₀_eq_Kfips]
  exact keygenInternal_refines (refines g₁₂) laws hP g d z hd hz

/-- **Encapsulation, FIPS 203 Algorithm 17.** On a record representing the
    octets `EK` (as returned by `parse_ek EK` or `keygen_internal`) and 32
    bytes `m`, `encapsulate_internal` returns `(c, K)` where
    `(K, c) = ML-KEM.Encaps_internal(EK, m)`. -/
theorem encaps_e2e {ek : EncapsulationKey P.k} {EK : Bytes} (hek : EkRepr P K₀ S₀ ek EK)
    (g : ℕ → Byte) (m : Bytes) (hm : m.length = 32) :
    encapsulateInternal P K₀ (I₀ g₁₂) g ek m =
      .ok ((encapsInternal P Kfips S₀ EK m).2, (encapsInternal P Kfips S₀ EK m).1) := by
  rw [← K₀_eq_Kfips]
  exact encapsulateInternal_refines (refines g₁₂) laws hP hek g m hm

/-- **Decapsulation, FIPS 203 Algorithm 18.** On a record representing the
    expanded key `DK` (as returned by `decapsulation_key_of_expanded DK` or
    `keygen_internal`) and a ciphertext of the right length, `decapsulate`
    computes `ML-KEM.Decaps_internal(DK, c)`, implicit rejection included. -/
theorem decaps_e2e {dk : DecapsulationKey P.k} {DK : Bytes} (hdk : DkRepr P K₀ S₀ dk DK)
    (g₁ g₂ : ℕ → Byte) (c : Bytes) (hc : c.length = P.ctSize) :
    decapsulate P K₀ (I₀ g₁₂) g₁ g₂ dk c = decapsInternal P Kfips S₀ DK c := by
  rw [← K₀_eq_Kfips]
  exact decapsulate_refines (refines g₁₂) laws hP hdk g₁ g₂ c hc

/-- **Implicit rejection.** `decapsulate` returns `K'` from `G(m' ‖ h)` if
    re-encrypting `m' = K-PKE.Decrypt(dk_PKE, c)` reproduces `c`, and
    `K̄ = J(z ‖ c)` otherwise, with FIPS 202's SHA3-512 and SHAKE256. -/
theorem decaps_select_e2e {dk : DecapsulationKey P.k} {DK : Bytes} (hdk : DkRepr P K₀ S₀ dk DK)
    (g₁ g₂ : ℕ → Byte) (c : Bytes) (hc : c.length = P.ctSize) :
    let m' := kpkeDecrypt P S₀ (slice DK 0 (384 * P.k)) c
    let h := slice DK (768 * P.k + 32) (768 * P.k + 64)
    let z := slice DK (768 * P.k + 64) (768 * P.k + 96)
    let c' := kpkeEncrypt P Kfips S₀ (slice DK (384 * P.k) (768 * P.k + 32)) m' (G Kfips (m' ++ h)).2
    decapsulate P K₀ (I₀ g₁₂) g₁ g₂ dk c =
      if c = c' then (G Kfips (m' ++ h)).1 else J Kfips (z ++ c) := by
  rw [← K₀_eq_Kfips]
  exact decapsulate_select (refines g₁₂) laws hP hdk g₁ g₂ c hc

/-- **Correctness of the implementation.** For 32-byte `d`, `z`, `m`:
    `keygen_internal ~d ~z` returns a key `dk`,
    `encapsulate_internal dk.ek ~randomness:m` returns `(c, K)`, and
    `decapsulate dk c = K`, provided the noise of the FIPS 203 encryption
    (`kpkeNoise`, computed with the FIPS primitives) has centred absolute value
    below `⌈q/4⌋ = 832` in every coefficient. -/
theorem correct_e2e (g g₁ g₂ g₃ : ℕ → Byte) (d z m : Bytes) (hd : d.length = 32)
    (hz : z.length = 32) (hm : m.length = 32)
    (hn : ∀ i, cabs (kpkeNoise P Kfips S₀ d m
      (G Kfips (m ++ H Kfips (keyGenInternal P Kfips S₀ d z).1)).2 i) < 832) :
    ∃ dk c Kss, keygenInternal P K₀ (I₀ g₁₂) g d z = .ok dk ∧
      encapsulateInternal P K₀ (I₀ g₁₂) g₁ dk.ek m = .ok (c, Kss) ∧
      decapsulate P K₀ (I₀ g₁₂) g₂ g₃ dk c = Kss := by
  rw [← K₀_eq_Kfips] at hn
  exact impl_mlkem_correct (refines g₁₂) laws algLaws hP compressEncode_one decodeDecompress_one
    g g₁ g₂ g₃ d z m hd hz hm hn

omit g₁₂ in
/-- **Correctness of FIPS 203 with the concrete primitives** (spec level):
    under the same noise bound, `Decaps_internal(dk, c) = K` for
    `(ek, dk) = KeyGen_internal(d, z)` and `(K, c) = Encaps_internal(ek, m)`. -/
theorem fips_correct (d z m : Bytes) (hm : m.length = 32)
    (hn : ∀ i, cabs (kpkeNoise P Kfips S₀ d m
      (G Kfips (m ++ H Kfips (keyGenInternal P Kfips S₀ d z).1)).2 i) < 832) :
    decapsInternal P Kfips S₀ (keyGenInternal P Kfips S₀ d z).2
        (encapsInternal P Kfips S₀ (keyGenInternal P Kfips S₀ d z).1 m).2 =
      (encapsInternal P Kfips S₀ (keyGenInternal P Kfips S₀ d z).1 m).1 :=
  mlkem_correct (refines fun _ => 0) laws algLaws hP compressEncode_one decodeDecompress_one
    d z m hm hn

end Generic

/-! ## The three parameter sets -/

/-- The end-to-end results for the parameter set `P`, for every content of
    every uninitialised buffer. Implementation side: the OCaml models with
    `I₀ g₁₂` and `K₀`; specification side: FIPS 203 with `S₀` and FIPS 202
    (`Kfips`). -/
structure KEMResults (P : Params) : Prop where
  /-- `keygen_internal` computes `ML-KEM.KeyGen_internal` (Algorithms 13, 16). -/
  keyGen_ok : ∀ (g₁₂ g : ℕ → Byte) (d z : Bytes), d.length = 32 → z.length = 32 →
    ∃ dk, keygenInternal P K₀ (I₀ g₁₂) g d z = .ok dk ∧ dk.seed = some (d ++ z) ∧ dk.z = z ∧
      encapsulationKeyToOctets P dk.ek = (keyGenInternal P Kfips S₀ d z).1 ∧
      (∀ g', decapsulationKeyToExpanded P (I₀ g₁₂) g' dk = (keyGenInternal P Kfips S₀ d z).2) ∧
      EkRepr P K₀ S₀ dk.ek (keyGenInternal P Kfips S₀ d z).1 ∧
      DkRepr P K₀ S₀ dk (keyGenInternal P Kfips S₀ d z).2
  /-- `parse_ek` implements the §7.2 encapsulation key check. -/
  parseEk_ok_iff : ∀ (g₁₂ : ℕ → Byte) (EK : Bytes),
    (∃ ek, parseEk P K₀ (I₀ g₁₂) EK = .ok ek) ↔ ekCheck P S₀ EK
  /-- `parse_ek` returns a record representing its input. -/
  parseEk_repr : ∀ (g₁₂ : ℕ → Byte) (EK : Bytes) (ek : EncapsulationKey P.k),
    parseEk P K₀ (I₀ g₁₂) EK = .ok ek → EkRepr P K₀ S₀ ek EK
  /-- `decapsulation_key_of_expanded` returns a record representing its input. -/
  ofExpanded_repr : ∀ (g₁₂ : ℕ → Byte) (DK : Bytes) (dk : DecapsulationKey P.k),
    decapsulationKeyOfExpanded P K₀ (I₀ g₁₂) DK = .ok dk → DkRepr P K₀ S₀ dk DK
  /-- `encapsulate_internal` computes `ML-KEM.Encaps_internal` (Algorithm 17). -/
  encaps_eq : ∀ (g₁₂ g : ℕ → Byte) (EK : Bytes) (ek : EncapsulationKey P.k),
    EkRepr P K₀ S₀ ek EK → ∀ m : Bytes, m.length = 32 →
      encapsulateInternal P K₀ (I₀ g₁₂) g ek m =
        .ok ((encapsInternal P Kfips S₀ EK m).2, (encapsInternal P Kfips S₀ EK m).1)
  /-- `decapsulate` computes `ML-KEM.Decaps_internal` (Algorithm 18). -/
  decaps_eq : ∀ (g₁₂ g₁ g₂ : ℕ → Byte) (DK : Bytes) (dk : DecapsulationKey P.k),
    DkRepr P K₀ S₀ dk DK → ∀ c : Bytes, c.length = P.ctSize →
      decapsulate P K₀ (I₀ g₁₂) g₁ g₂ dk c = decapsInternal P Kfips S₀ DK c
  /-- Implicit rejection. -/
  decaps_select : ∀ (g₁₂ g₁ g₂ : ℕ → Byte) (DK : Bytes) (dk : DecapsulationKey P.k),
    DkRepr P K₀ S₀ dk DK → ∀ c : Bytes, c.length = P.ctSize →
      let m' := kpkeDecrypt P S₀ (slice DK 0 (384 * P.k)) c
      let h := slice DK (768 * P.k + 32) (768 * P.k + 64)
      let z := slice DK (768 * P.k + 64) (768 * P.k + 96)
      let c' := kpkeEncrypt P Kfips S₀ (slice DK (384 * P.k) (768 * P.k + 32)) m' (G Kfips (m' ++ h)).2
      decapsulate P K₀ (I₀ g₁₂) g₁ g₂ dk c =
        if c = c' then (G Kfips (m' ++ h)).1 else J Kfips (z ++ c)
  /-- Correctness of the OCaml functions under the FIPS 203 noise bound. -/
  correct : ∀ (g₁₂ g g₁ g₂ g₃ : ℕ → Byte) (d z m : Bytes), d.length = 32 → z.length = 32 →
    m.length = 32 →
    (∀ i, cabs (kpkeNoise P Kfips S₀ d m
      (G Kfips (m ++ H Kfips (keyGenInternal P Kfips S₀ d z).1)).2 i) < 832) →
    ∃ dk c Kss, keygenInternal P K₀ (I₀ g₁₂) g d z = .ok dk ∧
      encapsulateInternal P K₀ (I₀ g₁₂) g₁ dk.ek m = .ok (c, Kss) ∧
      decapsulate P K₀ (I₀ g₁₂) g₂ g₃ dk c = Kss

theorem endToEnd {P : Params} (hP : P.Valid) : KEMResults P where
  keyGen_ok g₁₂ g d z hd hz := keygen_e2e g₁₂ hP g d z hd hz
  parseEk_ok_iff g₁₂ EK := parseEk_e2e g₁₂ EK
  parseEk_repr g₁₂ _ _ h := parseEk_repr_e2e g₁₂ h
  ofExpanded_repr g₁₂ _ _ h := ofExpanded_repr_e2e g₁₂ h
  encaps_eq g₁₂ g _ _ hek m hm := encaps_e2e g₁₂ hP hek g m hm
  decaps_eq g₁₂ g₁ g₂ _ _ hdk c hc := decaps_e2e g₁₂ hP hdk g₁ g₂ c hc
  decaps_select g₁₂ g₁ g₂ _ _ hdk c hc := decaps_select_e2e g₁₂ hP hdk g₁ g₂ c hc
  correct g₁₂ g g₁ g₂ g₃ d z m hd hz hm hn := correct_e2e g₁₂ hP g g₁ g₂ g₃ d z m hd hz hm hn

/-- **ML-KEM-512 end to end.** -/
theorem mlkem512_endToEnd : KEMResults mlkem512 := endToEnd (Or.inl rfl)

/-- **ML-KEM-768 end to end.** -/
theorem mlkem768_endToEnd : KEMResults mlkem768 := endToEnd (Or.inr (Or.inl rfl))

/-- **ML-KEM-1024 end to end.** -/
theorem mlkem1024_endToEnd : KEMResults mlkem1024 := endToEnd (Or.inr (Or.inr rfl))

end OcamlPq.EndToEnd.MLKEM
