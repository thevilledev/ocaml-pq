import OcamlPq.MLKEMAlg.Basic
import OcamlPq.MLKEMAlg.Params
import OcamlPq.MLKEMAlg.SampleCBD
import OcamlPq.MLKEMAlg.SampleNTT
import OcamlPq.MLKEMAlg.ConstTime
import OcamlPq.MLKEMAlg.Interface
import OcamlPq.MLKEMAlg.Spec
import OcamlPq.MLKEMAlg.Impl
import OcamlPq.MLKEMAlg.Lemmas
import OcamlPq.MLKEMAlg.RefinePKE
import OcamlPq.MLKEMAlg.RefineKEM
import OcamlPq.MLKEMAlg.Keys
import OcamlPq.MLKEMAlg.Portability
import OcamlPq.MLKEMAlg.Correctness

/-!
# ML-KEM sampling, K-PKE and the KEM composition

Verification of lib/mlkem_engine.ml lines 292-525 (and the size constants at
lines 60-75) against FIPS 203 Algorithms 7, 8 and 13-18 and the input checks
of §7.

| Module | Content |
|---|---|
| `Params` | parameter sets = FIPS 203 Table 2; sizes = Table 3 |
| `SampleCBD` | `sample_cbd` = Algorithm 8 ∘ PRF (`sampleCbd_spec`) |
| `SampleNTT` | `sample_ntt` with its restart = Algorithm 7 (`sampleNtt_spec`, `sampleNtt_portable`) |
| `ConstTime` | `ct_equal` (`ctEqual_spec`), `select_secret` (`selectSecret_spec`) |
| `Interface` | the arithmetic and encoding building blocks as hypotheses (`Refines`, `SpecPrims.Laws`) |
| `Spec` | FIPS 203 Algorithms 13-18, §7.2 and §7.3 checks |
| `Impl` | models of `keygen_internal`, `parse_ek`, `pke_encrypt`, `pke_decrypt`, `encapsulate_internal`, `decapsulate`, key (de)serialisation |
| `RefinePKE` | `pkeEncrypt_refines` (Alg. 14), `pkeDecrypt_refines` (Alg. 15), `matrix_spec` |
| `RefineKEM` | `keygenInternal_refines` (Alg. 13 + 16), `encapsulateInternal_refines` (Alg. 17), `decapsulate_refines` / `decapsulate_select` (Alg. 18) |
| `Keys` | `parseEk_ok_iff` (§7.2), `ofExpanded_ok_iff` (§7.3 and more), round trips |
| `Portability` | offsets, nonces and sizes of the composition layer |
| `Correctness` | K-PKE decryption identity `w = μ + n`, `kpke_correct`, `mlkem_correct`, `impl_mlkem_correct` (noise below `⌈q/4⌋`) |

Assumptions (all explicit arguments of the theorems that use them):

* `Keccak`: SHA3-256/512 return 32/64 bytes; SHAKE128/256 outputs are prefixes
  of one infinite stream per input.
* `Refines I S`: the arithmetic layer and the byte encodings refine their FIPS
  203 counterparts on canonical inputs (proved elsewhere in the project).
* `SpecPrims.Laws`: NTT⁻¹ is additive; ByteDecode₁₂ ∘ ByteEncode₁₂ = id.
* Only for `Correctness`: `SpecPrims.AlgLaws` (NTT additive, NTT ∘ NTT⁻¹ = id,
  MultiplyNTTs commutative, associative, distributive), and that the spec's
  `ByteEncode₁ ∘ Compress₁` / `Decompress₁ ∘ ByteDecode₁` are the FIPS 203
  formulas transcribed in `Correctness.lean`.

Deviation from FIPS 203 (not a safety bug): `decapsulation_key_of_expanded`
accepts a strict subset of the keys that pass FIPS 203 §7.3. Besides the
length and hash checks it also requires the embedded encapsulation key to pass
the §7.2 modulus check, and every 12-bit coefficient of `ŝ` to be below `q`
(`ofExpanded_ok_iff`). A key with an unreduced `ŝ` coefficient, or with an
unreduced `t̂` coefficient and a matching `H(ek)`, passes FIPS 203 §7.3 and is
rejected by the implementation.
-/
