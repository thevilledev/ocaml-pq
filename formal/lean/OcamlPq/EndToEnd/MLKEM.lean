import OcamlPq.EndToEnd.MLKEM.Adapters
import OcamlPq.EndToEnd.MLKEM.Prims
import OcamlPq.EndToEnd.MLKEM.Keccak
import OcamlPq.EndToEnd.MLKEM.Main

/-!
# ML-KEM end to end: lib/mlkem_engine.ml + lib/keccak.ml = FIPS 203 + FIPS 202

`MLKEMAlg` proves the sampling, K-PKE and KEM layers of lib/mlkem_engine.ml
correct against FIPS 203 Algorithms 13-18, taking the arithmetic, the byte
encodings and the hash functions as hypotheses (`Refines I S`,
`SpecPrims.Laws`, `SpecPrims.AlgLaws`, a `Keccak` structure, and the shape
of `ByteEncode₁ ∘ Compress₁`). This directory discharges those hypotheses with
the models and transcriptions verified by the `MLKEM`, `Encoding` and `Hash`
areas.

| Module | Content |
|---|---|
| `Adapters` | conversions between the areas' representations (`Array ℤ`, `List ℕ`, `Fin 256 → ℤ`, `ℕ → ZMod q`, `Fin 256 → ZMod q`, `List (Fin 256)`) |
| `Prims` | `I₀ g₁₂ : ImplPrims` (OCaml models), `S₀ : SpecPrims` (FIPS 203 transcriptions); `refines : Refines (I₀ g₁₂) S₀`, `laws`, `algLaws`, `compressEncode_one`, `decodeDecompress_one` |
| `Keccak` | `K₀` (lib/keccak.ml models), `Kfips` (FIPS 202), `K₀_eq_Kfips`, `K₀_shake128Out`, `K₀_shake256Out` |
| `Main` | `keygen_e2e`, `encaps_e2e`, `decaps_e2e`, `decaps_select_e2e`, `parseEk_e2e`, `ofExpanded_e2e`, `correct_e2e`, `fips_correct`; `mlkem512_endToEnd`, `mlkem768_endToEnd`, `mlkem1024_endToEnd` |

## Headline results (for each of ML-KEM-512/768/1024, `KEMResults P`)

With the OCaml models (`MLKEMAlg.Impl` instantiated with `I₀ g₁₂` and `K₀`)
on one side and FIPS 203 (`MLKEMAlg.Spec` with `S₀`) over FIPS 202 (`Kfips`)
on the other, for every content of every uninitialised buffer:

* `keyGen_ok`: `keygen_internal` = `ML-KEM.KeyGen_internal` (Alg. 13, 16);
* `parseEk_ok_iff`: `parse_ek` succeeds iff the §7.2 check passes;
* `encaps_eq`: `encapsulate_internal` = `ML-KEM.Encaps_internal` (Alg. 17);
* `decaps_eq`: `decapsulate` = `ML-KEM.Decaps_internal` (Alg. 18);
* `decaps_select`: the implicit-rejection selection;
* `correct`: `decapsulate (encapsulate (keygen))` returns the encapsulated
  key, under the FIPS 203 noise bound (`cabs < 832`), the only remaining
  hypothesis.

## Representation mismatches bridged here

* `ImplPrims.encode12` has no buffer argument, while `encode_12` writes into
  `Bytes.create` (uninitialised). `I₀` takes that buffer as a parameter
  `g₁₂`; everything is proved for all `g₁₂`, and `I₀_encode12_indep` shows the
  result does not depend on it.
* The encoding area's `encode_compressed` model takes `compress` as a
  parameter and requires `compress x d < 2^d` for *every* `x`. The OCaml
  `compress` ends with `land ((1 lsl d) - 1)`, which gives this for every
  `int` (`land_mask_bounds`), so no restriction is needed.
* `MLKEMAlg.Correctness` has its own transcription of `ByteEncode₁ ∘ Compress₁`,
  `Decompress₁ ∘ ByteDecode₁` and `BytesToBits`; it agrees with the encoding
  and arithmetic areas' transcriptions (`compressEncode_one`,
  `decodeDecompress_one`, `bytesToBits_eq`).
* `MLKEMAlg.Keccak` models SHAKE as an infinite stream; the OCaml functions
  take an output length. The stream is read off the model, and
  `K₀_shake128Out` / `K₀_shake256Out` (from the Hash area's prefix
  consistency) show that every call `shake ~output_length:L x` of the models
  is the OCaml model's output.
-/
