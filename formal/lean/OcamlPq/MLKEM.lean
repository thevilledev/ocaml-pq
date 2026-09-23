import OcamlPq.MLKEM.Field
import OcamlPq.MLKEM.Compress
import OcamlPq.MLKEM.Tables
import OcamlPq.MLKEM.NTTSpec
import OcamlPq.MLKEM.NTTLayers
import OcamlPq.MLKEM.NTTMath
import OcamlPq.MLKEM.NTTModel

/-!
# ML-KEM arithmetic core (FIPS 203)

Formal models of the field arithmetic, compression and NTT of
`lib/mlkem_engine.ml` (lines 105–228) and their refinement of FIPS 203.

* `OcamlPq.MLKEM.Field` — `field_reduce_once`, `field_reduce` (Barrett),
  `field_add/sub/mul/mul_sub/add_mul`.
* `OcamlPq.MLKEM.Compress` — `compress`, `decompress` vs. `Compress_d`,
  `Decompress_d`; rounding-error bound.
* `OcamlPq.MLKEM.Tables` — `zetas`, `gammas`, `ζ = 17`, `128⁻¹ = 3303`.
* `OcamlPq.MLKEM.NTTSpec` — FIPS 203 Algorithms 9–12.
* `OcamlPq.MLKEM.NTTLayers` — layer decomposition; `NTT⁻¹ ∘ NTT = id`,
  `NTT ∘ NTT⁻¹ = id`.
* `OcamlPq.MLKEM.NTTMath` — CRT characterisation and multiplication theorem.
* `OcamlPq.MLKEM.NTTModel` — models of `ntt`, `inverse_ntt`, `ntt_mul`,
  `poly_add`, `poly_sub` and their refinement of the FIPS algorithms.
-/
