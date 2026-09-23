import OcamlPq.Encoding.Digits
import OcamlPq.Encoding.Spec
import OcamlPq.Encoding.Bytes
import OcamlPq.Encoding.Packer
import OcamlPq.Encoding.Mlkem12
import OcamlPq.Encoding.MlkemCompressed
import OcamlPq.Encoding.MlkemLayout
import OcamlPq.Encoding.HintSpec
import OcamlPq.Encoding.Hint
import OcamlPq.Encoding.HintRoundTrip
import OcamlPq.Encoding.MldsaPack
import OcamlPq.Encoding.MldsaLayout
import OcamlPq.Encoding.MldsaSk

/-!
# Byte encodings of ML-KEM and ML-DSA

* `Digits`, `Spec`: little-endian digit regrouping and the FIPS 203/204 bit
  and byte algorithms (FIPS 203 Algorithms 3–6, FIPS 204 Algorithms 9–13,
  16–19).
* `Packer`: the generic accumulator packer `pack_codes`/`unpack_codes`.
* `Mlkem12`, `MlkemCompressed`, `MlkemLayout`: ML-KEM `encode_12`,
  `decode_12`, `encode_compressed`, `decode_compressed`, key and ciphertext
  layouts.
* `HintSpec`, `Hint`, `HintRoundTrip`: FIPS 204 Algorithms 20/21 and the
  hint codec of `encode_signature`/`decode_signature`, including canonicity.
* `MldsaPack`, `MldsaLayout`, `MldsaSk`: ML-DSA packings, `u16_le`, key and
  signature layouts.
-/
