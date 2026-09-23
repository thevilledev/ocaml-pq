import OcamlPq.Hash.KeccakModel
import OcamlPq.Hash.KeccakSpec
import OcamlPq.Hash.KeccakConstants
import OcamlPq.Hash.KeccakPermute
import OcamlPq.Hash.SpongeLemmas
import OcamlPq.Hash.SpongeAbsorb
import OcamlPq.Hash.SpongeSqueeze
import OcamlPq.Hash.Sponge
import OcamlPq.Hash.Sha2Spec
import OcamlPq.Hash.Sha2Model
import OcamlPq.Hash.Sha2Constants
import OcamlPq.Hash.Sha2Lemmas
import OcamlPq.Hash.Sha2Bytes
import OcamlPq.Hash.Sha256
import OcamlPq.Hash.Sha512
import OcamlPq.Hash.HmacMgf1
import OcamlPq.Hash.KAT
import OcamlPq.Hash.Safety

/-!
# Hash primitives: Keccak / SHA-3 / SHAKE, SHA-256, SHA-512, HMAC, MGF1

Formal verification of the in-house hash code of the library against
FIPS 202, FIPS 180-4, FIPS 198-1 and RFC 8017.

## Main theorems

* `Keccak.permute_eq_KeccakF` — `permute` (`lib/keccak.ml`) is KECCAK-f[1600]
  on every 25-lane state (lane `x + 5y`, bit `z` least significant first).
* `Keccak.sha3_256_eq`, `sha3_512_eq`, `shake128_eq`, `shake256_eq` — the four
  entry points are FIPS 202 SHA3-256/SHA3-512/SHAKE128/SHAKE256 on every input
  (and every output length for SHAKE); `Keccak.spongeWith_eq` for the generic
  `sponge`.
* `Keccak.shake128_prefix`, `shake256_prefix` — prefix consistency of SHAKE
  output lengths; `Keccak.sponge_final_state` — permutation count of the
  squeeze loop; `Keccak.fips202Shake128_neg` — `Mlkem.Fips202` rejects negative
  lengths.
* `Sha2.sha256_eq`, `Sha2.sha512_eq` — `sha256`/`sha512`
  (`slhdsa/slhdsa_hash.ml`) are FIPS 180-4 SHA-256 (every input) and SHA-512
  (inputs of fewer than `2^61` bytes, i.e. every OCaml string).
* `Sha2.hmacSha256_eq`, `hmacSha512_eq`, `hmac_eq` — FIPS 198-1 HMAC.
* `Sha2.mgf1_eq`, `mgf1Sha256_eq`, `mgf1Sha512_eq` — RFC 8017 MGF1.
* Constants: `Keccak.roundConstants_eq_RC`, `Keccak.rho_eq`,
  `Keccak.rotation_from_walk`, `Keccak.pi_position`,
  `Sha2.sha256Constants_eq`, `sha512Constants_eq`, `sha256H0_eq`, `sha512H0_eq`.
* `KAT.*` — published digests hold for the *specifications*.
* `Safety.*` — indices, shift amounts, `int` ranges.

## The two copies of `keccak.ml`

`mldsa/mldsa_keccak.ml` and lines 1–118 of `slhdsa/slhdsa_hash.ml` are
textual copies of `lib/keccak.ml` minus its last two lines (the `sha3_256` and
`sha3_512` definitions). Checked mechanically with

```
diff lib/keccak.ml mldsa/mldsa_keccak.ml
sed -n 1,118p slhdsa/slhdsa_hash.ml | diff lib/keccak.ml -
```

both of which print only
```
117,118d116
< let sha3_256 input = sponge ~rate:136 ~suffix:0x06 ~output_length:32 input
< let sha3_512 input = sponge ~rate:72 ~suffix:0x06 ~output_length:64 input
```
so every theorem about `sponge`, `shake128`, `shake256` here applies verbatim
to `Mldsa_keccak` and `Slhdsa_hash`.
-/
