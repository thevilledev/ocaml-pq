import OcamlPq.Hash.KeccakModel
import OcamlPq.Hash.KeccakSpec
import OcamlPq.Hash.KeccakConstants
import OcamlPq.Hash.KeccakPermute
import OcamlPq.Hash.SpongeLemmas
import OcamlPq.Hash.SpongeAbsorb
import OcamlPq.Hash.SpongeSqueeze
import OcamlPq.Hash.Sponge
import OcamlPq.Hash.TurboShakeSpec
import OcamlPq.Hash.TurboShake
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
# Hash primitives: Keccak / SHA-3 / SHAKE / TurboSHAKE, SHA-256, SHA-512, HMAC, MGF1

Formal verification of the in-house hash code of the library against
FIPS 202, RFC 9861, FIPS 180-4, FIPS 198-1 and RFC 8017.

## Main theorems

* `Keccak.permute_eq_KeccakF` — `permute` (`lib/keccak.ml`) is KECCAK-f[1600]
  on every 25-lane state (lane `x + 5y`, bit `z` least significant first);
  `Keccak.permuteFrom_eq_KeccakP` — `permute_from first` is
  KECCAK-p[1600, 24 − first], so `permute_from 12` is TurboSHAKE's
  KECCAK-p[1600, 12].
* `Keccak.sha3_256_eq`, `sha3_512_eq`, `shake128_eq`, `shake256_eq` — the four
  entry points are FIPS 202 SHA3-256/SHA3-512/SHAKE128/SHAKE256 on every input
  (and every output length for SHAKE); `Keccak.spongeWith_eq` for the generic
  `sponge`, and `Keccak.spongeWith_eq_of` for `sponge_with` over any
  permutation.
* `Keccak.turboshake128_eq`, `turboshake256_eq` — `turboshake128` and
  `turboshake256` are RFC 9861 TurboSHAKE128/TurboSHAKE256 on every input,
  domain byte in `0x01`–`0x7F` and output length;
  `Keccak.turboSHAKE_eq_pad101` — RFC 9861's padding is `pad10*1`;
  `Keccak.rfc9861Turboshake128_ok` etc. — `Mlkem.Rfc9861` and its errors.
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

`mldsa/mldsa_keccak.ml` and lines 1–126 of `slhdsa/slhdsa_hash.ml` are
textual copies of `lib/keccak.ml` minus its `sha3_256`, `sha3_512`,
`turboshake128` and `turboshake256` definitions. Checked mechanically with

```
diff lib/keccak.ml mldsa/mldsa_keccak.ml
sed -n 1,126p slhdsa/slhdsa_hash.ml | diff lib/keccak.ml -
```

both of which print only
```
125,126d124
< let sha3_256 input = sponge ~rate:136 ~suffix:0x06 ~output_length:32 input
< let sha3_512 input = sponge ~rate:72 ~suffix:0x06 ~output_length:64 input
129,135d126
< 
< (* TurboSHAKE (RFC 9861): the sponge of SHAKE over KECCAK-p[1600, 12], with the
<    domain separation byte [domain] as its suffix. *)
< let turboshake128 ~domain ~output_length input =
<   sponge_with ~permute:(permute_from 12) ~rate:168 ~suffix:domain ~output_length input
< let turboshake256 ~domain ~output_length input =
<   sponge_with ~permute:(permute_from 12) ~rate:136 ~suffix:domain ~output_length input
```
so every theorem about `permute_from`, `sponge_with`, `sponge`, `shake128`
and `shake256` here applies verbatim to `Mldsa_keccak` and `Slhdsa_hash`.
-/
