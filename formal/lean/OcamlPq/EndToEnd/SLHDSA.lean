import OcamlPq.EndToEnd.SLHDSA.Prims
import OcamlPq.EndToEnd.SLHDSA.HashFunctions
import OcamlPq.EndToEnd.SLHDSA.Congr
import OcamlPq.EndToEnd.SLHDSA.Theorems

/-!
# SLH-DSA end to end: `slhdsa_engine.ml` over `slhdsa_hash.ml` is FIPS 205

Joins the SLH-DSA area (the engine, verified over *abstract* hash
primitives) with the Hash area (the primitives, verified against FIPS 180-4,
FIPS 202, FIPS 198-1 and RFC 8017).

* `Prims` — the byte-representation adapters `toU8`/`ofU8` (`List ℕ` ↔
  `List UInt8`); `codePrims` (the OCaml models of `Slhdsa_hash`) and
  `specPrims` (the standards), equal primitive by primitive (SHA-512-based
  ones below `2^61` input bytes); `SHAKE256Bytes` (FIPS 202 on bytes);
  output lengths.
* `HashFunctions` — `address_compressed = ADRS_c` for every address;
  the code's `thash`/`prf` are §11's F, H, T_ℓ, PRF; §11 over `codePrims` =
  §11 over `specPrims`; `codeFam`; **`hashOk_code`** (`HashOk` for all
  twelve sets).
* `Congr` — `Agree`: the FIPS 205 algorithms give the same result under
  two tweakable-hash families that agree on the calls the algorithms make
  (`T_ℓ` only with `ℓ ∈ {len, k}`, blocks of bounded length).
* `Theorems` — FIPS 205 Algorithms 18–20, 22, 24 over the specified
  primitives, and:
  - `keypairFromSeed_e2e` (Alg. 18), `signingKeyRootOk_e2e`;
  - `signFormatted_e2e` (Alg. 19), `verifyFormatted_e2e` (Alg. 20);
  - `sign_e2e`, `signDeterministic_e2e` (Alg. 22), `verify_e2e` (Alg. 24);
  - `keygen_sign_e2e`: signing with the key `keypair_from_seed` returns is
    Alg. 22 under the Alg. 18 key;
  - `verify_signFormatted_e2e`, `verify_sign_e2e`,
    `verify_signDeterministic_e2e`, `verify_sign_cross_platform`: the
    concrete verifier accepts the concrete signer's output, for every valid
    key, context, message and randomness, on every platform.

Statement-level findings (no discrepancy in the OCaml code within OCaml's
string sizes):

* The area's `Hash.addressCompressed_eq` (and so `thash_F`, `thash_H`,
  `thash_T`, `prf_eq`) assumes `layer, type < 256`; this is unnecessary —
  both sides keep the low byte (`addressCompressed_eq_compress`).
* The code's `thash` is not FIPS 205 §11 *as a function*: on one block it
  is `F`, never `T_1` (SHA-256 instead of SHA-512 when `n ≥ 24`), and its
  SHA-512 leaves FIPS 180-4 at `2^61` input bytes. Neither case is reached:
  `Congr` follows the algorithms' recursion to show it.
* `MGF1`'s "mask too long" check is absent in the code (the Hash area's
  `mgf1_no_length_check`); SLH-DSA asks for at most 49 bytes.
-/
