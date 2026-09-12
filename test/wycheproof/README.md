# Wycheproof test vectors

This directory contains the complete Wycheproof corpus applicable to the
algorithms implemented by `ocaml-pq` at upstream revision
`3fa63dd0344abb611f1fb1d77e119938603ea230`:

- 1,725 ML-KEM tests covering key generation, encapsulation, seed-based
  decapsulation, and semi-expanded-key decapsulation for ML-KEM-512,
  ML-KEM-768, and ML-KEM-1024;
- 1,138 ML-DSA tests covering seed-based signing, expanded-key signing, and
  verification for ML-DSA-44, ML-DSA-65, and ML-DSA-87.

Wycheproof does not provide SLH-DSA vectors at this revision. SLH-DSA remains
covered by the NIST ACVP vectors in `../slhdsa_vectors`.

The upstream JSON files under `testvectors_v1` are converted to a compact,
line-oriented format so the OCaml tests need no JSON library. Cryptographic
field values, test identifiers, results, and flags are unchanged. Repeated
ML-DSA group keys are emitted once at an explicit group boundary; JSON schema
metadata, DER-only fields, and explanatory comments are omitted.

`import.sh SOURCE_DIR TARGET_DIR` reproduces the conversion with `jq` from a
Wycheproof checkout. `SOURCE_SHA256SUMS` records the selected upstream JSON
files, and `SHA256SUMS` records the derived files in this directory.

The vectors and the copied `LICENSE` are from
[C2SP/wycheproof](https://github.com/C2SP/wycheproof) and are distributed under
the Apache License 2.0. They are test data only; the libraries have no runtime
dependency on Wycheproof or `jq`.

## Case counts

| Algorithm | Keygen | Encap | Seed decap | Expanded decap | Seed sign | Expanded sign | Verify | Total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| ML-KEM-512 | 100 | 261 | 200 | 9 | - | - | - | 570 |
| ML-KEM-768 | 100 | 265 | 201 | 9 | - | - | - | 575 |
| ML-KEM-1024 | 100 | 269 | 202 | 9 | - | - | - | 580 |
| ML-DSA-44 | - | - | - | - | 86 | 73 | 180 | 339 |
| ML-DSA-65 | - | - | - | - | 105 | 78 | 210 | 393 |
| ML-DSA-87 | - | - | - | - | 96 | 69 | 241 | 406 |
| **Total** | **300** | **795** | **603** | **27** | **287** | **220** | **631** | **2,863** |
