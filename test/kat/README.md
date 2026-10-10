# Known-answer subset

Release archives omit the full test corpora in `../vectors`,
`../mldsa_vectors`, `../slhdsa_vectors`, and `../wycheproof`; together they
are about 21 MB compressed (see `.gitattributes` and issue #15). This
directory is what the package tests check against in a release archive:
about one known answer per parameter set and operation. From a git checkout
the tests check this subset and the full corpora.

Each file keeps the name and format of the file it was taken from, so the
tests read both with the same parsers. Records are copied verbatim, never
edited. `import.sh` regenerates the subset from the corpora and rewrites
`SHA256SUMS`; run it from any directory:

```sh
sh test/kat/import.sh
```

CI reruns it and fails if the result differs from the committed files.

## ML-KEM

| File | Taken from | Records |
| --- | --- | --- |
| `mlkem512-seed-decap.txt` | `../vectors/mlkem512-seed-decap.txt` | the first case |
| `mlkem512-encap.txt` | `../vectors/mlkem512-encap.txt` | the ninth case, the first valid one |
| `mlkem512-decap.txt` | `../vectors/mlkem512-decap.txt` | the first case |
| `mlkem768-keygen.txt` | `../vectors/mlkem768-keygen.txt` | the first case |
| `mlkem768-encap.txt` | `../vectors/mlkem768-encap.txt` | "Official test vector 0" |
| `mlkem768-decap.txt` | `../vectors/mlkem768-decap.txt` | "Official test vector 0" and the first "Bit flipped ciphertext" case |
| `mlkem1024-keygen.txt` | `../vectors/mlkem1024-keygen.txt` | the first case |
| `mlkem1024-encap.txt` | `../vectors/mlkem1024-encap.txt` | "Official test vector 0" |
| `mlkem1024-decap.txt` | `../vectors/mlkem1024-decap.txt` | "Official test vector 0" and the first "Bit flipped ciphertext" case |

The bit-flipped cases are the known answers for implicit rejection.

The ML-KEM-768 and ML-KEM-1024 records come from
[google/boringssl](https://github.com/google/boringssl) at revisions
`b9290021660b35aab4214d8e7cefbe84fce9dfc4` (768) and
`ebd832c3924065de594ffda62b376aeb2e4f61a9` (1024), files
`crypto/mlkem/mlkem{768,1024}_{nist_keygen,encap,decap}_tests.txt`. They are
under the Apache License 2.0 in `mlkem/LICENSE`.

The ML-KEM-512 records come from
[C2SP/wycheproof](https://github.com/C2SP/wycheproof) at revision
`3fa63dd0344abb611f1fb1d77e119938603ea230`, files
`testvectors_v1/mlkem_512_test.json`, `mlkem_512_encaps_test.json`, and
`mlkem_512_semi_expanded_decaps_test.json`, in the line-oriented conversion
described in `../vectors/README.md`. They are under the Apache License 2.0 in
`mlkem/LICENSE.wycheproof`.

## ML-DSA

| File | Records |
| --- | --- |
| `mldsa_nist_keygen_44_tests.txt` | header comment and the first case |
| `mldsa_nist_keygen_65_tests.txt` | header comment and the first case |
| `mldsa_nist_keygen_87_tests.txt` | header comment and the first case |
| `mldsa_nist_siggen_44_tests.txt` | header comment and the third case, whose message is 1 byte |
| `mldsa_nist_siggen_65_tests.txt` | header comment and the third case, whose message is 17 bytes |
| `mldsa_nist_siggen_87_tests.txt` | the sixth case, whose message is 1,207 bytes (the shortest) |
| `mldsa_eta_restart_keygen_65_tests.txt` | header comment and the first case |

The NIST records are taken from the files of the same name in
`../mldsa_vectors`, which come from
[google/boringssl](https://github.com/google/boringssl) revision
`ebd832c3924065de594ffda62b376aeb2e4f61a9`, `crypto/mldsa`. They are under the
Apache License 2.0 in `mldsa/LICENSE`.

`mldsa_eta_restart_keygen_65_tests.txt` is this repository's own data. Its
answer exercises the longer ExpandS prefix of FIPS 204 Algorithm 31, which no
NIST vector reaches; its header gives the OpenSSL commands that produced it.

## SLH-DSA

| File | Records |
| --- | --- |
| `keygen.txt` | all of `../slhdsa_vectors/keygen.txt`: one case per parameter set |
| `siggen.txt` | lines 1, 3, and 4 of `../slhdsa_vectors/siggen.txt`: SLH-DSA-SHA2-128f, SLH-DSA-SHA2-256f, and SLH-DSA-SHAKE-128f |
| `sigver.txt` | lines 98 and 133 of `../slhdsa_vectors/sigver.txt`: ACVP cases 19/266 (SLH-DSA-SHA2-128s) and 25/343 (SLH-DSA-SHAKE-128s), both valid |

The signing cases cover both hash constructions, and SHA2-256f is the one
that uses SHA-512 for H_msg and PRF_msg. They all use the fast `f` parameter
sets. The two verification cases cover the shape of the small `s` sets
without paying for `s` signing.

The records come from the
[NIST ACVP-Server](https://github.com/usnistgov/ACVP-Server) FIPS 205
corpus at revision `975de31eb83d87039ec88934fdc47d8c312b892d`, in the
tab-separated conversion described in `../slhdsa_vectors/README.md`. The
NIST notice is in `slhdsa/LICENSE`. As that notice asks, the change made here
is recorded: on 2026-10-10 the rows above were copied without alteration from
the converted files. The change selects a subset of the corpus and alters no
field.
