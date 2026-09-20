# ML-KEM test vectors

The ML-KEM-768 and ML-KEM-1024 `.txt` files are copied from BoringSSL's
`crypto/mlkem` test data, with trailing whitespace removed. They contain NIST
ACVP known-answer tests plus invalid-input and implicit-rejection cases used
for differential testing. Their upstream file names and revisions are recorded
here whenever the corpus is refreshed.

- `mlkem768-keygen.txt`: `mlkem768_nist_keygen_tests.txt`
- `mlkem768-encap.txt`: `mlkem768_encap_tests.txt`
- `mlkem768-decap.txt`: `mlkem768_decap_tests.txt`

Initial corpus source: BoringSSL revision
`b9290021660b35aab4214d8e7cefbe84fce9dfc4`.

- `mlkem1024-keygen.txt`: `mlkem1024_nist_keygen_tests.txt`
- `mlkem1024-encap.txt`: `mlkem1024_encap_tests.txt`
- `mlkem1024-decap.txt`: `mlkem1024_decap_tests.txt`

ML-KEM-1024 corpus source: BoringSSL revision
`ebd832c3924065de594ffda62b376aeb2e4f61a9`.

The ML-KEM-512 files are an earlier line-oriented conversion of the
corresponding Wycheproof JSON groups. Field values are unchanged; JSON-only
comments, test identifiers, and flags are omitted. The complete, provenance-
checked ML-KEM and ML-DSA Wycheproof corpus used by the current test suite is
in `../wycheproof`.

- `mlkem512-seed-decap.txt`: `testvectors_v1/mlkem_512_test.json`
- `mlkem512-encap.txt`: `testvectors_v1/mlkem_512_encaps_test.json`
- `mlkem512-decap.txt`:
  `testvectors_v1/mlkem_512_semi_expanded_decaps_test.json`

ML-KEM-512 corpus source: Wycheproof revision
`3fa63dd0344abb611f1fb1d77e119938603ea230`.

The BoringSSL-derived files and the copied `LICENSE` are from
[google/boringssl](https://github.com/google/boringssl) and are distributed
under the Apache License 2.0. The `LICENSE` copy is identical at both pinned
BoringSSL revisions. The ML-KEM-512 files derive from Wycheproof, whose
license is in `../wycheproof/LICENSE`.

The vectors are data consumed by tests; the implementation has no dependency
on BoringSSL.
