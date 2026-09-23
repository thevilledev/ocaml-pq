# ML-DSA test vectors

These files are copied from BoringSSL's `crypto/mldsa` test data. They contain
NIST ACVP known-answer tests for deterministic key generation and signing for
all three FIPS 204 parameter sets.

- `mldsa_nist_keygen_44_tests.txt`
- `mldsa_nist_keygen_65_tests.txt`
- `mldsa_nist_keygen_87_tests.txt`
- `mldsa_nist_siggen_44_tests.txt`
- `mldsa_nist_siggen_65_tests.txt`
- `mldsa_nist_siggen_87_tests.txt`

Corpus source: BoringSSL revision
`ebd832c3924065de594ffda62b376aeb2e4f61a9`. The upstream files identify the
corresponding NIST ACVP `ML-DSA-keyGen-FIPS204` and
`ML-DSA-sigGen-FIPS204` sources.

SHA-256 checksums:

```text
bca3e7b150e2216762ce4263f98c1267aff62673049ebbdef286e044e47c10d7  mldsa_nist_keygen_44_tests.txt
e946f7e10b07cd04342dd5a534d9129fbaf2726b1dfdcce22e01412733620143  mldsa_nist_keygen_65_tests.txt
2ee49b14270cfef5f46e18a15caff0217951cac6e8c4a7f57d94fb52c05edba1  mldsa_nist_keygen_87_tests.txt
4d1a7005968b6c23b5ac14c23b09f93c2cf3bda8b88f4d35f695254554070f1e  mldsa_nist_siggen_44_tests.txt
edcd66904eb718bf859b21a10a7df64ce5d03f342b43679cdc35276fadb7bc76  mldsa_nist_siggen_65_tests.txt
02ba6ddf6d9ce5123a52502e015817afc75ad02f5aec2810fde30b923c1d69de  mldsa_nist_siggen_87_tests.txt
```

`mldsa_eta_restart_keygen_65_tests.txt` is not from BoringSSL. It holds three
ML-DSA-65 key-generation answers whose seeds make ExpandS read past the first
272 bytes of SHAKE256 output for one polynomial, so the implementation must
draw a longer prefix (FIPS 204 Algorithm 31). About one ML-DSA-65 key in
13,000 takes that path and none of the NIST vectors do. The answers were
generated independently with OpenSSL 3.6.4; the file header gives the
commands.

```text
340eeb860517d3ccec242b5a4cb778f4979d13984748e0180a9509ee0dfc9763  mldsa_eta_restart_keygen_65_tests.txt
```

The BoringSSL vectors and the copied `LICENSE` are from
[google/boringssl](https://github.com/google/boringssl) and are distributed
under the Apache License 2.0.

The vectors are data consumed by tests; the implementation has no dependency
on BoringSSL. The complementary ML-DSA Wycheproof signing and verification
corpus, including malformed-input cases, is documented in `../wycheproof`.
