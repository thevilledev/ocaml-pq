# Changes

## 0.1.0 (2026-09-20)

First release of the `mlkem`, `mldsa`, and `slhdsa` opam packages.

- Implement every FIPS 203 parameter set: ML-KEM-512, ML-KEM-768, and
  ML-KEM-1024.
- Implement every FIPS 204 parameter set: ML-DSA-44, ML-DSA-65, and ML-DSA-87,
  including typed keys/signatures, strict decoding, contexts, and explicit
  hedged and deterministic PureML-DSA signing.
- Implement all twelve FIPS 205 parameter sets: SHA2 and SHAKE 128s/f, 192s/f,
  and 256s/f, including WOTS+, FORS, XMSS, hypertree signing, contexts, and
  explicit hedged and deterministic PureSLH-DSA signing.
- Implement SHA-256, SHA-512, SHA3-256, SHA3-512, SHAKE128, SHAKE256, HMAC, and
  MGF1 entirely in OCaml, with no C stubs or runtime package dependencies.
- Use shared parameterized engines, fixed-bound NTT arithmetic for ML-KEM and
  ML-DSA, ML-KEM implicit rejection, and the final FIPS 205 address-clearing
  and big-endian FORS rules.
- Provide abstract per-algorithm key, ciphertext, shared-secret, and signature
  types; exact-length and canonical decoders; caller-provided randomness; and
  seed-based key generation and serialization.
- Isolate expanded ACVP and raw-message hooks in the explicitly testing-only
  `mlkem.for_testing`, `mldsa.for_testing`, and `slhdsa.for_testing` libraries.
- Verify byte-for-byte NIST ACVP key generation and deterministic signatures
  for every parameter set; add all 2,863 applicable ML-KEM and ML-DSA cases
  from a pinned Wycheproof revision, pinned BoringSSL ML-KEM corpora,
  corruption and malformed-input tests, decoder fuzzing, and hash known answers.
- Check all 168 applicable NIST SLH-DSA signature-verification cases (24 valid
  and 144 invalid) and 36 signing known answers, covering hedged signing,
  8192-byte messages, and 255-byte contexts for every parameter set.
- Redistribute the BoringSSL, Wycheproof, and NIST ACVP-Server test corpora
  with their upstream license notices; see `LICENSE.md`.
- Add native, bytecode, and `js_of_ocaml` portability coverage. JavaScript CI
  exercises all ML-KEM and ML-DSA sets and representative SHA2/SHAKE SLH-DSA
  end-to-end operations.
- Evaluate every ML-DSA signing rejection check before deciding to retry,
  document its remaining variable-time boundary, and inspect aggressively
  optimized ML-KEM/ML-DSA native control flow in CI.
- Split decoder fuzzing by family, isolate expensive exact-length SLH-DSA key
  imports, and run deterministic bounded fuzz cases in CI.
- Add release-ready opam metadata for three independent packages, Avrea-hosted
  CI across OCaml 4.13 through 5.4, a non-blocking lower-dependency-bounds job,
  and GitHub Actions pinned to the latest release SHAs.
- Document the unaudited security boundary and intentionally exclude all
  downstream protocol integrations from 0.1.0.
