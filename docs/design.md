# Design notes

[Back to the README](../README.md)

## Repository and package boundary

`ocaml-pq` is one review and development boundary for pure-OCaml
post-quantum primitives. Version 0.1.0 publishes three separate opam packages:

- `mlkem` for FIPS 203;
- `mldsa` for FIPS 204;
- `slhdsa` for FIPS 205.

Separate packages prevent an application that needs only a KEM from pulling in
signature implementations, while one repository keeps portability, security
policy, testing, and release practice aligned. The packages share no runtime
dependency and contain no C stubs. The repository contains no TLS, X.509,
MirageOS, HPKE, or other downstream integration code.

## Parameter-set policy

Every parameter set standardized by FIPS 203, FIPS 204, and FIPS 205 is
implemented. ML-KEM-768 remains the recommended starting point for applications
without an external mandate because it is the common interoperability point in
Go, RustCrypto, the Mirage-adjacent work, and deployed hybrid TLS designs. That
default does not remove access to ML-KEM-512 or ML-KEM-1024.

References:

- [NIST FIPS 203](https://csrc.nist.gov/pubs/fips/203/final)
- [NIST FIPS 204](https://csrc.nist.gov/pubs/fips/204/final)
- [NIST FIPS 205](https://csrc.nist.gov/pubs/fips/205/final)
- [NIST ACVP](https://pages.nist.gov/ACVP/)
- [Go `crypto/mlkem`](https://pkg.go.dev/crypto/mlkem)
- [RustCrypto `ml-kem`](https://github.com/RustCrypto/KEMs/tree/master/ml-kem)
- [Mirage-adjacent `crypto-pq`](https://tangled.org/gazagnaire.org/ocaml-crypto/)

The Mirage-adjacent implementation uses extracted libcrux C/C++ and is an
interoperability reference, not a dependency or substitute for pure-OCaml
portability.

## API alignment

Production APIs use abstract algorithm-specific types, strict decoding, and
caller-provided randomness. Modules for different parameter sets intentionally
have incompatible key and signature types.

ML-KEM follows the safe common denominator of Go and Rust:

- distinct encapsulation-key, decapsulation-key, ciphertext, and shared-secret
  types;
- canonical 64-byte `d || z` private-key seeds;
- public-key coefficient validation;
- implicit rejection rather than an error oracle for invalid same-length
  ciphertexts.

`mlkem` also exports SHAKE128 and SHAKE256, as `Mlkem.Fips202`. A protocol
that adopts ML-KEM tends to need them: the HPKE specification of ML-KEM derives
key pairs with SHAKE256. `digestif`, the usual source of hash functions, has
SHA-3 but not the FIPS 202 extendable-output functions, so exporting the ones
ML-KEM already runs on keeps such a protocol from carrying a Keccak of its own.
`Mlkem.Rfc9861` exports TurboSHAKE for the same reason: the HPKE KDFs of
`draft-ietf-hpke-pq` use it, and no other OCaml package provides it. It is the
same sponge over the last 12 rounds of the same permutation, so it adds a
parameter to the Keccak code rather than a second copy of it.
The export is deliberately narrow. SHA3-256 and SHA3-512 stay internal, because
`digestif` provides them, and `mldsa` and `slhdsa` export no hash functions, so
the three packages still share no code and no dependency.

ML-DSA and SLH-DSA expose typed signing and verification keys and signatures,
255-byte-bounded contexts, hedged signing with caller-provided entropy, and an
explicit deterministic operation. Their expanded private-key parsers validate
internal consistency. Seed recovery returns `None` for keys imported only in
expanded form. Raw internal-message and deterministic ACVP hooks are isolated
in `mldsa.for_testing` and `slhdsa.for_testing`.

## Implementation structure

ML-KEM has a single parameterized engine for 512, 768, and 1024. It contains
Keccak, finite-field and fixed-bound NTT arithmetic, canonical encodings,
centered-binomial sampling, K-PKE, and the FIPS 203 transform with re-encryption
and implicit rejection.

ML-DSA has a single parameterized engine for 44, 65, and 87. It contains
Keccak, matrix expansion, fixed-bound NTT arithmetic, decomposition and hints,
strict key/signature encodings, rejection sampling, and both hedged and
deterministic PureML-DSA external interfaces. The implementation incorporates
the published FIPS 204 potential-correction guidance, including the 821-attempt
signing bound.

SLH-DSA has a single parameterized engine for all twelve sets. It contains
pure OCaml SHA-256, SHA-512, SHAKE256, HMAC, and MGF1; the expanded and
compressed FIPS address forms; WOTS+; FORS; XMSS; and hypertree signing. The
engine follows final FIPS 205 `setTypeAndClear` semantics and the standard's
big-endian `base_2b` extraction rather than the older pre-standard SPHINCS+
FORS bit convention.

## Security limitations

ML-KEM's NTT, inverse NTT, polynomial arithmetic, compression, and secret
selection use fixed loop bounds and avoid secret-dependent source-level
branches. ML-DSA evaluates every norm bound and rejection check before
deciding whether to retry a signing attempt, but the number of attempts
remains variable.

These source-level properties do not guarantee constant-time execution. The
OCaml compiler, garbage collector, and runtime do not provide a formally
verified constant-time execution model. ML-DSA signing must not be treated as
side-channel-hardened against precise timing, cache, power, or co-resident
observation. Timing and native-code regression checks are guards, not proofs.
See the [security policy](../SECURITY.md) for the audit status and reporting
guidance.

## Verification boundary

NIST ACVP key-generation and deterministic-signature outputs are checked
byte-for-byte for all 18 KEM/signature parameter sets. ML-KEM and ML-DSA also
use the complete applicable Wycheproof corpus at a pinned revision; ML-KEM uses
pinned BoringSSL invalid-input and implicit-rejection corpora as well.
Wycheproof has no SLH-DSA vectors at the selected revision. Primitive hash
known answers, malformed encodings, seed and expanded-key round trips,
randomness contracts, context handling, and signature corruption are covered.

CI builds on Avrea runners with OCaml 4.13, 4.14, 5.1, and 5.4. It has a
non-blocking lowest-dependency-bounds job, opam lint/install checks for all
three packages, bytecode coverage, native KATs, bounded per-family decoder
fuzzing, compiler inspection of ML-KEM secret arithmetic and ML-DSA rejection
checks, and
native-to-JavaScript end-to-end coverage. The expensive exact-length SLH-DSA
private-key fuzzer runs as a separate one-case smoke test so it cannot starve
public decoder coverage. GitHub Actions are pinned to exact release commits.

These checks establish interoperability and catch regressions. They are not a
formal proof, an independent audit, or a FIPS 140 validation.

The [formal verification](../formal/README.md) adds machine-checked proofs.
Lean proves that every implementation matches FIPS 203, FIPS 204, FIPS 205
and the hash standards underneath them on every input. It also proves that
integer arithmetic never overflows on 64-bit native, `js_of_ocaml` or 31-bit
platforms. TLA+ models, checked with TLC, explore the loops and state machines
exhaustively. These proofs cover the source code's behaviour, not side
channels, the compiler or the runtime, and they do not replace an independent
audit.
