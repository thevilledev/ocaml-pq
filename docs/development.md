# Development

[Back to the README](../README.md)

Run all commands from the repository root with OCaml 4.13 or newer.

## Build and test

Install development dependencies, build all packages, run the tests, and
generate API documentation:

```sh
opam install . --deps-only --with-test --with-doc
opam exec -- dune build @install @runtest @doc
```

The generated API documentation starts at
`_build/default/_doc/_html/index.html`.

## Test coverage

The native suite covers every standardized parameter set and all checked-in
vector corpora. Key generation and deterministic signing are checked
byte-for-byte against NIST ACVP vectors. ML-KEM and ML-DSA also use all 2,863
applicable Wycheproof cases at a pinned revision; ML-KEM adds pinned BoringSSL
corpora. Wycheproof has no SLH-DSA vectors at that revision.

SLH-DSA checks 36 signing known answers, including randomized signing, and
all 168 applicable NIST signature-verification cases (24 valid and 144
invalid). Every parameter set also exercises invalid lengths, context
limits, randomness callback contracts, and inconsistent private keys.
Generated-message tests for SHA2-128f and SHAKE-128f cover empty messages,
255-byte contexts, key serialization, and signature corruption.

Vector provenance and reproduction details are in the test directories:

- [ML-KEM vectors](../test/vectors/README.md)
- [ML-DSA vectors](../test/mldsa_vectors/README.md)
- [SLH-DSA vectors](../test/slhdsa_vectors/README.md)
- [Wycheproof corpus](../test/wycheproof/README.md)

Bytecode runs the portable primitive tests and other tests that are practical
to run there. The expensive SLH-DSA known-answer suite runs natively.
`js_of_ocaml` CI exercises every ML-KEM and ML-DSA parameter set, plus
representative SHA2 and SHAKE SLH-DSA end-to-end operations.

## Fuzz decoders

Crowbar exercises public decoders with separate targets for each algorithm,
so slow cases in one family cannot starve the others. The fuzz targets build
only under the `fuzz` profile and are not part of any package, so `crowbar` is
not a package test dependency. Install it separately:

```sh
opam install crowbar
```

These commands use the same bounded runs and seed as CI:

```sh
opam exec -- dune exec --profile fuzz fuzz/fuzz_mlkem.exe -- -r 5000 -s 1515870810
opam exec -- dune exec --profile fuzz fuzz/fuzz_mldsa.exe -- -r 5000 -s 1515870810
opam exec -- dune exec --profile fuzz fuzz/fuzz_slhdsa.exe -- -r 5000 -s 1515870810
```

SLH-DSA private-key imports of the correct length reconstruct a Merkle root
and are much slower. Run that target separately with a small repeat count:

```sh
opam exec -- dune exec --profile fuzz fuzz/fuzz_slhdsa_keys.exe -- -r 1 -s 1515870810
```

CI runs one case per decoder in this target. Native key round-trip and vector
tests provide deeper correctness coverage.

## Inspect native code and measure performance

The [native-code inspection guide](../compiler/README.md) describes how to
build optimized archives and inspect ML-KEM secret arithmetic and ML-DSA
rejection checks.

Run the performance and timing checks with:

```sh
opam exec -- dune exec bench/benchmark.exe
opam exec -- dune exec bench/timing.exe
```

Timing and compiler checks catch regressions; they do not prove constant-time
execution. See the [design notes](design.md#security-limitations) and
[security policy](../SECURITY.md) for the limits of these checks.

For package validation and publishing, see [Releasing](releasing.md).
