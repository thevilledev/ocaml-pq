# Native-code inspection

`inspect_mlkem_native.sh` checks the optimized native archive rather than the
OCaml source. It extracts `ct_equal` and `select_secret`, verifies the reviewed
control-flow shape on arm64 or x86_64, and confirms that implicit-rejection
selection contains arithmetic mask operations. It also rejects conditional
branches in nine scalar field-arithmetic and decompression helpers used on
secret data.

`inspect_mldsa_native.sh` confirms that the optimized signing-attempt routine
retains all three complete vector norm checks before its retry back-edge. It
does not claim that ML-DSA signing is constant-time: the number of attempts and
other arithmetic remain within the documented variable-time boundary.

Run it after an aggressively optimized native build:

```sh
opam exec -- dune build --profile compiler-audit lib/mlkem.a
opam exec -- dune build --profile compiler-audit mldsa/mldsa.a
sh compiler/inspect_mlkem_native.sh
sh compiler/inspect_mldsa_native.sh
```

The `compiler-audit` profile adds `ocamlopt -O3`. The branch baseline is
intentionally strict. A failure after an OCaml compiler upgrade is a request
for human inspection of the changed disassembly, not proof that the new output
leaks. Conversely, passing establishes only the reviewed control-flow shape of
these two routines; it is not a general constant-time proof for the compiler,
runtime, garbage collector, or complete library. CI runs these checks with both
the oldest and newest supported OCaml compilers.
