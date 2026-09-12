# ocaml-pq

`ocaml-pq` provides pure-OCaml implementations of the three NIST
post-quantum cryptography standards. One source repository and release
contains three independently installable opam packages:

| Package | Public module | Standard | Parameter sets |
| --- | --- | --- | --- |
| `mlkem` | `Mlkem` | FIPS 203 | ML-KEM-512, ML-KEM-768, ML-KEM-1024 |
| `mldsa` | `Mldsa` | FIPS 204 | ML-DSA-44, ML-DSA-65, ML-DSA-87 |
| `slhdsa` | `Slhdsa` | FIPS 205 | SHA2 and SHAKE at 128/192/256, each in small/fast variants (12) |

None of the packages uses C stubs or has runtime package dependencies. All
target OCaml 4.13 or newer. Randomness is supplied by the caller, so the same
APIs work in native programs, MirageOS unikernels, and `js_of_ocaml`
applications.

## Release scope and status

Version 0.1.0 is the first release of this repository. The three opam packages
share that version and release archive, while remaining independently
installable. This release contains the cryptographic primitives, typed APIs,
test vectors, portability checks, and package metadata.

Key generation and deterministic signing are checked byte-for-byte against
NIST ACVP vectors for every standardized parameter set. ML-KEM and ML-DSA are
additionally checked against the complete applicable Wycheproof corpus at a
pinned revision; ML-KEM also uses pinned BoringSSL corpora. Wycheproof does not
provide SLH-DSA vectors at that revision. This is a new implementation that has
not received an independent cryptographic audit; release `0.1.x` must not be
presented as audited software.

TLS, X.509, HPKE, and other downstream integrations are intentionally outside
this repository and outside the 0.1.0 release.

## APIs

ML-KEM-768 is the default starting point for applications without a
parameter-set mandate:

```ocaml
let dk, ek = Mlkem.Mlkem768.generate ~random:secure_random () in
let ciphertext, sender_secret =
  Mlkem.Mlkem768.encapsulate ~random:secure_random ek
in
let receiver_secret = Mlkem.Mlkem768.decapsulate dk ciphertext in
assert (
  Mlkem.Mlkem768.shared_secret_to_octets sender_secret =
  Mlkem.Mlkem768.shared_secret_to_octets receiver_secret)
```

ML-DSA and SLH-DSA use the same typed signing shape. Hedged signing is the
default; deterministic signing is explicit:

```ocaml
let sk, vk = Mldsa.Mldsa65.generate ~random:secure_random () in
let signature =
  Mldsa.Mldsa65.sign ~context:"example" ~random:secure_random sk
    ~message:"content"
  |> Result.get_ok
in
assert (Mldsa.Mldsa65.verify ~context:"example" vk ~message:"content" signature)

let sk, vk = Slhdsa.Shake_128f.generate ~random:secure_random () in
let signature =
  Slhdsa.Shake_128f.sign_deterministic sk ~message:"content"
  |> Result.get_ok
in
assert (Slhdsa.Shake_128f.verify vk ~message:"content" signature)
```

`secure_random : int -> string` must return exactly the requested number of
cryptographically secure random bytes. The libraries deliberately do not
select a platform-specific random provider.

Production APIs use abstract and distinct key, ciphertext, shared-secret, and
signature types. Parsers enforce exact lengths and algorithm-specific
canonical encodings. ML-KEM private keys serialize as the canonical 64-byte
`d || z` seed. ML-DSA and SLH-DSA expose both expanded private-key encodings
and optional recovery of the original seed when a key was constructed from
one. Expanded-vector and raw-message hooks live only in the explicitly named
`.for_testing` libraries.

## Security design

- ML-KEM's NTT, inverse NTT, polynomial arithmetic, compression, and secret
  selection use fixed loop bounds and avoid secret-dependent source-level
  branches. Decapsulation always re-encrypts and applies implicit rejection.
- ML-DSA uses a fixed-bound NTT and the 821-attempt FIPS 204 signing bound. Key,
  hint, and signature decoding rejects non-canonical encodings. Each signing
  attempt scans every norm bound and computes all rejection checks before one
  decision, but the number of attempts remains variable.
- SLH-DSA implements the final FIPS 205 address-clearing and big-endian
  `base_2b` rules, WOTS+, FORS, XMSS, and hypertree traversal for both SHA2 and
  SHAKE families.
- SHA-2, SHA-3, SHAKE, HMAC, and MGF1 primitives are implemented internally in
  OCaml, leaving no hidden C dependency.
- Returned secret serializations are immutable strings; callers remain
  responsible for minimizing their lifetime.

"Constant time" describes the source structure. The OCaml compiler, garbage
collector, and runtime do not provide a formally verified constant-time
execution model. In particular, ML-DSA signing uses the variable-attempt
rejection process required by FIPS 204 and must not be treated as
side-channel-hardened against precise timing, cache, power, or co-resident
observation. Timing and native-code regression checks are guards, not proofs.

## Development

```sh
opam install . --deps-only --with-test --with-doc
opam exec -- dune build @install @runtest @doc
opam exec -- dune exec --profile fuzz fuzz/fuzz_mlkem.exe
opam exec -- dune exec --profile fuzz fuzz/fuzz_mldsa.exe
opam exec -- dune exec --profile fuzz fuzz/fuzz_slhdsa.exe
opam exec -- dune build --profile compiler-audit lib/mlkem.a
opam exec -- dune build --profile compiler-audit mldsa/mldsa.a
sh compiler/inspect_mlkem_native.sh
sh compiler/inspect_mldsa_native.sh
opam exec -- dune exec bench/benchmark.exe
opam exec -- dune exec bench/timing.exe
```

The three default fuzzers keep cheap decoder coverage independent so one
family cannot starve the others. Exact-length SLH-DSA private-key imports
reconstruct a Merkle root and therefore live in the deliberately slow
`fuzz/fuzz_slhdsa_keys.exe` target; run it separately with a small repeat count.

For a local installation, use `opam install .`. Once 0.1.0 is accepted into
the public opam repository, install individual packages with `opam install
mlkem`, `opam install mldsa`, or `opam install slhdsa`.

The native test suite covers every standardized parameter set and all checked
in vector corpora, including 2,863 applicable Wycheproof cases for ML-KEM and
ML-DSA. Bytecode covers the portable primitive and non-prohibitive tests; the
computationally expensive SLH-DSA KAT suite runs natively.
`js_of_ocaml` CI runs every ML-KEM and ML-DSA set plus representative SHA2 and
SHAKE SLH-DSA end-to-end operations. Crowbar stresses every public decoder.
The bounded fuzz targets are compiled and run in CI; the expensive exact-length
SLH-DSA private-key target gets one case per decoder in CI, with deeper
correctness coverage supplied by the native key round-trip/vector tests.

See [SECURITY.md](SECURITY.md) before reporting a security issue. Design and
package decisions are in [DESIGN.md](DESIGN.md), and the maintainer procedure
is in [RELEASE.md](RELEASE.md).
