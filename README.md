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
NIST ACVP vectors for every standardized parameter set. ML-KEM is additionally
checked against pinned BoringSSL and Wycheproof corpora. This is a new
implementation that has not received an independent cryptographic audit;
release `0.1.x` must not be presented as audited software.

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
  hint, and signature decoding rejects non-canonical encodings.
- SLH-DSA implements the final FIPS 205 address-clearing and big-endian
  `base_2b` rules, WOTS+, FORS, XMSS, and hypertree traversal for both SHA2 and
  SHAKE families.
- SHA-2, SHA-3, SHAKE, HMAC, and MGF1 primitives are implemented internally in
  OCaml, leaving no hidden C dependency.
- Returned secret serializations are immutable strings; callers remain
  responsible for minimizing their lifetime.

"Constant time" describes the source structure. The OCaml compiler, garbage
collector, and runtime do not provide a formally verified constant-time
execution model. Timing regression checks are guards, not proofs.

## Development

```sh
opam install . --deps-only --with-test --with-doc
opam exec -- dune build @install @runtest @doc
opam exec -- dune exec --profile fuzz fuzz/fuzz_decode.exe
opam exec -- dune exec bench/benchmark.exe
opam exec -- dune exec bench/timing.exe
```

For a local installation, use `opam install .`. Once 0.1.0 is accepted into
the public opam repository, install individual packages with `opam install
mlkem`, `opam install mldsa`, or `opam install slhdsa`.

The native test suite covers every standardized parameter set and all checked
in vector corpora. Bytecode covers the portable primitive and non-prohibitive
tests; the computationally expensive SLH-DSA KAT suite runs natively.
`js_of_ocaml` CI runs every ML-KEM and ML-DSA set plus representative SHA2 and
SHAKE SLH-DSA end-to-end operations. Crowbar stresses every public decoder.

See [SECURITY.md](SECURITY.md) before reporting a security issue. Design and
package decisions are in [DESIGN.md](DESIGN.md), and the maintainer procedure
is in [RELEASE.md](RELEASE.md).
