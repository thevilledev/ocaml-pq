# API usage

[Back to the README](../README.md)

## Packages and parameter sets

Each package exposes one public module. Choose the parameter-set module
within it to generate keys and perform operations:

| Package | Public module | Parameter-set modules |
| --- | --- | --- |
| `mlkem` | `Mlkem` | `Mlkem512`, `Mlkem768`, `Mlkem1024` |
| `mldsa` | `Mldsa` | `Mldsa44`, `Mldsa65`, `Mldsa87` |
| `slhdsa` | `Slhdsa` | `Sha2_128s` through `Sha2_256f`, and `Shake_128s` through `Shake_256f` |

SLH-DSA supports both SHA2 and SHAKE at security levels 128, 192, and 256.
Each has a small-signature (`s`) and fast-signing (`f`) variant, for twelve
parameter sets in total. The [SLH-DSA interface](../slhdsa/slhdsa.mli) lists
every module.

The packages are independently installable and share a release version.
For installation from this checkout, see the [README](../README.md#install).
Once 0.1.1 is accepted into the public opam repository, individual packages
can be installed with `opam install mlkem`, `opam install mldsa`, or
`opam install slhdsa`.

These are cryptographic primitives. TLS, X.509, HPKE, and other protocol
integrations are outside this repository.

## Supply secure randomness

Key generation, encapsulation, and randomized signing take a caller-provided
function of type `int -> string`. It must return exactly the requested number
of cryptographically secure random bytes. The examples call it
`secure_random`; supply an implementation appropriate to your platform.

The libraries do not choose a random provider. This keeps the APIs portable
across native programs, MirageOS unikernels, and `js_of_ocaml` applications.

## Establish a shared secret with ML-KEM

The [README example](../README.md#example-establish-a-shared-secret) uses
ML-KEM-768. The other parameter sets have the same API, with distinct key and
ciphertext types. See the [ML-KEM-768 interface](../lib/mlkem768.mli) for
function signatures, encoded sizes, and parsing errors.

Decapsulation always returns a shared secret. Invalid ciphertexts of the
correct length produce a replacement secret through FIPS 203 implicit
rejection; they do not produce an error that reveals whether validation
succeeded.

## SHAKE for protocols that adopt ML-KEM

A protocol that adopts ML-KEM often needs SHAKE as well. HPKE, for example,
derives an ML-KEM key pair from keying material with SHAKE256. `Mlkem.Fips202`
exposes the two extendable-output functions that ML-KEM itself runs on, so
that such a protocol does not need a second Keccak implementation:

```ocaml
let seed = Mlkem.Fips202.shake256 ~output_length:64 keying_material
```

`shake128` has the same shape. Both take the whole input at once, and the
outputs for one input are prefixes of each other. They are the only hash
functions this repository exports: `digestif` already provides SHA3-256 and
SHA3-512.

## Sign and verify messages

ML-DSA and SLH-DSA use the same API shape. The default `sign` operation uses
fresh randomness for each signature (hedged signing). For example, with
ML-DSA-65:

```ocaml
let signing_key, verification_key =
  Mldsa.Mldsa65.generate ~random:secure_random ()
in
let signature =
  Mldsa.Mldsa65.sign ~context:"example" ~random:secure_random signing_key
    ~message:"content"
  |> Result.get_ok
in
assert (
  Mldsa.Mldsa65.verify ~context:"example" verification_key
    ~message:"content" signature)
```

Use `sign_deterministic` to sign without fresh randomness. Key generation
still needs secure randomness, as in this SLH-DSA example:

```ocaml
let signing_key, verification_key =
  Slhdsa.Shake_128f.generate ~random:secure_random ()
in
let signature =
  Slhdsa.Shake_128f.sign_deterministic signing_key ~message:"content"
  |> Result.get_ok
in
assert (Slhdsa.Shake_128f.verify verification_key ~message:"content" signature)
```

An optional context string identifies the application's use of a signature.
It is limited to 255 bytes and must match when signing and verifying. The
examples use `Result.get_ok` for brevity; application code should handle
signing errors. Full interfaces and error types are documented in
[ML-DSA](../mldsa/mldsa_engine.mli) and
[SLH-DSA](../slhdsa/slhdsa_engine.mli).

## Key types and serialization

Keys, ciphertexts, shared secrets, and signatures have distinct abstract
types. Keys from different parameter sets cannot be mixed. Parsers check
exact lengths and algorithm-specific canonical encodings.

ML-KEM private keys serialize as a 64-byte seed: the concatenation of the
32-byte values `d` and `z`. ML-DSA and SLH-DSA support expanded private-key
encodings and can recover the original seed when the key was constructed
from one. Seed recovery returns `None` for keys imported only in expanded
form.

Secret serializations are immutable strings. Callers are responsible for
minimizing how long they keep those strings in memory.

The `.for_testing` libraries contain expanded-vector and raw-message hooks
for test suites. Use the main package libraries in application code.

Read the [security policy](../SECURITY.md) for audit status and side-channel
limitations.
