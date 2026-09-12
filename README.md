# ocaml-pq

`ocaml-pq` implements the three NIST post-quantum cryptography standards in
pure OCaml. Each algorithm is available as a separate opam package:

| Package | Purpose | Standard |
| --- | --- | --- |
| `mlkem` | Establish a shared secret | FIPS 203 (ML-KEM) |
| `mldsa` | Sign and verify messages | FIPS 204 (ML-DSA) |
| `slhdsa` | Sign and verify messages using hash-based signatures | FIPS 205 (SLH-DSA) |

All standardized parameter sets are supported. The packages require OCaml
4.13 or newer, have no C stubs or runtime package dependencies, and work in
native programs, MirageOS unikernels, and `js_of_ocaml` applications.

**Security status:** The `0.1.x` series has not received an independent
cryptographic audit. Constant-time execution is not guaranteed, and ML-DSA
signing has timing limitations. Read the [security policy](SECURITY.md)
before use.

## Install

From a checkout of this repository:

```sh
opam install .
```

Add the package you use to your Dune stanza, for example `(libraries mlkem)`.

## Example: establish a shared secret

The receiver generates a key pair and shares the public encapsulation key.
The sender uses it to produce a ciphertext and shared secret; the receiver
recovers the same secret from the ciphertext with the private key.

Supply `secure_random : int -> string`, a function that returns exactly the
requested number of cryptographically secure random bytes.

```ocaml
let private_key, public_key = Mlkem.Mlkem768.generate ~random:secure_random () in
let ciphertext, sender_secret =
  Mlkem.Mlkem768.encapsulate ~random:secure_random public_key
in
let receiver_secret = Mlkem.Mlkem768.decapsulate private_key ciphertext in
assert (
  Mlkem.Mlkem768.shared_secret_to_octets sender_secret =
  Mlkem.Mlkem768.shared_secret_to_octets receiver_secret)
```

## Documentation

- [API usage](docs/usage.md): parameter sets, signing examples, randomness, and key formats.
- [Design notes](docs/design.md): package boundaries, implementation, and security limitations.
- [Development](docs/development.md): building, testing, fuzzing, and benchmarks.
- [Releasing](docs/releasing.md): maintainer instructions.
- [Changelog](CHANGES.md): release history.

Licensed under the [ISC license](LICENSE.md).
