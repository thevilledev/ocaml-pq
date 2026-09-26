# Formal verification

[Back to the README](../README.md)

This directory holds a machine-checked verification of every implementation
in the repository. The FIPS 203, FIPS 204 and FIPS 205 algorithms are covered
for all 18 parameter sets, together with the hash functions underneath them:
Keccak (SHA3-256, SHA3-512, SHAKE128, SHAKE256), SHA-256, SHA-512, HMAC and
MGF1.

Two tools divide the work:

- **Lean 4 with Mathlib** (`lean/`) proves functional correctness for every
  input. Each OCaml function is modelled in Lean, the corresponding FIPS
  pseudo-code is transcribed independently, and a theorem states that the
  model equals the specification on the inputs the code receives. Further
  theorems prove that array indices stay in bounds and that `int` arithmetic
  never overflows on any supported platform.
- **TLA+ with TLC** (`tla/`) model-checks the loops and state machines
  exhaustively at small sizes. Each model also contains an independent
  functional definition of the FIPS algorithm to compare against.

**Result: no bugs were found.** Every implementation matches its standard on
every input it can receive. The verification did turn up behaviour that is
stricter than the standards, hazards that no caller can reach, and one
untested code path, which now has a regression test; all are listed under
[Findings](#findings).

The proofs cover the source-level behaviour of the OCaml code. They say
nothing about timing, cache or other side channels, and they do not verify
the OCaml compiler or runtime. See [Trust base](#trust-base).

**Not yet covered: TurboSHAKE.** `Mlkem.Rfc9861` (RFC 9861) came after the
proofs. It runs the same sponge over `permute_from 12`, the last twelve rounds
of the permutation, which the models do not yet describe. The model of
`permute` is the loop of `permute_from` from round 0, and the model of
`sponge` the body of `sponge_with` with that permutation, so every result
below about Keccak, SHA-3 and SHAKE still holds as stated. TurboSHAKE is held
to the vectors of RFC 9861 by the test suite.

## What is proved

The table lists the principal results; `lean/OcamlPq/Audit.lean` names the
headline theorems. Unless noted otherwise, results hold for every parameter
set and every input.

| Component | OCaml | Lean area | Principal results |
| --- | --- | --- | --- |
| ML-KEM arithmetic | `lib/mlkem_engine.ml` 105–228 | `MLKEM` | Barrett and conditional reduction are correct on their exact domains, with margins against every caller. `compress` and `decompress` equal FIPS 203 eq. 4.7/4.8, and the compression error bound holds. The zeta tables are powers of 17 in bit-reversed order. `ntt`, `inverse_ntt` and `ntt_mul` equal FIPS 203 Algorithms 9–12. The NTT is the CRT ring isomorphism, and the code's `inverse_ntt (ntt_mul (ntt a) (ntt b))` computes a·b in Z_q[X]/(X²⁵⁶+1). |
| ML-KEM algorithms | `lib/mlkem_engine.ml` 292–525 | `MLKEMAlg` | SamplePolyCBD and SampleNTT match FIPS 203 Algorithms 7–8, including the rarely taken retry with a longer XOF prefix. K-PKE and the KEM match Algorithms 13–18, including nonce order, matrix transposition and implicit rejection. `ct_equal` and `select_secret` are correct. Key parsing is exactly the §7.2/§7.3 checks, and one more (see [Findings](#findings)). Decapsulation returns the encapsulated key whenever the noise stays below ⌈q/4⌋. |
| ML-DSA arithmetic | `mldsa/mldsa_engine.ml` 111–469 | `MLDSA` | Modular arithmetic is correct for every int input. The NTT and inverse NTT equal FIPS 204 Algorithms 41/42, and the inverse NTT of a pointwise product is the product in R_q. Power2Round, Decompose, UseHint and MakeHint equal Algorithms 35–40, and the UseHint lemma holds. The signer uses the reference implementation's shortcuts (`r0 = w0 − cs2`, and `make_hint` on `(r0 + ct0, w1)`); these give exactly the accept/reject decision and hints of FIPS 204 Algorithm 7. |
| ML-DSA algorithms | `mldsa/mldsa_engine.ml` 328–908 | `MLDSAAlg` | RejNTTPoly, RejBoundedPoly and SampleInBall match FIPS 204 Algorithms 29–31, including their retries. SampleInBall output has exactly τ coefficients equal to ±1. ExpandA, ExpandS, ExpandMask and key generation match their algorithms. Mask nonces never repeat and always fit in 16 bits. The loop returns FIPS Algorithm 7's first accepted attempt within 821 iterations; failure probability is below 2⁻²⁵⁸, and 814 is the smallest cap below 2⁻²⁵⁶. Sign, verify, context handling and key import follow Algorithms 1–3 and 6–8. |
| Encodings | both engines | `Encoding` | One generic theorem covers the LSB-first bit packer and unpacker for every width. From it, ByteEncode/ByteDecode (FIPS 203), SimpleBitPack/BitPack and their unpackers (FIPS 204) follow. `decode_12` is equivalent to the modulus check. The hint codec equals FIPS 204 Algorithms 20/21 for every (k, ω) and is canonical: an accepted hint section re-encodes to the same bytes, so signatures are not malleable. Key, ciphertext and signature layouts and sizes match both standards. |
| SLH-DSA | `slhdsa/slhdsa_engine.ml` | `SLHDSA` | The stack-based `treehash` returns the FIPS 205 node and authentication path for every height, leaf index and hash function. `compute_root` inverts it. `message_to_fors_indices` equals base_2b even though its accumulator wraps, at 63, 32 and 31 bits. WOTS+, XMSS, FORS, the hypertree, the ADRS encodings and the §11 hash selection match FIPS 205. Top-level key generation, signing and verification match Algorithms 18–22, and verification accepts every signature the code produces. |
| Hash functions | `lib/keccak.ml`, `slhdsa/slhdsa_hash.ml` | `Hash` | `permute` is Keccak-f[1600] on every state. The sponge is FIPS 202 SPONGE with pad10*1 and the domain suffixes. SHAKE output is prefix-consistent. SHA-256 and SHA-512 match FIPS 180-4. HMAC matches FIPS 198-1, and MGF1 matches RFC 8017. Round constants, rotation offsets and the SHA-2 constants are derived from their mathematical definitions, not copied. |
| Loops and state machines | all three engines | `tla/` | 13 TLC models, listed in [`tla/README.md`](tla/README.md). They cover the hint codec over all strings of a small size, treehash and the hypertree traversal, the signing loop at its real bound, the four rejection samplers' retry behaviour, the bit packers at their real widths, FORS index wrap-around, the Keccak sponge, SHA-2 padding and MGF1, and implicit rejection. |

### End to end

The areas above were proved separately, each assuming the other areas'
building blocks as explicit hypotheses. `lean/OcamlPq/EndToEnd/` discharges
those hypotheses. The concrete models from the arithmetic, encoding and hash
areas fill in every building block, and the FIPS building blocks come only
from the standards' transcriptions. Adapters between the areas' data
representations only re-index or re-type values. The resulting theorems
relate each engine directly to its standard:

- **ML-KEM** (`EndToEnd/MLKEM`: `mlkem512_endToEnd`, `mlkem768_endToEnd`,
  `mlkem1024_endToEnd`).
  - `keygen_internal`, `encapsulate_internal` and `decapsulate` compute FIPS
    203 Algorithms 16–18, including implicit rejection.
  - Both the implementation and the spec use their FIPS 202 hash functions.
  - `parse_ek` succeeds exactly when the §7.2 check passes.
  - `correct_e2e`: decapsulation returns the encapsulated key. The FIPS
    noise bound is its only hypothesis.
- **ML-DSA** (`EndToEnd/MLDSA`: `mldsa44_endToEnd`, `mldsa65_endToEnd`,
  `mldsa87_endToEnd`).
  - Key generation equals Algorithms 1 and 6.
  - `sign_mu_with_randomness` returns Algorithm 7's signature exactly when
    Algorithm 7 finishes within 821 iterations, and `Signing_failed`
    otherwise.
  - `sign`, `sign_deterministic` and `verify` equal Algorithms 2, 3 and 8.
  - Key import accepts exactly the keys that Algorithm 6 could produce.
  - `sign_verify`: the code's verifier accepts every signature the code's
    signer returns. Its algebraic premise is derived from the NTT theorems.
- **SLH-DSA** (`EndToEnd/SLHDSA`), for all twelve parameter sets.
  - Key generation, signing and verification, over the verified SHA-2 and
    SHAKE code, equal FIPS 205 Algorithms 18–20, 22 and 24.
  - The §11 hash functions are built from the FIPS 180-4, 202 and 198-1 and
    RFC 8017 specifications.
  - `verify_sign_e2e` and `verify_sign_cross_platform`: verification accepts
    every signature the code produces, including when signing and
    verification run on different platforms.

The remaining hypotheses are the probabilistic ones from the
[trust base](#trust-base), plus a few facts every input satisfies:

- ML-DSA signing keys have secrets in [−η, η]. This is proved for generated
  and imported keys.
- SLH-DSA key parts are n bytes long, and messages are shorter than 2⁵⁷
  bytes, as every OCaml string is.

The integration found no false hypothesis about the OCaml code. It did find
places where the areas' statements did not line up, which the end-to-end
layer bridges:

- ML-DSA's composition assumed its building blocks equal FIPS on *all*
  inputs. The code only agrees on the inputs the algorithms produce. For
  example, the packers spill out-of-range values into the next code, and
  `use_hint` reads a hint value of 2 as 1.
- ML-DSA's composition required the samplers to terminate on every seed.

The end-to-end layer proves agreement on every reachable input and assumes
termination only at the inputs actually used.

### Portability

OCaml's `int` is 63 bits wide in 64-bit native code, 32 bits under
`js_of_ocaml`, and 31 bits in 32-bit native code and under `wasm_of_ocaml`.
The Lean models evaluate `int` expressions over the integers. For every
modelled function, the proofs show that each intermediate fits in 31 bits,
so the result is the same on every platform (`Common/Int.lean` defines
`Portable`). Where the code relies on wrap-around, as the FORS index
accumulator does, the proofs show the result is still correct at every
width. `Int32.t` and `Int64.t` code is modelled with fixed-width bit vectors.

## Findings

No bug was found. The verification did establish the following:

- **Stricter than the standards.**
  - `unpack_eta` rejects coefficient codes above 2η in expanded ML-DSA
    signing keys. FIPS 204 `skDecode` would decode them to out-of-range
    coefficients.
  - `decapsulation_key_of_expanded`, reachable only through
    `mlkem.for_testing`, applies the modulus check to ŝ and the embedded
    encapsulation key. FIPS 203 §7.3 requires only the length and hash
    checks.

  Neither function rejects a key that a conforming key generator produces.
- **Hazards no caller can reach.** Each was proved or model-checked
  unreachable from the library's callers:
  - `treehash` would blit out of bounds for a leaf index in
    [2^h, 2^(h+1)).
  - `encode_signature` writes with `Bytes.unsafe_set` and would write past
    the hint area for more than ω hints; the signer rejects that case
    first.
  - `ct_equal` reads its second argument at the first argument's length;
    ciphertext types fix the length.
  - `u16_le` silently truncates values of 2^16 or more.
  - The SLH-DSA `mgf1` has no RFC 8017 "mask too long" check; it is only
    called with outputs of at most 49 bytes.
  - With a 31-bit `int`, the SHA-2 padding length computation overflows for
    a single input of about 1 GiB. `Bytes.make` then raises; a wrong digest
    is never returned.
- **An untested path.** For about one ML-DSA-65 key in 13,000, ExpandS needs
  more than the first 272 bytes of SHAKE256 output, and the sampler retries
  with a longer prefix. None of the NIST vectors reach that path. The proofs
  cover it. `test/mldsa_vectors/mldsa_eta_restart_keygen_65_tests.txt` adds
  three such seeds, with answers generated independently by OpenSSL, as a
  regression test.

The other retry paths (SampleNTT, RejNTTPoly and SampleInBall) have
probabilities between 2⁻⁸⁸ and 2⁻²⁵⁶ per call, far too rare to test with
real inputs. For those paths the Lean proofs are the evidence. The
TLA+ work adds a test with the initial prefixes shrunk so that almost every
call retries; outputs stayed byte-identical.

## Trust base

A theorem here is only as strong as the following assumptions:

- **The models are faithful to the OCaml code.** Each model was transcribed
  by hand and cites the file and lines it models. Loop structure, constants
  and integer operations follow the source literally. The transcriptions
  were reviewed, and several were run against the real OCaml code on
  boundary and random inputs; all agreed.
- **The FIPS transcriptions are faithful to the standards.** The
  specifications were written from the standards' pseudo-code, not from the
  implementation. The hash specifications are checked against published
  known answers inside Lean.
- **OCaml semantics.** The models assume the standard semantics of OCaml's
  integer, `Int32`, `Int64`, string and array operations. The compiler, the
  runtime and the garbage collector are outside the proof.
- **Lean's kernel and Mathlib.** No proof uses `native_decide`, `bv_decide`,
  `sorry` or a new axiom. `lean/OcamlPq/Audit.lean` prints the axioms each
  headline theorem depends on; only `propext`, `Classical.choice` and
  `Quot.sound` appear.
- **TLC's exhaustive search** at the sizes each model states.

Probabilistic properties are hypotheses, not theorems. The two are
termination of the rejection samplers and the noise bound behind ML-KEM
decryption correctness. Where a result depends on termination, it covers
every run that terminates. The code and the specification diverge on
exactly the same inputs.

## Running the checks

Requirements:

- [elan](https://github.com/leanprover/elan), which installs the Lean
  toolchain pinned in `lean/lean-toolchain`
- a Java runtime
- `tla2tools.jar` from the
  [TLA+ releases](https://github.com/tlaplus/tlaplus/releases)

```sh
TLA2TOOLS=/path/to/tla2tools.jar sh formal/check.sh
```

`check.sh` performs these steps:

1. Fetches Mathlib's prebuilt cache.
2. Rejects `sorry`, `admit` and new axioms.
3. Builds every proof, which takes about 5 minutes on a 10-core laptop.
4. Prints and checks the axiom audit.
5. Runs every TLA+ model, which takes 4 to 6 minutes.

To work on one area, build it on its own:

```sh
cd formal/lean
lake exe cache get
lake build OcamlPq.SLHDSA
```

## Layout

| Path | Contents |
| --- | --- |
| `lean/OcamlPq/Common/Int.lean` | OCaml `int` semantics: platform widths, wrap-around, `Portable`, truncating division |
| `lean/OcamlPq/MLKEM/` | ML-KEM field arithmetic, compression, NTT |
| `lean/OcamlPq/MLKEMAlg/` | ML-KEM sampling, K-PKE, KEM, key handling, correctness |
| `lean/OcamlPq/MLDSA/` | ML-DSA modular arithmetic, NTT, rounding, hints, signer checks |
| `lean/OcamlPq/MLDSAAlg/` | ML-DSA samplers, expansion, key generation, signing loop, interface |
| `lean/OcamlPq/Encoding/` | Bit packing, ML-KEM and ML-DSA encodings, hint codec, layouts |
| `lean/OcamlPq/SLHDSA/` | SLH-DSA addresses, base_2b, WOTS+, XMSS, FORS, treehash, hypertree, top level |
| `lean/OcamlPq/Hash/` | Keccak-f[1600], sponge, SHA-256, SHA-512, HMAC, MGF1, known answers |
| `lean/OcamlPq/EndToEnd/` | The areas linked into end-to-end theorems for each engine |
| `lean/OcamlPq/Audit.lean` | Axiom audit of the headline theorems |
| `tla/` | TLA+ models, their configurations, `check.sh` and a README |
| `check.sh` | Runs every check |
