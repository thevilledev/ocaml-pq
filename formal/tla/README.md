# TLA+ models of ocaml-pq loops and state machines

These specifications model the loop-structured and stateful parts of the
ML-KEM (FIPS 203), ML-DSA (FIPS 204) and SLH-DSA (FIPS 205) implementations
as TLC-checkable state machines. The Lean development in `../lean` covers
functional correctness; these models cover the loops, where exhaustive
exploration at small sizes works well.

## Running

```sh
TLA2TOOLS=/path/to/tla2tools.jar ./check.sh          # all models
TLA2TOOLS=/path/to/tla2tools.jar ./check.sh SlhTreehash MldsaHintCodec
```

`check.sh` runs SANY on every module and TLC on every `.cfg`. It exits with a
non-zero status if a module fails to parse (SANY exits 0 on semantic errors,
so the script also checks SANY's output), if TLC reports a violation, if an
`ASSUME` is false, or if TLC does not print "No error has been found".
Settings:

- `TLA2TOOLS`: path to the jar. Defaults to `tla2tools.jar` next to the script.
- `JAVA`: the Java binary. Defaults to `java` on `PATH`.
- `TLC_WORKERS`: TLC worker count. Defaults to `auto`.

TLC metadata goes to a temporary directory that the script deletes when it
exits. The script passes `-noGenerateSpecTE`, so no trace files are written
next to the specs. A whole run takes about 6 minutes on a 10-core laptop.

## How the models are built

Each model has two parts:

1. A state machine that transcribes the OCaml code. The OCaml refs and array
   contents are the state variables, and each loop iteration is one TLC
   action. The OCaml bit expressions are written out literally (`BitOps.tla`
   provides `land`, `lor`, `lxor`, `lsl` and `lsr`). Every buffer access is
   checked against the buffer's bounds and recorded in a `fault` variable.
2. A separate TLA+ definition of the FIPS algorithm. It is a recursive
   function that follows the standard's pseudo-code, not the OCaml code.

The invariants check three things:

- **Safety:** `NoFault`, `TypeOK`, accumulator ranges and stack depth.
- **Agreement with FIPS:** at termination, the OCaml result equals the FIPS
  result.
- **Termination:** a step counter stays within a static bound, `StepBound`.

Deadlock checking stays on. A finished state stutters explicitly, so TLC
reports a deadlock only when a non-final state has no successor.

Several abstractions keep the searches exhaustive and small:

- **Symbolic bits.** This applies to code that only shifts, masks and ORs:
  the bit packers, `base_2b`, the digest split, the Keccak lane mapping, the
  SampleInBall sign register and SHA-2 padding. Each input bit is an atom,
  and each machine bit is the set of atoms ORed into it. The operations are
  exact at bit level, so one symbolic run covers every input value, at the
  real word widths (63-bit OCaml `int`, `Int64`, `Int32`) and with the real
  parameters. The model also flags any OR of overlapping bits and any bit
  shifted out of the word.
- **Lazily chosen XOF streams.** The rejection samplers re-read a SHAKE
  prefix from the start on every retry. The model therefore keeps one stream
  that grows only when the OCaml code reads a position it has not reached
  yet. At that point TLC branches over a byte alphabet, so every stream over
  the alphabet is explored. `KeccakSponge` checks that output of length `L`
  is a prefix of output of length `2L`. The per-byte arithmetic (d1/d2,
  CoeffFromThreeBytes, CoeffFromHalfByte, the η = 2 reduction by `205 * v lsr
  10`) is checked for every byte value by `ASSUME`s. The alphabet therefore
  only has to produce every accept/reject pattern.
- **Free-term hashes** for Merkle trees. A node is the term `<<"H", height,
  index, left, right>>`, so two nodes are equal exactly when they come from
  the same computation at the same address.
- **Nondeterministic outcomes** for the ML-DSA rejection loop. The loop runs
  in lock-step with FIPS, using the real bound of 821 attempts.

TLC integers are 32-bit, so `Int32` and `Int64` values are modelled as bit
vectors, and products that could overflow are split. The splits are
documented where they occur.

## Models

"States" is the number of distinct states, and "time" is the wall-clock
time of the final `check.sh` run. Both come from TLC 2026.09.22 with
10 workers on a machine that other jobs were also using.

| Model | OCaml modelled | FIPS reference | Constants (cfg) | Properties checked | States | Time |
|---|---|---|---|---|---|---|
| `MldsaHintCodec` | `mldsa_engine.ml` 652–676 (hint part of `decode_signature`: `valid`, endpoint checks, strictly increasing positions, trailing zeros), 694–704 (hint part of `encode_signature`) | FIPS 204 Alg. 20 HintBitPack, Alg. 21 HintBitUnpack | N = 7 (byte alphabet = ring degree, as 256 = 256 in the real code), K = 3, ω = 4. All 7^7 strings and all 7,547 hint matrices of weight ≤ ω | TypeOK, NoFault (reads and writes in bounds; encoder never writes into the endpoint area), DecodeMatchesFIPS (same accept set, same output), Canonical (decode(s) = h ⇒ encode(h) = s), EncodeMatchesFIPS, RoundTrip (decode(encode(h)) = h), FIPSRoundTrip, StepBound | 10,357,460 | 52 s |
| `SlhTreehash` | `slhdsa_engine.ml` 337–370 `treehash` (stack, heights, offset, address fields, both auth-path blits), 372–392 `compute_root` | FIPS 205 Alg. 9–11 (xmss_node / sign / pkFromSig), 15–17 (fors_node / sign / pkFromSig) | heights 1..8; index_offset = t·2^h for t ∈ 0..2; every leaf_index ∈ {−1} ∪ [0, 2^h) | NoFault (stack depth ≤ h+1, no auth write at level h), StackInv (every stack entry is the FIPS node for its position), RootOK, AuthOK (each auth level written exactly once and equal to node((leaf≫j)⊕1, j); nothing written for −1), CaptureOnce (WOTS signature captured once), ComputeRootOK (OCaml compute_root = FIPS pkFromSig = root), StepBound | 804,852 | 45 s |
| `SlhHypertree` | `slhdsa_engine.ml` 487–513 (`bytes_to_u64`, `low_mask`, `split_message_digest`), 589–637 sign layer loop, 662–722 verify layer loop, 477–485 `merkle_root`, 168–176 `set_u64_be` | FIPS 205 Alg. 19/20 (digest split with unbounded toInt), Alg. 12/13 (ht_sign / ht_verify), Alg. 1/3 | the six FIPS 205 (h, d, a, k, m) sets (shared by SHA2 and SHAKE) plus 231 synthetic (h′ ≤ 17, d) with tree_bits = h′(d−1) ≤ 64, including d = 1 and tree_bits = 63 and 64; symbolic digest | NoFault (no unspecified shift ≥ 64, no bits lost in `Int64.to_int`, no overlapping `logor`), ForsAddressOK (FORS tree = idx_tree, keypair = idx_leaf in sign and verify), SignLayersOK and VerifyLayersOK (per-layer (layer, tree, leaf) equals ht_sign / ht_verify, and verify sees the same messages), TopTreeZero, VerifyAccepts (the final root is `merkle_root`'s pk_root), TreeAddressBytes (set_u64_be = toByte(tree, 12)[4..15]), StepBound | 7,967 | 10 s |
| `MldsaSignLoop` | `mldsa_engine.ml` 728–800 `attempt` (bound 821, κ = iteration·ℓ, `u16_le` nonces, rejection flag, `encode_signature` precondition) | FIPS 204 Alg. 7 (κ ← κ + ℓ), Alg. 34 ExpandMask nonces | real (ℓ, ω) for ML-DSA-44/65/87, real bound 821; every sequence of attempt outcomes (z / r0 / ct0 flags, hint count ∈ {0, ω, ω+1}) | KappaAgrees, NoncesInRange (every κ + r < 2^16 and u16_le = IntegerToBytes(·, 2)), NoncesFresh (strictly increasing, so never reused), EncodePrecond (encode sees ≤ ω hints), FailedIffAllReject, ResultIsFIPS (first attempt that FIPS accepts), StepBound | 7,395 | 2 s |
| `MlkemSampleNTT` | `mlkem_engine.ml` 312–336 `sample_ntt` / `draw` restart | FIPS 203 Alg. 7 SampleNTT | n = 3, q = 3329; initial prefix 3, 4 or 5 bytes, doubling up to 16; alphabet {0x00, 0x5A, 0xFF}; ASSUMEs cover d1/d2 for all 2^16 byte pairs | NoFault (reads < output_length, writes < n, including the `count < n` guard on d2), CountInv (the OCaml state equals FIPS on the bytes read), DoneOK (same result; consumes exactly the FIPS byte count), GaveUpOK, StepBound | 816,348 | 18 s |
| `MldsaRejNTTPoly` | `mldsa_engine.ml` 328–348 `uniform_polynomial` | FIPS 204 Alg. 30 RejNTTPoly, Alg. 14 CoeffFromThreeBytes | n = 3, q = 8380417; initial prefix 3, 4 or 5 bytes, up to 16; alphabet {0x00, 0x80, 0xFF}; ASSUMEs cover b2 masking (all 256 values) and b0 + 256·b1 (all 2^16 pairs) | NoFault, CountInv, DoneOK, GaveUpOK, StepBound | 2,536,140 | 24 s |
| `MldsaRejBoundedPoly` | `mldsa_engine.ml` 350–375 `eta_polynomial` (reads the whole prefix; `accept` guard) | FIPS 204 Alg. 31 RejBoundedPoly, Alg. 15 CoeffFromHalfByte | n = 3, η ∈ {2, 4}; initial prefix 1, 2 or 3 bytes, up to 8; alphabet {0x31, 0x70, 0x9E, 0xF8, 0xFF}; ASSUMEs cover the nibble split (all bytes) and `accept` (all nibbles, both η) | NoFault, CountInv, DoneOK, GaveUpOK, StepBound | 470,624 | 7 s |
| `MldsaSampleInBall` | `mldsa_engine.ml` 383–414 `challenge_polynomial` (Int64 sign register, `complete` flag, swap, restart) | FIPS 204 Alg. 29 SampleInBall | n = 4, τ ∈ {1, 2, 3, 4}; 8 symbolic sign bytes (every 64-bit sign word); initial prefix 8 or 9 bytes, up to 18; candidate alphabet {0, 2, 3, 255} | NoFault, SignsInv (after m placements, signs = h ≫ m in BytesToBits order), DoneOK, Weight (exactly τ entries are ±1), GaveUpOK, StepBound | 7,944,331 | 103 s |
| `BitPack` | `mldsa_engine.ml` 265–300 `pack_codes` / `unpack_codes`; `mlkem_engine.ml` 255–287 `encode_compressed` / `decode_compressed`; 125–137 `compress` / `decompress` (ASSUME); 230–253 `encode_12` / `decode_12` (ASSUME) | FIPS 204 Alg. 16/18 (and 9, 12, 13); FIPS 203 Alg. 5/6 ByteEncode/ByteDecode, eq. 4.7/4.8 Compress/Decompress, §7.2 modulus check | real widths with n = 256 (ML-DSA 3, 4, 6, 10, 13, 18, 20; ML-KEM 1, 4, 5, 10, 11); sweep of widths 1..20 (dsa) and 1..12 (kem) × 1..9 codes; symbolic codes and bytes; compress for all x < q and d ∈ {1, 4, 5, 10, 11}; decompress for all y < 2^d | NoFault (writes and reads in bounds, nothing shifted out of the 63/64-bit accumulator, no overlapping lor), AccRange (accumulator < 2^(b+7)), BytesWritten = count·b/8, PackIsFIPS, UnpackIsFIPS, RoundTrips (unpack∘pack = id and pack∘unpack = id), StepBound | 48,687 | 31 s |
| `SlhBase2b` | `slhdsa_engine.ml` 394–408 `message_to_fors_indices` (`total` wraps mod 2^63), 282–299 `base_w_nibbles` / `chain_lengths` (ASSUMEs) | FIPS 205 Alg. 4 base_2b with unbounded `total`; Alg. 7/8 checksum | the six FIPS (a, k) pairs with W = 63; W-bit analogues W ∈ {10, 12, 16, 20, 31, 32} with every a ≤ W−7 and k ≤ 5; symbolic message; checksum digits for every checksum 0..15·len1, n ∈ {16, 24, 32} | NoOverlap (`+` never carries), InputBound (bytes read = ⌈ka/8⌉), BitsRange, IndicesFIPS (every index equals FIPS despite the wrap), StepBound | 3,957 | 2 s |
| `KeccakSponge` | `keccak.ml` 87–115 `sponge` with 68–85 `load64_le` / `xor_block` / `store64_le` (identical copies in `mldsa_keccak.ml`, `slhdsa_hash.ml`) | FIPS 202 Alg. 8 SPONGE, Alg. 9 pad10*1, SHA3 (M‖01) / SHAKE (M‖1111), App. B.1 bit order | rates 72, 136 (SHA3) and 136, 168 (SHAKE), plus abstract rates 8 and 16 with both suffixes; every input length 0..2r (all rem ∈ [0, r−1], including rem = r−1); every output length 0..3r; symbolic message and abstract permutation | AbsorbOK (lane-by-lane XORed blocks equal P_i‖0^c, and the permutation count equals len(P)/r), TailBytesOK (byte-level pad10*1 with suffix), SqueezeOK (output length and permutation count max(0, ⌈d/r⌉−1)), PrefixOK (output byte i depends only on i), StepBound | 9,008 | 39 s |
| `MlkemDecaps` | `mlkem_engine.ml` 411–417 `ct_equal`, 508–516 `select_secret`, 518–524 `decapsulate` | FIPS 203 Alg. 18 (implicit rejection) | every (c, c′) ∈ {0x00, 0x01, 0x80, 0xFF}^3 × same; 2-byte secrets; ASSUMEs cover the Int32 zero test for every diff ∈ 0..255 and select_secret for every byte pair and choose_left ∈ {0, 1} | DiffInv, CtEqualOK (1 iff c = c′, and only 0 or 1), DecapsOK (K′ iff c = c′, otherwise K̄), StepBound | 32,768 | 4 s |
| `SlhSha2Pad` | `slhdsa_hash.ml` 162–182 / 269–284 (SHA-256 / SHA-512 padding and block count), 329–337 `mgf1`, 126–137 `set_u32_be`, 321–323 HMAC K0 (ASSUME) | FIPS 180-4 §5.1.1/5.1.2/5.2; RFC 8017 B.2.1 MGF1; FIPS 198-1 steps 1–3 | every message length < 3 blocks, for both hashes; MGF1 output lengths 0..200 with 32- and 64-byte digests; HMAC key lengths 0..2B+1 | NoFault (length bytes inside the buffer and never over the message or 0x80; `String.sub` in range), PadOK (padded buffer and block count), MgfOK (output = leading m bytes of H(seed‖C(0))‖…, and C = I2OSP(counter, 4)), StepBound | 9,508 | 3 s |

`BitOps.tla` is a helper module with no configuration of its own.

## Results

TLC finds no violations in any configuration. None of the models found a
behaviour where the OCaml code differs from the FIPS algorithm or accesses
memory out of bounds.

- **Hint codec.** Decoding accepts exactly the canonical encodings. That
  includes rows where `valid` turns false partway through while later
  positions are still written, and the trailing-zero loop, which starts
  from the last valid endpoint.
- **Treehash.** The stack never exceeds `height + 1` entries, and the
  authentication blit at level `height` is unreachable for `leaf_index <
  2^height`. With `leaf_index ∈ [2^h, 2^(h+1))` the model reaches exactly that
  blit, which would be out of bounds. No caller passes such a value, and
  `SlhHypertree` checks the masking that guarantees it.
- **FORS indices.** The unmasked `total` wraps modulo 2^63 without harm. An
  index needs bit positions up to `bits + a − 1 ≤ a + 6`, and `a ≤ 14`. The
  W-bit analogues show where wrap-around would start to matter. `a ≤ W − 7`
  always passes. Running the model outside that range (a scratch run, not
  part of `check.sh`) gives wrong indices at W = 10 for a ∈ {5, 6, 7, 9, 10},
  at W = 12 for a ≥ 9, and at W = 16 for a ∈ {11, 13, 14, 15}. For example,
  a = 8 at W = 10 passes because `bits` is then always 0.
- **Signing loop.** The largest mask nonce is 820·7 + 6 = 5746, well below
  2^16.

### Evidence the checks are not vacuous

Each model was also run on hand-mutated copies in a scratch directory. Every
mutation below was caught:

- **MldsaHintCodec:** `<=` → `<` in the strictly-increasing check,
  `endpoint > ω` → `>=`, and dropping the trailing-zero check. All three
  violate DecodeMatchesFIPS.
- **SlhTreehash:** an address index offset by one shift violates StackInv. An
  out-of-range leaf_index violates NoFault. Swapped compute_root operands
  violate ComputeRootOK.
- **SlhHypertree:**
  - Removing the `bits = 64` case of `low_mask` violates NoFault.
  - An arithmetic instead of a logical shift violates SignLayersOK.
  - Reading the leaf bytes one byte early violates ForsAddressOK.
- **MldsaSignLoop:** perturbing κ violates NoncesInRange. A bound of 14000
  attempts pushes a nonce to 2^16 or beyond and violates NoncesInRange.
  Accepting ω+1 hints violates EncodePrecond.
- **MlkemSampleNTT:** dropping the `count < n` guard on d2 violates TypeOK.
  `off + 1 < len` violates NoFault. A wrong d2 shift makes an ASSUME fail.
- **MldsaRejNTTPoly:** `position + 3 < len` violates GaveUpOK.
- **MldsaRejBoundedPoly:** 204 in place of 205 makes an ASSUME fail. A stale
  coefficient array for the high nibble violates CountInv.
- **MldsaSampleInBall:** swapping the order of the two coefficient writes
  violates DoneOK. An arithmetic shift of `signs` violates SignsInv.
- **BitPack:** `>= 8` → `> 8` violates AccRange. Moving the compress rounding
  threshold makes an ASSUME fail.
- **KeccakSponge:** ORing 0x80 into the tail before the suffix is written
  violates AbsorbOK. Permuting after the last squeeze block violates
  SqueezeOK.
- **MlkemDecaps:** shift 0 in place of 31, and a missing `lxor 1` in
  select_secret, make ASSUMEs fail. Overwriting `diff` instead of ORing into
  it violates DiffInv.
- **SlhSha2Pad:** `len + 8` in the SHA-256 padded length and a flooring
  MGF1 block count violate NoFault. `len + 9` in the SHA-512 padded length
  violates PadOK.

## What is not covered

- **Arithmetic outside the loops.** The models do not cover the Keccak-f and
  SHA-2 compression functions, the NTT, field reduction, `power2round`,
  `decompose`, `make_hint` / `use_hint`, or the norm checks. The Lean
  development and the ACVP vectors cover these.
- **Small sizes instead of real sizes.** The real initial prefixes (840, 272
  and 136 bytes) are replaced by small ones, and n, τ and ω are small. The
  restart logic does not depend on these values. To confirm this against the
  real OCaml, the four samplers were copied into a scratch directory with
  initial prefixes of 3, 3, 1 and 8 bytes, so almost every call restarts
  several times. The copies produced byte-identical ML-KEM keys, ciphertexts
  and shared secrets (including implicit rejection) and ML-DSA keys and
  signatures, compared with the unmodified code. Across 180,000 generated
  hint areas at the real n = 256, ω and k, `decode_signature` and
  `encode_signature` also agreed with an OCaml transliteration of Algorithms
  20/21. These checks live outside the repository.
- **Restricted alphabets.** Byte alphabets are restricted where the per-byte
  arithmetic has been checked separately by `ASSUME`. The data-independence
  argument is given in each header.
- **Constant-time behaviour** is not expressible in these models.
- **Very long messages.** SHA-2 length fields are checked for messages up to
  3 blocks. TLC cannot represent lengths of 2^29 bytes or more.
