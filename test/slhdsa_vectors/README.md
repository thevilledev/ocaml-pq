# SLH-DSA test vectors

These line-oriented files come from the NIST ACVP-Server FIPS 205 validation
corpus. They cover all twelve standardized SLH-DSA parameter sets:

- `keygen.txt`: 12 deterministic key-generation cases.
- `siggen.txt`: 12 deterministic signing cases.
- `siggen-extra.txt`: 24 additional signing cases, with one deterministic
  signature over an 8192-byte message and one randomized (hedged) signature
  using a 255-byte context per parameter set.
- `sigver.txt`: all 168 pure, external-message verification cases from the
  pinned corpus: 24 valid signatures and 144 invalid signatures.

Only cases supported by the public API are included. Internal-message and
pre-hash interfaces are excluded. Keeping signing to three known-answer
cases per parameter set limits the cost of the slowest variants.

Corpus source: [NIST ACVP-Server revision
`975de31eb83d87039ec88934fdc47d8c312b892d`](https://github.com/usnistgov/ACVP-Server/tree/975de31eb83d87039ec88934fdc47d8c312b892d/gen-val/json-files).

The source JSON files were:

- `SLH-DSA-keyGen-FIPS205/prompt.json`
- `SLH-DSA-keyGen-FIPS205/expectedResults.json`
- `SLH-DSA-sigGen-FIPS205/prompt.json`
- `SLH-DSA-sigGen-FIPS205/expectedResults.json`
- `SLH-DSA-sigVer-FIPS205/prompt.json`
- `SLH-DSA-sigVer-FIPS205/expectedResults.json`

SHA-256 checksums of the original key-generation and signing source JSON:

```text
bce170976f257ee3dfc8c54ea46722ccb553539847daa6d8048f0216cc28b51c  keygen prompt.json
f35f74b6676d6b369c87e88c36698f28c14d5929d31e507d910288c69258afee  keygen expectedResults.json
afa673eacdf0aec53512a159159b7632684adfcd0d88f8640a7f6f5796aacdc8  siggen prompt.json
71e8e0f7e4b0cfd1747314299204d9d4d50968d200a4ae873921eaa7aabeaad1  siggen expectedResults.json
```

SHA-256 checksums of the original compact files:

```text
89bd43a6ba5dbe3194168281d1719df91ab73d5bd2337a0d5367fc2e5181b45f  keygen.txt
4127dbca821634fcbfa9d7383fd79b9d493483ecd2488e6665b2ec6ca3d69d8c  siggen.txt
```

## Reproduce the additional vectors

`import.py` uses only the Python standard library. It verifies all four
signing and verification source files against pinned checksums before
writing anything. It joins prompts and expected results by NIST group and
case IDs, which are retained in the output for tracing failures.

With the pinned ACVP-Server checkout available locally, run from this
repository's root:

```sh
python3 test/slhdsa_vectors/import.py \
  /path/to/ACVP-Server/gen-val/json-files test/slhdsa_vectors
cd test/slhdsa_vectors
shasum -a 256 -c SHA256SUMS
```

The importer regenerates `siggen-extra.txt`, `sigver.txt`, and their
`SHA256SUMS`. `SOURCE_SHA256SUMS` records the four source hashes. The original
`keygen.txt` and `siggen.txt` remain unchanged.

Each output row is tab-separated; byte strings are hexadecimal. Empty byte
strings are represented by empty fields.

| File | Columns |
| --- | --- |
| `siggen-extra.txt` | Parameter set, group/case ID, mode, secret key, message, context, randomness, expected signature |
| `sigver.txt` | Parameter set, group/case ID, public key, message, context, signature, `valid` or `invalid` |

The vectors derive from
[usnistgov/ACVP-Server](https://github.com/usnistgov/ACVP-Server). That
repository carries no `LICENSE` file at the pinned revision; its terms are
stated in its README, and the copied `LICENSE` here reproduces that notice
verbatim.

That notice asks that modified works state the nature of the change. The
change made here is a format conversion only, first made for the 0.1.0
release: the upstream JSON prompts and expected results were joined by group
and case ID and rewritten as the tab-separated files described above,
restricted to the cases the public API supports. No cryptographic field value
was altered. `import.py` performs the conversion and `SOURCE_SHA256SUMS`
pins the inputs it was run against.

The vectors are data consumed by tests; the implementation has no dependency
on the ACVP-Server. Normal test runs require neither Python nor network access.
