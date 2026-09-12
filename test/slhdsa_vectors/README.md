# SLH-DSA test vectors

These compact, line-oriented files were derived from the NIST ACVP-Server
FIPS 205 validation corpus. They cover deterministic key generation and one
deterministic external-message signature for each of the twelve standardized
SLH-DSA parameter sets.

Corpus source: NIST ACVP-Server revision
`975de31eb83d87039ec88934fdc47d8c312b892d`.

The source JSON files were:

- `SLH-DSA-keyGen-FIPS205/prompt.json`
- `SLH-DSA-keyGen-FIPS205/expectedResults.json`
- `SLH-DSA-sigGen-FIPS205/prompt.json`
- `SLH-DSA-sigGen-FIPS205/expectedResults.json`

SHA-256 checksums of the source JSON:

```text
bce170976f257ee3dfc8c54ea46722ccb553539847daa6d8048f0216cc28b51c  keygen prompt.json
f35f74b6676d6b369c87e88c36698f28c14d5929d31e507d910288c69258afee  keygen expectedResults.json
afa673eacdf0aec53512a159159b7632684adfcd0d88f8640a7f6f5796aacdc8  siggen prompt.json
71e8e0f7e4b0cfd1747314299204d9d4d50968d200a4ae873921eaa7aabeaad1  siggen expectedResults.json
```

SHA-256 checksums of the compact files:

```text
89bd43a6ba5dbe3194168281d1719df91ab73d5bd2337a0d5367fc2e5181b45f  keygen.txt
4127dbca821634fcbfa9d7383fd79b9d493483ecd2488e6665b2ec6ca3d69d8c  siggen.txt
```

The vectors are data consumed by tests; the implementation has no dependency
on the ACVP-Server.
