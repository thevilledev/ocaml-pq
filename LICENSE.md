ISC License

Copyright (c) 2026 ocaml-pq contributors

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
PERFORMANCE OF THIS SOFTWARE.

## Third-party test data

The ISC license above covers the libraries and their sources. The test vector
corpora under `test/` are third-party data redistributed under their own
terms. They are test data only: no part of `mlkem`, `mldsa`, or `slhdsa`
links against or depends on these projects at build or run time.

| Directory | Source | License |
| --- | --- | --- |
| `test/vectors` | [google/boringssl](https://github.com/google/boringssl), [C2SP/wycheproof](https://github.com/C2SP/wycheproof) | Apache-2.0 (`test/vectors/LICENSE`, `test/wycheproof/LICENSE`) |
| `test/mldsa_vectors` | [google/boringssl](https://github.com/google/boringssl) | Apache-2.0 (`test/mldsa_vectors/LICENSE`) |
| `test/slhdsa_vectors` | [usnistgov/ACVP-Server](https://github.com/usnistgov/ACVP-Server) | NIST public-service notice (`test/slhdsa_vectors/LICENSE`) |
| `test/wycheproof` | [C2SP/wycheproof](https://github.com/C2SP/wycheproof) | Apache-2.0 (`test/wycheproof/LICENSE`) |

Each directory's `README.md` records the pinned upstream revision, the
original file names, and, where the files are derived rather than copied
verbatim, the checksums used to reproduce them.
