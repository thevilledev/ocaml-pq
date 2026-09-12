# Releasing ocaml-pq

[Back to the README](../README.md)

The source tree and generated opam metadata use one release version. Release
0.1.0 is recorded in `dune-project`, `mlkem.opam`, `mldsa.opam`,
`slhdsa.opam`, and the [changelog](../CHANGES.md).

Run all commands from the repository root. See the
[development guide](development.md) for individual checks.

## Before tagging

From a clean checkout, validate all three packages:

```sh
opam install . --deps-only --with-test --with-doc
opam install dune-release
opam lint mlkem.opam mldsa.opam slhdsa.opam
opam exec -- dune build @install @runtest @doc
opam install . --with-test --with-doc
dune-release check
```

Confirm that every required CI job passes on the Avrea runners. Inspect the
non-blocking lower-bounds result too: understand any failure and correct package
constraints before publishing even though that job does not block ordinary
pull requests.

## Publish 0.1.0

Commit every release file before creating the annotated tag; distribution
archives ignore uncommitted changes. Then use the standard Dune release flow:

```sh
dune-release tag 0.1.0
dune-release bistro
```

The release tool creates and checks the archive, publishes the GitHub release,
generates opam-repository entries with archive checksums, and opens the
opam-repository pull request. Review all three generated entries:

- `packages/mlkem/mlkem.0.1.0/opam`
- `packages/mldsa/mldsa.0.1.0/opam`
- `packages/slhdsa/slhdsa.0.1.0/opam`

Wait for opam-repository CI and maintainer review before announcing the
release. Never replace an archive behind a published 0.1.0 URL; publish a new
patch release for any correction.
