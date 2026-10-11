# Releasing ocaml-pq

[Back to the README](../README.md)

The source tree and generated opam metadata use one release version. Release
0.2.1 is recorded in `dune-project`, `mlkem.opam`, `mldsa.opam`,
`slhdsa.opam`, and the [changelog](../CHANGES.md).

Run all commands from the repository root. See the
[development guide](development.md) for individual checks.

## Release archives

opam downloads each release from the archive that GitHub generates for its
tag, such as
`https://github.com/thevilledev/ocaml-pq/archive/refs/tags/v0.2.1.tar.gz`.
GitHub builds that archive with `git archive`, so it leaves out the paths
marked `export-ignore` in `.gitattributes`: the full test corpora and
`formal/`. The package tests in the archive check the known-answer subset in
`test/kat` instead.

Do not publish with `dune-release distrib` or `dune-release bistro`.
dune-release builds its own archive from a full clone and ignores
`export-ignore`, so that archive would carry about 21 MB of test corpora.

## Before tagging

From a clean checkout, validate all three packages:

```sh
opam install . --deps-only --with-test --with-doc
opam lint mlkem.opam mldsa.opam slhdsa.opam
opam exec -- dune build @install @runtest @doc
opam install . --with-test --with-doc
```

Then build the archive that the tag will produce, check its size, and run the
package tests from it as opam-repository CI does:

```sh
git archive --format=tar.gz --prefix=ocaml-pq/ -o /tmp/ocaml-pq.tar.gz HEAD
wc -c < /tmp/ocaml-pq.tar.gz
tar -xzf /tmp/ocaml-pq.tar.gz -C /tmp
cd /tmp/ocaml-pq && opam exec -- dune build -p mlkem,mldsa,slhdsa @install @runtest
```

The archive must stay under 512 KiB; the `Release archive` CI job enforces the
same limit. `git archive` reads `.gitattributes` from the commit, not from
the working tree, so run this on the commit you will tag.

Confirm that every required CI job passes on the Avrea runners. Inspect the
non-blocking lower-bounds result too: understand any failure and correct package
constraints before publishing even though that job does not block ordinary
pull requests.

## Publish 0.2.1

Commit every release file before creating the annotated tag; the archive
contains only what the tagged commit holds. Push the tag, then check the
size of the archive GitHub serves for it:

```sh
git tag -a v0.2.1 -m "ocaml-pq 0.2.1"
git push origin v0.2.1
curl -fsSL https://github.com/thevilledev/ocaml-pq/archive/refs/tags/v0.2.1.tar.gz | wc -c
```

Generate the opam-repository entries with opam-publish. It records the archive
URL and checksums from the tag archive. Review a dry run first, then publish,
which opens the opam-repository pull request:

```sh
opam publish -n https://github.com/thevilledev/ocaml-pq/archive/refs/tags/v0.2.1.tar.gz
opam publish https://github.com/thevilledev/ocaml-pq/archive/refs/tags/v0.2.1.tar.gz
```

Review all three generated entries:

- `packages/mlkem/mlkem.0.2.1/opam`
- `packages/mldsa/mldsa.0.2.1/opam`
- `packages/slhdsa/slhdsa.0.2.1/opam`

Wait for opam-repository CI and maintainer review before announcing the
release. Never move a published tag or replace an archive behind a published
0.2.1 URL; publish a new patch release for any correction.
