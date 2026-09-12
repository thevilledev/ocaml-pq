# Security policy

This repository implements cryptographic primitives. Please do not open a
public issue for a suspected vulnerability that could put users at risk.
Use [GitHub private vulnerability reporting](https://github.com/thevilledev/ocaml-pq/security/advisories/new)
to report the issue confidentially to the maintainers. Include a reproducer,
the affected revision, and your assessment of impact when possible.

No release should be described as independently audited unless the audit and
the exact audited revision are linked from this file.

The initial `0.1.x` series has not received an independent cryptographic audit.

## Side-channel boundary

The implementations avoid secret-dependent source-level branches where the
standard requires constant-time selection, including ML-KEM implicit
rejection. The OCaml compiler, runtime, garbage collector, and host system do
not provide a verified constant-time execution model.

ML-DSA signing performs a variable number of rejection-sampling attempts.
Every attempt evaluates all rejection checks before deciding whether to try
again, but signing is not suitable for environments where an attacker can make
precise timing, cache, power, electromagnetic, or co-resident observations.
Use a separately audited side-channel-hardened implementation for that threat
model.
