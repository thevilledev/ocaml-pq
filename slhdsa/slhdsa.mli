(** Pure OCaml FIPS 205 SLH-DSA implementations.

    SLH-DSA signs and verifies messages using stateless hash-based
    signatures. Pick one parameter-set module and use it throughout; keys and
    signatures from different sets have incompatible types. All twelve sets
    provide the same operations.

    A set is chosen along three axes: the hash family ([Sha2] or [Shake]),
    the security level (128, 192, or 256), and the signing tradeoff. The
    small-signature ([s]) variants produce smaller signatures and sign more
    slowly; the fast-signing ([f]) variants do the reverse. Signatures are
    large in every case, and signing is far slower than ML-DSA; prefer the
    separate [mldsa] package unless a hash-based signature is specifically
    wanted. *)

module Sha2_128s = Slhdsa_sha2_128s
module Sha2_128f = Slhdsa_sha2_128f
module Sha2_192s = Slhdsa_sha2_192s
module Sha2_192f = Slhdsa_sha2_192f
module Sha2_256s = Slhdsa_sha2_256s
module Sha2_256f = Slhdsa_sha2_256f
module Shake_128s = Slhdsa_shake_128s
module Shake_128f = Slhdsa_shake_128f
module Shake_192s = Slhdsa_shake_192s
module Shake_192f = Slhdsa_shake_192f
module Shake_256s = Slhdsa_shake_256s
module Shake_256f = Slhdsa_shake_256f
