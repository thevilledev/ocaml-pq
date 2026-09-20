(** SLH-DSA-SHAKE-192f, as standardized by FIPS 205.

    The SHAKE hash family at security level 192, so the security
    parameter [n] is 24 bytes. This is the fast-signing ([f]) variant:
    faster signing and larger signatures than SLH-DSA-SHAKE-192s.

    Operations, randomness contract, and encodings are documented in
    the shared signature below. *)
include Slhdsa_engine.S
