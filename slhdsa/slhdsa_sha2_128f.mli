(** SLH-DSA-SHA2-128f, as standardized by FIPS 205.

    The SHA2 hash family at security level 128, so the security
    parameter [n] is 16 bytes. This is the fast-signing ([f]) variant:
    faster signing and larger signatures than SLH-DSA-SHA2-128s.

    Operations, randomness contract, and encodings are documented in
    the shared signature below. *)
include Slhdsa_engine.S
