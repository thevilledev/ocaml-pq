(** SLH-DSA-SHA2-128s, as standardized by FIPS 205.

    The SHA2 hash family at security level 128, so the security
    parameter [n] is 16 bytes. This is the small-signature ([s]) variant:
    smaller signatures and slower signing than SLH-DSA-SHA2-128f.

    Operations, randomness contract, and encodings are documented in
    the shared signature below. *)
include Slhdsa_engine.S
