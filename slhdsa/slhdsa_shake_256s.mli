(** SLH-DSA-SHAKE-256s, as standardized by FIPS 205.

    The SHAKE hash family at security level 256, so the security
    parameter [n] is 32 bytes. This is the small-signature ([s]) variant:
    smaller signatures and slower signing than SLH-DSA-SHAKE-256f.

    Operations, randomness contract, and encodings are documented in
    the shared signature below. *)
include Slhdsa_engine.S
