(** ML-DSA-65, as standardized by FIPS 204.

    The default signing function is hedged: callers supply 32 fresh random
    bytes for each signature. Deterministic signing is available explicitly.
    Context strings are limited to 255 bytes by FIPS 204. *)

include Mldsa_engine.S
