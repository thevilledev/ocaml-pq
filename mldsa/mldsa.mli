(** Pure OCaml FIPS 204 module-lattice digital signatures.

    ML-DSA signs and verifies messages. Pick one parameter-set module and use
    it throughout; signing keys, verification keys, and signatures from
    different sets have incompatible types. The modules increase in security
    level and in key and signature size, and all three provide the same
    operations. *)

module Mldsa44 = Mldsa44
module Mldsa65 = Mldsa65
module Mldsa87 = Mldsa87
