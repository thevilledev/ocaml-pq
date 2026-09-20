(** Pure OCaml ML-KEM (FIPS 203).

    ML-KEM is a key-encapsulation mechanism: it establishes a shared secret
    between two parties, it does not sign or encrypt messages. Pick one
    parameter-set module and use it throughout; keys, ciphertexts, and shared
    secrets from different sets have incompatible types.

    {!Mlkem768} is the recommended default for applications without an
    external security-level mandate. *)

module Mlkem512 : module type of Mlkem512
module Mlkem768 : module type of Mlkem768
module Mlkem1024 : module type of Mlkem1024
