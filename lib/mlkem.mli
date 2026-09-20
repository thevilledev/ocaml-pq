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

module Fips202 : sig
  (** The extendable-output functions of FIPS 202.

      ML-KEM is built on SHAKE, and a protocol that adopts ML-KEM often needs
      SHAKE itself: HPKE, for one, derives an ML-KEM key pair from keying
      material with SHAKE256. These are the functions ML-KEM runs on, exposed
      so that such a protocol does not carry a second Keccak.

      Both are one-shot. For inputs of one length they perform the same
      operations whatever the input holds, so the input may be secret, within
      the limits on constant-time execution that apply to this whole library.
      Outputs for one input are prefixes of each other. *)

  val shake128 : output_length:int -> string -> string
  (** [shake128 ~output_length input] is the first [output_length] bytes of
      SHAKE128 over [input], which has 128 bits of security strength. A
      negative [output_length] raises [Invalid_argument]. *)

  val shake256 : output_length:int -> string -> string
  (** [shake256 ~output_length input] is the first [output_length] bytes of
      SHAKE256 over [input], which has 256 bits of security strength. A
      negative [output_length] raises [Invalid_argument]. *)
end
