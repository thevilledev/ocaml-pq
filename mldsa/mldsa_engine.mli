type error =
  | Invalid_length of { what : string; expected : int; actual : int }
  | Invalid_encoding of string
  | Context_too_long of int
  | Signing_failed

val pp_error : Format.formatter -> error -> unit

module type PARAMETERS = sig
  val name : string
  val k : int
  val l : int
  val eta : int
  val tau : int
  val gamma1 : int
  val gamma2 : int
  val omega : int
  val c_tilde_bytes : int
end

module type S = sig
  type nonrec error = error =
    | Invalid_length of { what : string; expected : int; actual : int }
    | Invalid_encoding of string
    | Context_too_long of int
    | Signing_failed

  val pp_error : Format.formatter -> error -> unit

  type signing_key
  type verification_key
  type signature

  val seed_size : int
  val signing_key_size : int
  val verification_key_size : int
  val signature_size : int

  val generate :
    random:(int -> string) -> unit -> signing_key * verification_key

  val signing_key_of_seed : string -> (signing_key, error) result
  val signing_key_to_seed : signing_key -> string option
  val signing_key_of_octets : string -> (signing_key, error) result
  val signing_key_to_octets : signing_key -> string

  val verification_key_of_signing_key : signing_key -> verification_key
  val verification_key_of_octets : string -> (verification_key, error) result
  val verification_key_to_octets : verification_key -> string

  val signature_of_octets : string -> (signature, error) result
  val signature_to_octets : signature -> string

  val sign :
    ?context:string ->
    random:(int -> string) ->
    signing_key ->
    message:string ->
    (signature, error) result

  val sign_deterministic :
    ?context:string -> signing_key -> message:string -> (signature, error) result

  val verify :
    ?context:string ->
    verification_key ->
    message:string ->
    signature ->
    bool
end

module type INTERNAL = sig
  include S

  val sign_internal_for_testing :
    signing_key ->
    formatted_message:string ->
    randomness:string ->
    (signature, error) result

  val sign_mu_for_testing :
    signing_key ->
    mu:string ->
    randomness:string ->
    (signature, error) result

  val verify_internal_for_testing :
    verification_key -> formatted_message:string -> signature -> bool

  val verify_mu_for_testing :
    verification_key -> mu:string -> signature -> bool
end

module Make (P : PARAMETERS) : INTERNAL
module Mldsa44 : INTERNAL
module Mldsa65 : INTERNAL
module Mldsa87 : INTERNAL
