type error =
  | Invalid_length of { what : string; expected : int; actual : int }
  | Invalid_encoding of string

val pp_error : Format.formatter -> error -> unit

module type PARAMETERS = sig
  val k : int
  val eta1 : int
  val eta2 : int
  val du : int
  val dv : int
end

module type S = sig
  type nonrec error = error =
    | Invalid_length of { what : string; expected : int; actual : int }
    | Invalid_encoding of string

  val pp_error : Format.formatter -> error -> unit

  type encapsulation_key
  type decapsulation_key
  type ciphertext
  type shared_secret

  val seed_size : int
  val encapsulation_key_size : int
  val expanded_decapsulation_key_size : int
  val ciphertext_size : int
  val shared_secret_size : int

  val decapsulation_key_of_seed : string -> (decapsulation_key, error) result
  val decapsulation_key_to_seed : decapsulation_key -> string option
  val decapsulation_key_of_expanded : string -> (decapsulation_key, error) result
  val decapsulation_key_to_expanded : decapsulation_key -> string
  val encapsulation_key_of_decapsulation_key : decapsulation_key -> encapsulation_key
  val encapsulation_key_of_octets : string -> (encapsulation_key, error) result
  val encapsulation_key_to_octets : encapsulation_key -> string
  val ciphertext_of_octets : string -> (ciphertext, error) result
  val ciphertext_to_octets : ciphertext -> string
  val shared_secret_to_octets : shared_secret -> string

  val keygen_internal : d:string -> z:string -> (decapsulation_key, error) result
  val encapsulate_internal : encapsulation_key -> randomness:string ->
    (ciphertext * shared_secret, error) result
  val decapsulate : decapsulation_key -> ciphertext -> shared_secret

  val ct_equal_for_testing : string -> string -> int
  (** [ct_equal_for_testing a b] is the comparison decapsulation uses: 1 if
      [a] and [b] are equal, 0 otherwise, including when their lengths
      differ. *)
end

module Make (P : PARAMETERS) : S
module Mlkem512 : S
module Mlkem768 : S
module Mlkem1024 : S
