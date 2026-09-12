(** ML-KEM-1024, as standardized by FIPS 203.

    Keys, ciphertexts, and shared secrets have distinct abstract types. All
    parsing functions reject inputs of the wrong length. Encapsulation-key
    parsing also performs the FIPS 203 modulus check.

    The caller supplies randomness so that this library stays portable across
    Unix, MirageOS unikernels, and [js_of_ocaml]. The callback must return
    exactly the requested number of cryptographically secure random bytes. *)

type error = Mlkem_engine.error =
  | Invalid_length of { what : string; expected : int; actual : int }
  | Invalid_encoding of string

val pp_error : Format.formatter -> error -> unit

type encapsulation_key
type decapsulation_key
type ciphertext
type shared_secret

val seed_size : int
(** The size of a seed-encoded decapsulation key: 64 bytes ([d || z]). *)

val encapsulation_key_size : int
(** The size of an encoded encapsulation key: 1568 bytes. *)

val ciphertext_size : int
(** The size of a ciphertext: 1568 bytes. *)

val shared_secret_size : int
(** The size of a shared secret: 32 bytes. *)

val generate : random:(int -> string) -> unit -> decapsulation_key * encapsulation_key

val decapsulation_key_of_seed : string -> (decapsulation_key, error) result
val decapsulation_key_to_seed : decapsulation_key -> string

val encapsulation_key_of_decapsulation_key : decapsulation_key -> encapsulation_key
val encapsulation_key_of_octets : string -> (encapsulation_key, error) result
val encapsulation_key_to_octets : encapsulation_key -> string

val ciphertext_of_octets : string -> (ciphertext, error) result
val ciphertext_to_octets : ciphertext -> string

val shared_secret_to_octets : shared_secret -> string

val encapsulate : random:(int -> string) -> encapsulation_key -> ciphertext * shared_secret
val decapsulate : decapsulation_key -> ciphertext -> shared_secret
