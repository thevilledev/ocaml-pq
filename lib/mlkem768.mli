(** ML-KEM-768, as standardized by FIPS 203.

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
(** [pp_error] formats a parsing error for humans. *)

type encapsulation_key
type decapsulation_key
type ciphertext
type shared_secret

val seed_size : int
(** The size of a seed-encoded decapsulation key: 64 bytes ([d || z]). *)

val encapsulation_key_size : int
(** The size of an encoded encapsulation key: 1184 bytes. *)

val ciphertext_size : int
(** The size of a ciphertext: 1088 bytes. *)

val shared_secret_size : int
(** The size of a shared secret: 32 bytes. *)

val generate : random:(int -> string) -> unit -> decapsulation_key * encapsulation_key
(** [generate ~random ()] creates a key pair from 64 bytes obtained from
    [random]. *)

val decapsulation_key_of_seed : string -> (decapsulation_key, error) result
(** [decapsulation_key_of_seed seed] expands the canonical 64-byte [d || z]
    representation. *)

val decapsulation_key_to_seed : decapsulation_key -> string
(** [decapsulation_key_to_seed key] returns a fresh 64-byte seed encoding.
    The result is secret key material. *)

val encapsulation_key_of_decapsulation_key : decapsulation_key -> encapsulation_key
val encapsulation_key_of_octets : string -> (encapsulation_key, error) result
val encapsulation_key_to_octets : encapsulation_key -> string

val ciphertext_of_octets : string -> (ciphertext, error) result
val ciphertext_to_octets : ciphertext -> string

val shared_secret_to_octets : shared_secret -> string
(** [shared_secret_to_octets secret] returns a fresh 32-byte string. *)

val encapsulate : random:(int -> string) -> encapsulation_key -> ciphertext * shared_secret
(** [encapsulate ~random key] obtains 32 bytes from [random], then produces a
    ciphertext and shared secret. *)

val decapsulate : decapsulation_key -> ciphertext -> shared_secret
(** [decapsulate key ciphertext] always returns a shared secret. Invalid
    same-length ciphertexts are handled with FIPS 203 implicit rejection. *)
