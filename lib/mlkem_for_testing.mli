(** Deterministic FIPS 203 entry points for known-answer testing only.

    This library exposes test entropy and expanded decapsulation keys. It must
    not be used by production protocols. Use the corresponding module from
    {!Mlkem} instead. *)

val sha3_256 : string -> string
val sha3_512 : string -> string
val shake128 : output_length:int -> string -> string
val shake256 : output_length:int -> string -> string
(** Internal hash entry points exposed for primitive known-answer tests. *)

val ct_equal : string -> string -> int
(** The comparison behind implicit rejection: 1 if the two strings are equal,
    0 otherwise, including when their lengths differ. *)

val keygen_512 : d:string -> z:string ->
  ((string * string), Mlkem.Mlkem512.error) result
val encapsulate_512 : encapsulation_key:string -> randomness:string ->
  ((string * string), Mlkem.Mlkem512.error) result
val decapsulate_512 : expanded_decapsulation_key:string -> ciphertext:string ->
  (string, Mlkem.Mlkem512.error) result

val keygen_768 : d:string -> z:string ->
  ((string * string), Mlkem.Mlkem768.error) result
(** Returns [(expanded_decapsulation_key, encapsulation_key)]. Both [d] and
    [z] must be 32 bytes. *)

val encapsulate_768 : encapsulation_key:string -> randomness:string ->
  ((string * string), Mlkem.Mlkem768.error) result
(** Returns [(ciphertext, shared_secret)] using the supplied 32-byte test
    randomness. *)

val decapsulate_768 : expanded_decapsulation_key:string -> ciphertext:string ->
  (string, Mlkem.Mlkem768.error) result
(** Decapsulates an ACVP-format 2400-byte key. *)

val keygen_1024 : d:string -> z:string ->
  ((string * string), Mlkem.Mlkem1024.error) result
val encapsulate_1024 : encapsulation_key:string -> randomness:string ->
  ((string * string), Mlkem.Mlkem1024.error) result
val decapsulate_1024 : expanded_decapsulation_key:string -> ciphertext:string ->
  (string, Mlkem.Mlkem1024.error) result
