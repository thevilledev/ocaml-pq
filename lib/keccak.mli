(** Internal, one-shot FIPS 202 hash and extendable-output functions. *)

val sha3_256 : string -> string
val sha3_512 : string -> string
val shake128 : output_length:int -> string -> string
val shake256 : output_length:int -> string -> string
