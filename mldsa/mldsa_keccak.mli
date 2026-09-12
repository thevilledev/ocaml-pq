(** Internal, one-shot FIPS 202 extendable-output functions. *)

val shake128 : output_length:int -> string -> string
val shake256 : output_length:int -> string -> string
