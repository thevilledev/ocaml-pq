val shake128 : output_length:int -> string -> string
val shake256 : output_length:int -> string -> string
val sha256 : string -> string
val sha512 : string -> string
val hmac_sha256 : string -> string -> string
val hmac_sha512 : string -> string -> string
val mgf1_sha256 : output_length:int -> string -> string
val mgf1_sha512 : output_length:int -> string -> string
