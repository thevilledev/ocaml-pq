(** Raw-message hooks for FIPS 205 ACVP tests. Not for production use. *)

val sign_internal_sha2_128s : signing_key:string -> formatted_message:string -> randomness:string -> (string, Slhdsa.Sha2_128s.error) result
val sign_internal_sha2_128f : signing_key:string -> formatted_message:string -> randomness:string -> (string, Slhdsa.Sha2_128f.error) result
val sign_internal_sha2_192s : signing_key:string -> formatted_message:string -> randomness:string -> (string, Slhdsa.Sha2_192s.error) result
val sign_internal_sha2_192f : signing_key:string -> formatted_message:string -> randomness:string -> (string, Slhdsa.Sha2_192f.error) result
val sign_internal_sha2_256s : signing_key:string -> formatted_message:string -> randomness:string -> (string, Slhdsa.Sha2_256s.error) result
val sign_internal_sha2_256f : signing_key:string -> formatted_message:string -> randomness:string -> (string, Slhdsa.Sha2_256f.error) result
val sign_internal_shake_128s : signing_key:string -> formatted_message:string -> randomness:string -> (string, Slhdsa.Shake_128s.error) result
val sign_internal_shake_128f : signing_key:string -> formatted_message:string -> randomness:string -> (string, Slhdsa.Shake_128f.error) result
val sign_internal_shake_192s : signing_key:string -> formatted_message:string -> randomness:string -> (string, Slhdsa.Shake_192s.error) result
val sign_internal_shake_192f : signing_key:string -> formatted_message:string -> randomness:string -> (string, Slhdsa.Shake_192f.error) result
val sign_internal_shake_256s : signing_key:string -> formatted_message:string -> randomness:string -> (string, Slhdsa.Shake_256s.error) result
val sign_internal_shake_256f : signing_key:string -> formatted_message:string -> randomness:string -> (string, Slhdsa.Shake_256f.error) result

val verify_internal_sha2_128s : verification_key:string -> formatted_message:string -> signature:string -> bool
val verify_internal_sha2_128f : verification_key:string -> formatted_message:string -> signature:string -> bool
val verify_internal_sha2_192s : verification_key:string -> formatted_message:string -> signature:string -> bool
val verify_internal_sha2_192f : verification_key:string -> formatted_message:string -> signature:string -> bool
val verify_internal_sha2_256s : verification_key:string -> formatted_message:string -> signature:string -> bool
val verify_internal_sha2_256f : verification_key:string -> formatted_message:string -> signature:string -> bool
val verify_internal_shake_128s : verification_key:string -> formatted_message:string -> signature:string -> bool
val verify_internal_shake_128f : verification_key:string -> formatted_message:string -> signature:string -> bool
val verify_internal_shake_192s : verification_key:string -> formatted_message:string -> signature:string -> bool
val verify_internal_shake_192f : verification_key:string -> formatted_message:string -> signature:string -> bool
val verify_internal_shake_256s : verification_key:string -> formatted_message:string -> signature:string -> bool
val verify_internal_shake_256f : verification_key:string -> formatted_message:string -> signature:string -> bool

val sha256 : string -> string
val sha512 : string -> string
val hmac_sha256 : string -> string -> string
val hmac_sha512 : string -> string -> string
val shake256 : output_length:int -> string -> string
val mgf1_sha256 : output_length:int -> string -> string
val mgf1_sha512 : output_length:int -> string -> string
(** RFC 8017 MGF1. Raises [Invalid_argument] for a negative length or a mask
    longer than 2^32 hash outputs. *)

val fors_tree_sha2_128f :
  sk_seed:string -> pk_seed:string -> leaf_index:int -> string * string
(** The root and the authentication path of [leaf_index] in the first FORS
    tree of SLH-DSA-SHA2-128f (a = 6). Raises [Invalid_argument] for a leaf
    index of 64 or more; [-1] returns the root alone. *)
