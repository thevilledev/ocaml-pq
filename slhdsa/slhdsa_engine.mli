type error =
  | Invalid_length of { what : string; expected : int; actual : int }
  | Invalid_encoding of string
  | Context_too_long of int

val pp_error : Format.formatter -> error -> unit

module type PARAMETERS = sig
  val name : string
  val hash : [ `Sha2 | `Shake ]
  val n : int
  val h : int
  val d : int
  val a : int
  val k : int
  val m : int
end

(** The operations every SLH-DSA parameter set provides.

    Keys and signatures have distinct abstract types per parameter set, so
    values from different parameter sets cannot be mixed. All parsing
    functions reject inputs of the wrong length.

    Sizes are given in terms of the security parameter [n], which is 16 bytes
    at security level 128, 24 at level 192, and 32 at level 256. The [s]
    variants produce smaller signatures and sign more slowly; the [f]
    variants sign faster and produce larger signatures.

    The caller supplies randomness so that this library stays portable across
    Unix, MirageOS unikernels, and [js_of_ocaml]. A [random] callback must
    return exactly the requested number of cryptographically secure random
    bytes; returning any other length raises [Invalid_argument]. *)
module type S = sig
  type nonrec error = error =
    | Invalid_length of { what : string; expected : int; actual : int }
    | Invalid_encoding of string
    | Context_too_long of int

  val pp_error : Format.formatter -> error -> unit
  (** [pp_error] formats an error for humans. *)

  type signing_key
  type verification_key
  type signature

  val seed_size : int
  (** The size of a key-generation seed: [3 * n] bytes. *)

  val signing_key_size : int
  (** The size of an encoded signing key: [4 * n] bytes. *)

  val verification_key_size : int
  (** The size of an encoded verification key: [2 * n] bytes. *)

  val signature_size : int
  (** The size of an encoded signature, in bytes. *)

  val generate :
    random:(int -> string) -> unit -> signing_key * verification_key
  (** [generate ~random ()] creates a key pair from [seed_size] bytes obtained
      from [random]. It builds the top-level Merkle tree, which is markedly
      slower for the [s] parameter sets because their trees are taller. *)

  val signing_key_of_seed : string -> (signing_key, error) result
  (** [signing_key_of_seed seed] expands a [seed_size]-byte key-generation
      seed. *)

  val signing_key_to_seed : signing_key -> string option
  (** [signing_key_to_seed key] returns the [seed_size]-byte seed [key] was
      generated from, or [None] when [key] was imported with
      {!signing_key_of_octets} and no seed is recoverable. The result is
      secret key material. *)

  val signing_key_of_octets : string -> (signing_key, error) result
  (** [signing_key_of_octets octets] parses the [signing_key_size]-byte
      encoding. It recomputes the top-level Merkle root and returns
      [Invalid_encoding] when the embedded root disagrees, so importing a key
      costs about as much as generating one. *)

  val signing_key_to_octets : signing_key -> string
  (** [signing_key_to_octets key] returns the encoded key. The result is
      secret key material. *)

  val verification_key_of_signing_key : signing_key -> verification_key
  (** [verification_key_of_signing_key key] extracts the public half of a key
      pair. *)

  val verification_key_of_octets : string -> (verification_key, error) result
  (** [verification_key_of_octets octets] checks the length only; a
      verification key carries nothing that can be validated on its own. *)

  val verification_key_to_octets : verification_key -> string

  val signature_of_octets : string -> (signature, error) result
  val signature_to_octets : signature -> string

  val sign :
    ?context:string ->
    random:(int -> string) ->
    signing_key ->
    message:string ->
    (signature, error) result
  (** [sign ?context ~random key ~message] produces a hedged PureSLH-DSA
      signature, drawing [n] fresh bytes from [random] as the randomizer for
      this signature. Prefer it over {!sign_deterministic}.

      [context] defaults to [""] and identifies the application's use of the
      signature. It is limited to 255 bytes by FIPS 205, and verification
      must supply the same value. A longer context returns
      [Context_too_long]. *)

  val sign_deterministic :
    ?context:string -> signing_key -> message:string -> (signature, error) result
  (** [sign_deterministic ?context key ~message] signs with the FIPS 205
      deterministic variant, using the public key seed as the randomizer
      instead of fresh entropy. The same key, message, and context always
      yield the same signature. Key generation still requires secure
      randomness. *)

  val verify :
    ?context:string ->
    verification_key ->
    message:string ->
    signature ->
    bool
  (** [verify ?context key ~message signature] returns [true] only when
      [signature] is valid for [message] under [key] and the same [context]
      used when signing. *)
end

module type INTERNAL = sig
  include S

  val sign_internal_for_testing :
    signing_key ->
    formatted_message:string ->
    randomness:string ->
    (signature, error) result

  val verify_internal_for_testing :
    verification_key -> formatted_message:string -> signature -> bool

  val fors_tree_for_testing :
    sk_seed:string -> pk_seed:string -> leaf_index:int -> string * string
  (** [fors_tree_for_testing ~sk_seed ~pk_seed ~leaf_index] runs the tree
      hash over the first FORS tree of keypair 0 and returns its root and the
      authentication path of [leaf_index]. Raises [Invalid_argument] for a
      leaf index of [2^a] or more; [-1] returns the root alone. *)
end

module Make (P : PARAMETERS) : INTERNAL

module Sha2_128s : INTERNAL
module Sha2_128f : INTERNAL
module Sha2_192s : INTERNAL
module Sha2_192f : INTERNAL
module Sha2_256s : INTERNAL
module Sha2_256f : INTERNAL
module Shake_128s : INTERNAL
module Shake_128f : INTERNAL
module Shake_192s : INTERNAL
module Shake_192f : INTERNAL
module Shake_256s : INTERNAL
module Shake_256f : INTERNAL
