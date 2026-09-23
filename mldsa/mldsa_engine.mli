type error =
  | Invalid_length of { what : string; expected : int; actual : int }
  | Invalid_encoding of string
  | Context_too_long of int
  | Signing_failed

val pp_error : Format.formatter -> error -> unit

val u16_le : int -> string
(** [u16_le nonce] is FIPS 204 IntegerToBytes([nonce], 2). Raises
    [Invalid_argument] unless [0 <= nonce < 2^16]. Exposed for tests. *)

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

(** The operations every ML-DSA parameter set provides.

    Keys and signatures have distinct abstract types per parameter set, so
    values from ML-DSA-44, ML-DSA-65, and ML-DSA-87 cannot be mixed. All
    parsing functions reject inputs of the wrong length and validate the
    algorithm-specific encoding.

    The caller supplies randomness so that this library stays portable across
    Unix, MirageOS unikernels, and [js_of_ocaml]. A [random] callback must
    return exactly the requested number of cryptographically secure random
    bytes; returning any other length raises [Invalid_argument]. *)
module type S = sig
  type nonrec error = error =
    | Invalid_length of { what : string; expected : int; actual : int }
    | Invalid_encoding of string
    | Context_too_long of int
    | Signing_failed
        (** Signing exhausted the FIPS 204 bound of 821 rejection-sampling
            attempts. Reaching this is negligibly unlikely. *)

  val pp_error : Format.formatter -> error -> unit
  (** [pp_error] formats an error for humans. *)

  type signing_key
  type verification_key
  type signature

  val seed_size : int
  (** The size of a key-generation seed: 32 bytes. *)

  val signing_key_size : int
  (** The size of an expanded signing key, in bytes. *)

  val verification_key_size : int
  (** The size of an encoded verification key, in bytes. *)

  val signature_size : int
  (** The size of an encoded signature, in bytes. *)

  val generate :
    random:(int -> string) -> unit -> signing_key * verification_key
  (** [generate ~random ()] creates a key pair from [seed_size] bytes obtained
      from [random]. *)

  val signing_key_of_seed : string -> (signing_key, error) result
  (** [signing_key_of_seed seed] expands a [seed_size]-byte key-generation
      seed. *)

  val signing_key_to_seed : signing_key -> string option
  (** [signing_key_to_seed key] returns the [seed_size]-byte seed [key] was
      generated from, or [None] when [key] was imported with
      {!signing_key_of_octets} and no seed is recoverable. The result is
      secret key material. *)

  val signing_key_of_octets : string -> (signing_key, error) result
  (** [signing_key_of_octets octets] parses the expanded
      [signing_key_size]-byte encoding, checking that the embedded public-key
      hash and [t0] vector are internally consistent. *)

  val signing_key_to_octets : signing_key -> string
  (** [signing_key_to_octets key] returns the expanded encoding. The result is
      secret key material. *)

  val verification_key_of_signing_key : signing_key -> verification_key
  (** [verification_key_of_signing_key key] extracts the public half of a key
      pair. *)

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
  (** [sign ?context ~random key ~message] produces a hedged PureML-DSA
      signature, drawing 32 fresh bytes from [random] for this signature.
      Prefer it over {!sign_deterministic}.

      [context] defaults to [""] and identifies the application's use of the
      signature. It is limited to 255 bytes by FIPS 204, and verification
      must supply the same value. A longer context returns
      [Context_too_long]. *)

  val sign_deterministic :
    ?context:string -> signing_key -> message:string -> (signature, error) result
  (** [sign_deterministic ?context key ~message] signs with the FIPS 204
      deterministic variant, substituting 32 zero bytes for the per-signature
      randomness. The same key, message, and context always yield the same
      signature. Key generation still requires secure randomness. *)

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

  val sign_mu_for_testing :
    signing_key ->
    mu:string ->
    randomness:string ->
    (signature, error) result

  val verify_internal_for_testing :
    verification_key -> formatted_message:string -> signature -> bool

  val verify_mu_for_testing :
    verification_key -> mu:string -> signature -> bool

  val use_hint_for_testing : int -> int -> int
  (** [use_hint_for_testing r h] is FIPS 204 UseHint(h, r): the high bits of
      [r], moved by one when [h = 1]. *)
end

module Make (P : PARAMETERS) : INTERNAL
module Mldsa44 : INTERNAL
module Mldsa65 : INTERNAL
module Mldsa87 : INTERNAL
