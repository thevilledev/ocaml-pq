(** Deterministic and precomputed-message hooks for FIPS 204 ACVP and
    Wycheproof tests. Not for production use. *)

val sign_internal_44 :
  signing_key:string ->
  formatted_message:string ->
  randomness:string ->
  (string, Mldsa.Mldsa44.error) result

val sign_internal_65 :
  signing_key:string ->
  formatted_message:string ->
  randomness:string ->
  (string, Mldsa.Mldsa65.error) result

val sign_internal_87 :
  signing_key:string ->
  formatted_message:string ->
  randomness:string ->
  (string, Mldsa.Mldsa87.error) result

val sign_mu_44 :
  signing_key:string ->
  mu:string ->
  randomness:string ->
  (string, Mldsa.Mldsa44.error) result

val sign_mu_65 :
  signing_key:string ->
  mu:string ->
  randomness:string ->
  (string, Mldsa.Mldsa65.error) result

val sign_mu_87 :
  signing_key:string ->
  mu:string ->
  randomness:string ->
  (string, Mldsa.Mldsa87.error) result

val verify_internal_44 :
  verification_key:string ->
  formatted_message:string ->
  signature:string ->
  bool

val verify_internal_65 :
  verification_key:string ->
  formatted_message:string ->
  signature:string ->
  bool

val verify_internal_87 :
  verification_key:string ->
  formatted_message:string ->
  signature:string ->
  bool

val verify_mu_44 :
  verification_key:string ->
  mu:string ->
  signature:string ->
  bool

val verify_mu_65 :
  verification_key:string ->
  mu:string ->
  signature:string ->
  bool

val verify_mu_87 :
  verification_key:string ->
  mu:string ->
  signature:string ->
  bool

val use_hint_44 : int -> int -> int
(** [use_hint_44 r h] is FIPS 204 UseHint(h, r) for ML-DSA-44: the high bits
    of [r], moved by one when [h = 1]. *)

val use_hint_65 : int -> int -> int
val use_hint_87 : int -> int -> int

val u16_le : int -> string
(** The nonce encoding of ExpandA, ExpandS and ExpandMask: IntegerToBytes(n,
    2). Raises [Invalid_argument] unless [0 <= n < 2^16]. *)
