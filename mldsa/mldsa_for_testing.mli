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
