let sign module_ ~signing_key ~formatted_message ~randomness =
  let module Engine = (val module_ : Slhdsa__Slhdsa_engine.INTERNAL) in
  match Engine.signing_key_of_octets signing_key with
  | Error error -> Error error
  | Ok key -> begin
      match Engine.sign_internal_for_testing key ~formatted_message ~randomness with
      | Error error -> Error error
      | Ok signature -> Ok (Engine.signature_to_octets signature)
    end

let verify module_ ~verification_key ~formatted_message ~signature =
  let module Engine = (val module_ : Slhdsa__Slhdsa_engine.INTERNAL) in
  match
    Engine.verification_key_of_octets verification_key,
    Engine.signature_of_octets signature
  with
  | Ok key, Ok signature ->
      Engine.verify_internal_for_testing key ~formatted_message signature
  | Error _, _ | _, Error _ -> false

let sign_internal_sha2_128s = sign (module Slhdsa__Slhdsa_engine.Sha2_128s)
let sign_internal_sha2_128f = sign (module Slhdsa__Slhdsa_engine.Sha2_128f)
let sign_internal_sha2_192s = sign (module Slhdsa__Slhdsa_engine.Sha2_192s)
let sign_internal_sha2_192f = sign (module Slhdsa__Slhdsa_engine.Sha2_192f)
let sign_internal_sha2_256s = sign (module Slhdsa__Slhdsa_engine.Sha2_256s)
let sign_internal_sha2_256f = sign (module Slhdsa__Slhdsa_engine.Sha2_256f)
let sign_internal_shake_128s = sign (module Slhdsa__Slhdsa_engine.Shake_128s)
let sign_internal_shake_128f = sign (module Slhdsa__Slhdsa_engine.Shake_128f)
let sign_internal_shake_192s = sign (module Slhdsa__Slhdsa_engine.Shake_192s)
let sign_internal_shake_192f = sign (module Slhdsa__Slhdsa_engine.Shake_192f)
let sign_internal_shake_256s = sign (module Slhdsa__Slhdsa_engine.Shake_256s)
let sign_internal_shake_256f = sign (module Slhdsa__Slhdsa_engine.Shake_256f)

let verify_internal_sha2_128s = verify (module Slhdsa__Slhdsa_engine.Sha2_128s)
let verify_internal_sha2_128f = verify (module Slhdsa__Slhdsa_engine.Sha2_128f)
let verify_internal_sha2_192s = verify (module Slhdsa__Slhdsa_engine.Sha2_192s)
let verify_internal_sha2_192f = verify (module Slhdsa__Slhdsa_engine.Sha2_192f)
let verify_internal_sha2_256s = verify (module Slhdsa__Slhdsa_engine.Sha2_256s)
let verify_internal_sha2_256f = verify (module Slhdsa__Slhdsa_engine.Sha2_256f)
let verify_internal_shake_128s = verify (module Slhdsa__Slhdsa_engine.Shake_128s)
let verify_internal_shake_128f = verify (module Slhdsa__Slhdsa_engine.Shake_128f)
let verify_internal_shake_192s = verify (module Slhdsa__Slhdsa_engine.Shake_192s)
let verify_internal_shake_192f = verify (module Slhdsa__Slhdsa_engine.Shake_192f)
let verify_internal_shake_256s = verify (module Slhdsa__Slhdsa_engine.Shake_256s)
let verify_internal_shake_256f = verify (module Slhdsa__Slhdsa_engine.Shake_256f)

let sha256 = Slhdsa__Slhdsa_hash.sha256
let sha512 = Slhdsa__Slhdsa_hash.sha512
let hmac_sha256 = Slhdsa__Slhdsa_hash.hmac_sha256
let hmac_sha512 = Slhdsa__Slhdsa_hash.hmac_sha512
let shake256 = Slhdsa__Slhdsa_hash.shake256
