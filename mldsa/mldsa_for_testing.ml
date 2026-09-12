let sign module_ ~signing_key ~formatted_message ~randomness =
  let module Engine = (val module_ : Mldsa__Mldsa_engine.INTERNAL) in
  match Engine.signing_key_of_octets signing_key with
  | Error error -> Error error
  | Ok key -> begin
      match
        Engine.sign_internal_for_testing key ~formatted_message ~randomness
      with
      | Error error -> Error error
      | Ok signature -> Ok (Engine.signature_to_octets signature)
    end

let sign_internal_44 =
  sign (module Mldsa__Mldsa_engine.Mldsa44)

let sign_internal_65 =
  sign (module Mldsa__Mldsa_engine.Mldsa65)

let sign_internal_87 =
  sign (module Mldsa__Mldsa_engine.Mldsa87)

let verify module_ ~verification_key ~formatted_message ~signature =
  let module Engine = (val module_ : Mldsa__Mldsa_engine.INTERNAL) in
  match
    Engine.verification_key_of_octets verification_key,
    Engine.signature_of_octets signature
  with
  | Ok key, Ok signature ->
      Engine.verify_internal_for_testing key ~formatted_message signature
  | Error _, _ | _, Error _ -> false

let verify_internal_44 =
  verify (module Mldsa__Mldsa_engine.Mldsa44)

let verify_internal_65 =
  verify (module Mldsa__Mldsa_engine.Mldsa65)

let verify_internal_87 =
  verify (module Mldsa__Mldsa_engine.Mldsa87)
