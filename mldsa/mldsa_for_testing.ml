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

let sign_mu module_ ~signing_key ~mu ~randomness =
  let module Engine = (val module_ : Mldsa__Mldsa_engine.INTERNAL) in
  match Engine.signing_key_of_octets signing_key with
  | Error error -> Error error
  | Ok key ->
      begin match Engine.sign_mu_for_testing key ~mu ~randomness with
      | Error error -> Error error
      | Ok signature -> Ok (Engine.signature_to_octets signature)
      end

let sign_mu_44 = sign_mu (module Mldsa__Mldsa_engine.Mldsa44)
let sign_mu_65 = sign_mu (module Mldsa__Mldsa_engine.Mldsa65)
let sign_mu_87 = sign_mu (module Mldsa__Mldsa_engine.Mldsa87)

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

let verify_mu module_ ~verification_key ~mu ~signature =
  let module Engine = (val module_ : Mldsa__Mldsa_engine.INTERNAL) in
  match
    Engine.verification_key_of_octets verification_key,
    Engine.signature_of_octets signature
  with
  | Ok key, Ok signature -> Engine.verify_mu_for_testing key ~mu signature
  | Error _, _ | _, Error _ -> false

let verify_mu_44 = verify_mu (module Mldsa__Mldsa_engine.Mldsa44)
let verify_mu_65 = verify_mu (module Mldsa__Mldsa_engine.Mldsa65)
let verify_mu_87 = verify_mu (module Mldsa__Mldsa_engine.Mldsa87)

let use_hint_44 = Mldsa__Mldsa_engine.Mldsa44.use_hint_for_testing
let use_hint_65 = Mldsa__Mldsa_engine.Mldsa65.use_hint_for_testing
let use_hint_87 = Mldsa__Mldsa_engine.Mldsa87.use_hint_for_testing

let u16_le = Mldsa__Mldsa_engine.u16_le
