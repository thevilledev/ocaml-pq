module Engine = Mlkem_engine.Mlkem768
include Engine

let decapsulation_key_to_seed dk =
  match Engine.decapsulation_key_to_seed dk with
  | Some seed -> seed
  | None -> assert false

let require_random random length =
  let value = random length in
  if String.length value <> length then
    invalid_arg
      (Format.sprintf "Mlkem768: randomness callback returned %d bytes, expected %d"
         (String.length value) length);
  value

let generate ~random () =
  let seed = require_random random seed_size in
  match decapsulation_key_of_seed seed with
  | Error error -> invalid_arg (Format.asprintf "Mlkem768.generate: %a" pp_error error)
  | Ok dk -> dk, encapsulation_key_of_decapsulation_key dk

let encapsulate ~random ek =
  let randomness = require_random random 32 in
  match encapsulate_internal ek ~randomness with
  | Error error -> invalid_arg (Format.asprintf "Mlkem768.encapsulate: %a" pp_error error)
  | Ok result -> result
