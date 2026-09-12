module M512 = Mlkem__Mlkem_engine.Mlkem512
module M768 = Mlkem__Mlkem_engine.Mlkem768
module M1024 = Mlkem__Mlkem_engine.Mlkem1024
module type ENGINE = Mlkem__Mlkem_engine.S

let sha3_256 = Mlkem__Keccak.sha3_256
let sha3_512 = Mlkem__Keccak.sha3_512
let shake128 = Mlkem__Keccak.shake128
let shake256 = Mlkem__Keccak.shake256

let keygen (module M : ENGINE) ~d ~z =
  match M.keygen_internal ~d ~z with
  | Error _ as e -> e
  | Ok dk ->
      let ek = M.encapsulation_key_of_decapsulation_key dk in
      Ok (M.decapsulation_key_to_expanded dk, M.encapsulation_key_to_octets ek)

let encapsulate (module M : ENGINE) ~encapsulation_key ~randomness =
  match M.encapsulation_key_of_octets encapsulation_key with
  | Error _ as e -> e
  | Ok ek ->
      match M.encapsulate_internal ek ~randomness with
      | Error _ as e -> e
      | Ok (ct, ss) -> Ok (M.ciphertext_to_octets ct, M.shared_secret_to_octets ss)

let decapsulate (module M : ENGINE) ~expanded_decapsulation_key ~ciphertext =
  match M.decapsulation_key_of_expanded expanded_decapsulation_key with
  | Error _ as e -> e
  | Ok dk ->
      match M.ciphertext_of_octets ciphertext with
      | Error _ as e -> e
      | Ok ct -> Ok (M.shared_secret_to_octets (M.decapsulate dk ct))

let keygen_512 = keygen (module M512)
let encapsulate_512 = encapsulate (module M512)
let decapsulate_512 = decapsulate (module M512)
let keygen_768 = keygen (module M768)
let encapsulate_768 = encapsulate (module M768)
let decapsulate_768 = decapsulate (module M768)
let keygen_1024 = keygen (module M1024)
let encapsulate_1024 = encapsulate (module M1024)
let decapsulate_1024 = decapsulate (module M1024)
