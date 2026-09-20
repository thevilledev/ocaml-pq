let deterministic_random =
  let counter = ref 0 in
  fun length ->
    let start = !counter in
    counter := start + length;
    String.init length (fun i -> Char.chr ((start + i) land 0xff))

let test_512 () =
  let module M = Mlkem.Mlkem512 in
  let dk, ek = M.generate ~random:deterministic_random () in
  let ciphertext, sender_secret = M.encapsulate ~random:deterministic_random ek in
  let receiver_secret = M.decapsulate dk ciphertext in
  if M.shared_secret_to_octets sender_secret <>
     M.shared_secret_to_octets receiver_secret
  then failwith "ML-KEM-512 js_of_ocaml round trip failed"

let test_768 () =
  let module M = Mlkem.Mlkem768 in
  let dk, ek = M.generate ~random:deterministic_random () in
  let ciphertext, sender_secret = M.encapsulate ~random:deterministic_random ek in
  let receiver_secret = M.decapsulate dk ciphertext in
  if M.shared_secret_to_octets sender_secret <>
     M.shared_secret_to_octets receiver_secret
  then failwith "ML-KEM-768 js_of_ocaml round trip failed"

let test_1024 () =
  let module M = Mlkem.Mlkem1024 in
  let dk, ek = M.generate ~random:deterministic_random () in
  let ciphertext, sender_secret = M.encapsulate ~random:deterministic_random ek in
  let receiver_secret = M.decapsulate dk ciphertext in
  if M.shared_secret_to_octets sender_secret <>
     M.shared_secret_to_octets receiver_secret
  then failwith "ML-KEM-1024 js_of_ocaml round trip failed"

(* A round trip cannot tell a Keccak that is wrong on both sides from a right
   one, so the public SHAKE256 is held to known answers: the FIPS 202 example
   for the empty message, and an input and an output of several blocks. *)
let test_shake256 () =
  let hex value =
    String.concat ""
      (List.map (fun c -> Printf.sprintf "%02x" (Char.code c))
         (List.of_seq (String.to_seq value)))
  in
  let input = String.init 273 (fun i -> Char.chr (i mod 251)) in
  let long = Mlkem.Fips202.shake256 ~output_length:300 input in
  if hex (Mlkem.Fips202.shake256 ~output_length:32 "") <>
     "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f"
     || hex (String.sub long 268 32) <>
        "a11afbe4536702607493aa49091d5384f97c81ba4bb7b08a63fd2565c11891bb"
  then failwith "SHAKE256 js_of_ocaml known answer failed"

module type SIGNATURE = sig
  type error
  type signing_key
  type verification_key
  type signature

  val generate :
    random:(int -> string) -> unit -> signing_key * verification_key

  val sign :
    ?context:string ->
    random:(int -> string) ->
    signing_key ->
    message:string ->
    (signature, error) result

  val verify :
    ?context:string ->
    verification_key ->
    message:string ->
    signature ->
    bool
end

let test_signature name (module M : SIGNATURE) =
  let signing_key, verification_key = M.generate ~random:deterministic_random () in
  let message = "js_of_ocaml post-quantum signature" in
  match
    M.sign ~context:"ocaml-pq" ~random:deterministic_random signing_key ~message
  with
  | Error _ -> failwith (name ^ " js_of_ocaml signing failed")
  | Ok signature ->
      if not (M.verify ~context:"ocaml-pq" verification_key ~message signature) then
        failwith (name ^ " js_of_ocaml verification failed")

let () =
  test_shake256 ();
  test_512 ();
  test_768 ();
  test_1024 ();
  test_signature "ML-DSA-44" (module Mldsa.Mldsa44);
  test_signature "ML-DSA-65" (module Mldsa.Mldsa65);
  test_signature "ML-DSA-87" (module Mldsa.Mldsa87);
  test_signature "SLH-DSA-SHA2-128f" (module Slhdsa.Sha2_128f);
  test_signature "SLH-DSA-SHAKE-128f" (module Slhdsa.Shake_128f);
  print_endline
    "ML-KEM, ML-DSA, and SHA2/SHAKE SLH-DSA js_of_ocaml round trips passed"
