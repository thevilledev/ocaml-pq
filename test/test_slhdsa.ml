module type VARIANT = sig
  type error
  type signing_key
  type verification_key
  type signature

  val seed_size : int
  val signing_key_size : int
  val verification_key_size : int
  val signature_size : int
  val signing_key_of_seed : string -> (signing_key, error) result
  val signing_key_to_seed : signing_key -> string option
  val signing_key_of_octets : string -> (signing_key, error) result
  val signing_key_to_octets : signing_key -> string
  val verification_key_of_signing_key : signing_key -> verification_key
  val verification_key_of_octets : string -> (verification_key, error) result
  val verification_key_to_octets : verification_key -> string
  val signature_of_octets : string -> (signature, error) result
  val signature_to_octets : signature -> string
  val sign_deterministic : ?context:string -> signing_key -> message:string -> (signature, error) result
  val verify : ?context:string -> verification_key -> message:string -> signature -> bool
end

let variants =
  [
    "SLH-DSA-SHA2-128s", (module Slhdsa.Sha2_128s : VARIANT);
    "SLH-DSA-SHA2-128f", (module Slhdsa.Sha2_128f : VARIANT);
    "SLH-DSA-SHA2-192s", (module Slhdsa.Sha2_192s : VARIANT);
    "SLH-DSA-SHA2-192f", (module Slhdsa.Sha2_192f : VARIANT);
    "SLH-DSA-SHA2-256s", (module Slhdsa.Sha2_256s : VARIANT);
    "SLH-DSA-SHA2-256f", (module Slhdsa.Sha2_256f : VARIANT);
    "SLH-DSA-SHAKE-128s", (module Slhdsa.Shake_128s : VARIANT);
    "SLH-DSA-SHAKE-128f", (module Slhdsa.Shake_128f : VARIANT);
    "SLH-DSA-SHAKE-192s", (module Slhdsa.Shake_192s : VARIANT);
    "SLH-DSA-SHAKE-192f", (module Slhdsa.Shake_192f : VARIANT);
    "SLH-DSA-SHAKE-256s", (module Slhdsa.Shake_256s : VARIANT);
    "SLH-DSA-SHAKE-256f", (module Slhdsa.Shake_256f : VARIANT);
  ]

let hex_value = function
  | '0' .. '9' as value -> Char.code value - Char.code '0'
  | 'a' .. 'f' as value -> Char.code value - Char.code 'a' + 10
  | 'A' .. 'F' as value -> Char.code value - Char.code 'A' + 10
  | _ -> invalid_arg "invalid hexadecimal test vector"

let decode_hex input =
  if String.length input mod 2 <> 0 then invalid_arg "odd hexadecimal test vector";
  String.init (String.length input / 2) (fun index ->
      Char.unsafe_chr
        ((hex_value input.[2 * index] lsl 4)
         lor hex_value input.[(2 * index) + 1]))

let vector_path name =
  let local = Filename.concat "slhdsa_vectors" name in
  if Sys.file_exists local then local else Filename.concat "test/slhdsa_vectors" name

let read_keygen_vectors () =
  let channel = open_in (vector_path "keygen.txt") in
  let rec loop result =
    match input_line channel with
    | line ->
        if line = "" || line.[0] = '#' then loop result
        else begin
          match String.split_on_char '\t' line with
          | [ name; seed; secret; public ] ->
              loop ((name, decode_hex seed, decode_hex secret, decode_hex public) :: result)
          | _ -> failwith "invalid SLH-DSA key-generation vector"
        end
    | exception End_of_file -> close_in channel; List.rev result
  in
  loop []

let read_siggen_vectors () =
  let channel = open_in (vector_path "siggen.txt") in
  let rec loop result =
    match input_line channel with
    | line -> begin
        match String.split_on_char '\t' line with
        | [ name; secret; message; context; signature ] ->
            loop
              ((name, decode_hex secret, decode_hex message, decode_hex context,
                decode_hex signature)
               :: result)
        | _ -> failwith "invalid SLH-DSA signature-generation vector"
      end
    | exception End_of_file -> close_in channel; List.rev result
  in
  loop []

let result_ok = function
  | Ok value -> value
  | Error _ -> Alcotest.fail "operation unexpectedly returned an error"

let variant name =
  match List.assoc_opt name variants with
  | Some variant -> variant
  | None -> failwith ("unknown SLH-DSA variant " ^ name)

let test_keygen () =
  List.iter
    (fun (name, seed, expected_secret, expected_public) ->
      let module M = (val variant name : VARIANT) in
      let signing_key = M.signing_key_of_seed seed |> result_ok in
      let verification_key = M.verification_key_of_signing_key signing_key in
      Alcotest.(check string) (name ^ " signing key") expected_secret
        (M.signing_key_to_octets signing_key);
      Alcotest.(check string) (name ^ " verification key") expected_public
        (M.verification_key_to_octets verification_key);
      Alcotest.(check (option string)) (name ^ " seed") (Some seed)
        (M.signing_key_to_seed signing_key))
    (read_keygen_vectors ())

let mutate value =
  let result = Bytes.of_string value in
  Bytes.set result 0 (Char.chr (Char.code (Bytes.get result 0) lxor 1));
  Bytes.unsafe_to_string result

let check_bytes name expected actual =
  if expected <> actual then begin
    let limit = min (String.length expected) (String.length actual) in
    let rec first index =
      if index = limit then index
      else if expected.[index] <> actual.[index] then index
      else first (index + 1)
    in
    let index = first 0 in
    if index = limit then
      Alcotest.failf "%s lengths differ: expected %d, got %d" name
        (String.length expected) (String.length actual)
    else
      Alcotest.failf "%s differs at byte %d: expected %02x, got %02x" name
        index (Char.code expected.[index]) (Char.code actual.[index])
  end

let test_siggen () =
  List.iter
    (fun (name, expected_secret, message, context, expected_signature) ->
      let module M = (val variant name : VARIANT) in
      let seed = String.sub expected_secret 0 M.seed_size in
      let signing_key = M.signing_key_of_seed seed |> result_ok in
      Alcotest.(check int) (name ^ " signing-key size") M.signing_key_size
        (String.length expected_secret);
      Alcotest.(check int) (name ^ " verification-key size")
        M.verification_key_size (2 * (M.seed_size / 3));
      Alcotest.(check int) (name ^ " signature size") M.signature_size
        (String.length expected_signature);
      Alcotest.(check string) (name ^ " vector signing key") expected_secret
        (M.signing_key_to_octets signing_key);
      let imported_signing_key =
        M.signing_key_of_octets expected_secret |> result_ok
      in
      Alcotest.(check (option string)) (name ^ " expanded key has no seed")
        None (M.signing_key_to_seed imported_signing_key);
      let verification_key = M.verification_key_of_signing_key signing_key in
      let signature =
        M.sign_deterministic ~context signing_key ~message |> result_ok
      in
      check_bytes (name ^ " deterministic signature") expected_signature
        (M.signature_to_octets signature);
      let imported_signature =
        M.signature_of_octets expected_signature |> result_ok
      in
      Alcotest.(check bool) (name ^ " verifies") true
        (M.verify ~context verification_key ~message imported_signature);
      let bad_signature =
        M.signature_of_octets (mutate expected_signature) |> result_ok
      in
      Alcotest.(check bool) (name ^ " rejects corruption") false
        (M.verify ~context verification_key ~message bad_signature);
      let encoded_public = M.verification_key_to_octets verification_key in
      let imported_public = M.verification_key_of_octets encoded_public |> result_ok in
      Alcotest.(check bool) (name ^ " imported key verifies") true
        (M.verify ~context imported_public ~message imported_signature))
    (read_siggen_vectors ())

let test_decoding () =
  let module M = Slhdsa.Sha2_128f in
  let bad length decode =
    match decode (String.make length '\000') with
    | Error _ -> ()
    | Ok _ -> Alcotest.fail "malformed length was accepted"
  in
  bad (M.signing_key_size - 1) M.signing_key_of_octets;
  bad (M.verification_key_size + 1) M.verification_key_of_octets;
  bad (M.signature_size - 1) M.signature_of_octets

let () =
  Alcotest.run "SLH-DSA"
    [
      ( "NIST ACVP",
        [
          Alcotest.test_case "key generation" `Slow test_keygen;
          Alcotest.test_case "signature generation" `Slow test_siggen;
        ] );
      "decoding", [ Alcotest.test_case "length checks" `Quick test_decoding ];
    ]
