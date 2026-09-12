module type VARIANT = sig
  type error
  type signing_key
  type verification_key
  type signature

  val seed_size : int
  val signing_key_size : int
  val verification_key_size : int
  val signature_size : int
  val generate : random:(int -> string) -> unit -> signing_key * verification_key
  val signing_key_of_seed : string -> (signing_key, error) result
  val signing_key_to_seed : signing_key -> string option
  val signing_key_of_octets : string -> (signing_key, error) result
  val signing_key_to_octets : signing_key -> string
  val verification_key_of_signing_key : signing_key -> verification_key
  val verification_key_of_octets : string -> (verification_key, error) result
  val verification_key_to_octets : verification_key -> string
  val signature_of_octets : string -> (signature, error) result
  val signature_to_octets : signature -> string
  val sign : ?context:string -> random:(int -> string) -> signing_key -> message:string -> (signature, error) result
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

let read_rows name parse =
  let channel = open_in (vector_path name) in
  let rec loop line_number result =
    match input_line channel with
    | line ->
        let row =
          match parse (String.split_on_char '\t' line) with
          | Some row -> row
          | None -> failwith (Printf.sprintf "%s:%d: invalid vector" name line_number)
        in
        loop (line_number + 1) (row :: result)
    | exception End_of_file -> List.rev result
  in
  match loop 1 [] with
  | rows -> close_in channel; rows
  | exception exn -> close_in_noerr channel; raise exn

let read_extra_siggen_vectors () =
  let rows = read_rows "siggen-extra.txt" (function
    | [ name; id; mode; secret; message; context; randomness; signature ]
      when mode = "deterministic" || mode = "hedged" ->
        Some (name, id, mode, decode_hex secret, decode_hex message,
              decode_hex context, decode_hex randomness, decode_hex signature)
    | _ -> None)
  in
  Alcotest.(check int) "additional signing vector count" 24 (List.length rows);
  rows

let read_sigver_vectors () =
  let rows = read_rows "sigver.txt" (function
    | [ name; id; public; message; context; signature; result ]
      when result = "valid" || result = "invalid" ->
        Some (name, id, decode_hex public, decode_hex message, decode_hex context,
              decode_hex signature, result = "valid")
    | _ -> None)
  in
  Alcotest.(check int) "verification vector count" 168 (List.length rows);
  Alcotest.(check int) "valid verification vector count" 24
    (List.length (List.filter (fun (_, _, _, _, _, _, valid) -> valid) rows));
  rows

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
        (M.signing_key_to_seed signing_key);
      let calls = ref [] in
      let generated, public = M.generate ~random:(fun length ->
        calls := length :: !calls;
        seed) ()
      in
      Alcotest.(check (list int)) (name ^ " key-generation randomness")
        [ M.seed_size ] !calls;
      Alcotest.(check string) (name ^ " generated signing key") expected_secret
        (M.signing_key_to_octets generated);
      Alcotest.(check string) (name ^ " generated verification key") expected_public
        (M.verification_key_to_octets public))
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

let expect_error label = function
  | Error _ -> ()
  | Ok _ -> Alcotest.fail label

let expect_invalid_argument label operation =
  match operation () with
  | exception Invalid_argument _ -> ()
  | _ -> Alcotest.fail label

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
      Alcotest.(check bool) (name ^ " rejects wrong message") false
        (M.verify ~context verification_key ~message:(message ^ "\000") imported_signature);
      let wrong_context = if context = "" then "x" else mutate context in
      Alcotest.(check bool) (name ^ " rejects wrong context") false
        (M.verify ~context:wrong_context verification_key ~message imported_signature);
      let long_context = String.make 256 'x' in
      expect_error (name ^ " accepted a 256-byte signing context")
        (M.sign_deterministic ~context:long_context signing_key ~message);
      expect_error (name ^ " accepted a 256-byte hedged signing context")
        (M.sign ~context:long_context
           ~random:(fun _ -> Alcotest.fail "invalid context consumed randomness")
           signing_key ~message);
      Alcotest.(check bool) (name ^ " rejects long verification context") false
        (M.verify ~context:long_context verification_key ~message imported_signature);
      let n = M.seed_size / 3 in
      List.iter (fun length ->
        expect_invalid_argument (name ^ " accepted wrong signing randomness length")
          (fun () -> M.sign ~random:(fun requested ->
            Alcotest.(check int) "requested signing randomness" n requested;
            String.make length '\000') signing_key ~message))
        [ 0; n - 1; n + 1 ];
      let bad_signature =
        M.signature_of_octets (mutate expected_signature) |> result_ok
      in
      Alcotest.(check bool) (name ^ " rejects corruption") false
        (M.verify ~context verification_key ~message bad_signature);
      let encoded_public = M.verification_key_to_octets verification_key in
      let imported_public = M.verification_key_of_octets encoded_public |> result_ok in
      Alcotest.(check bool) (name ^ " imported key verifies") true
        (M.verify ~context imported_public ~message imported_signature);
      let wrong_public =
        M.verification_key_of_octets (mutate encoded_public) |> result_ok
      in
      Alcotest.(check bool) (name ^ " rejects wrong verification key") false
        (M.verify ~context wrong_public ~message imported_signature);
      let inconsistent_secret = Bytes.of_string expected_secret in
      let last = Bytes.length inconsistent_secret - 1 in
      Bytes.set inconsistent_secret last
        (Char.chr (Char.code (Bytes.get inconsistent_secret last) lxor 1));
      expect_error (name ^ " accepted an inconsistent signing key")
        (M.signing_key_of_octets (Bytes.to_string inconsistent_secret)))
    (read_siggen_vectors ())

let test_extra_siggen name =
  let rows = read_extra_siggen_vectors ()
    |> List.filter (fun (parameter, _, _, _, _, _, _, _) -> parameter = name)
  in
  Alcotest.(check int) (name ^ " additional signing vectors") 2 (List.length rows);
  List.iter (fun (_, id, mode, secret, message, context, randomness, expected) ->
    let module M = (val variant name : VARIANT) in
    let label = name ^ " ACVP " ^ id ^ " " ^ mode in
    let key = M.signing_key_of_octets secret |> result_ok in
    let public = M.verification_key_of_signing_key key in
    let signature =
      if mode = "deterministic" then
        M.sign_deterministic ~context key ~message |> result_ok
      else begin
        let calls = ref [] in
        let signature = M.sign ~context ~random:(fun length ->
          calls := length :: !calls;
          randomness) key ~message |> result_ok
        in
        Alcotest.(check (list int)) (label ^ " randomness callback")
          [ M.seed_size / 3 ] !calls;
        signature
      end
    in
    check_bytes label expected (M.signature_to_octets signature);
    Alcotest.(check bool) (label ^ " verifies") true
      (M.verify ~context public ~message signature)) rows

let test_sigver () =
  List.iter (fun (name, id, public, message, context, signature, expected) ->
    let module M = (val variant name : VARIANT) in
    let accepted =
      match M.verification_key_of_octets public, M.signature_of_octets signature with
      | Ok key, Ok signature -> M.verify ~context key ~message signature
      | _ -> false
    in
    Alcotest.(check bool) (name ^ " ACVP verification " ^ id) expected accepted)
    (read_sigver_vectors ())

let test_decoding () =
  List.iter (fun (name, (module M : VARIANT)) ->
    let check_lengths what size decode =
      List.iter (fun length ->
        expect_error (name ^ " accepted wrong " ^ what ^ " length")
          (decode (String.make length '\000')))
        [ 0; size - 1; size + 1 ]
    in
    check_lengths "seed" M.seed_size M.signing_key_of_seed;
    check_lengths "signing key" M.signing_key_size M.signing_key_of_octets;
    check_lengths "verification key" M.verification_key_size M.verification_key_of_octets;
    check_lengths "signature" M.signature_size M.signature_of_octets;
    List.iter (fun length ->
      expect_invalid_argument (name ^ " accepted wrong key-generation randomness length")
        (fun () -> M.generate ~random:(fun requested ->
          Alcotest.(check int) "requested key-generation randomness" M.seed_size requested;
          String.make length '\000') ()))
      [ 0; M.seed_size - 1; M.seed_size + 1 ]) variants

let test_generated_messages name =
  let module M = (val variant name : VARIANT) in
  (* Reproducible test data, not a cryptographic random provider. *)
  let state = Random.State.make [| 0x534c48; 0x445341 |] in
  let random length = String.init length (fun _ -> Char.chr (Random.State.int state 256)) in
  List.iter (fun (message_length, context_length) ->
    let message = random message_length and context = random context_length in
    let key, public = M.generate ~random () in
    let first = M.sign_deterministic ~context key ~message |> result_ok in
    let encoded_key = M.signing_key_to_octets key in
    let imported = M.signing_key_of_octets encoded_key |> result_ok in
    let repeated = M.sign_deterministic ~context imported ~message |> result_ok in
    check_bytes "deterministic signature survives key import"
      (M.signature_to_octets first) (M.signature_to_octets repeated);
    let hedged = M.sign ~context ~random key ~message |> result_ok in
    Alcotest.(check bool) "hedged signing uses fresh randomness" false
      (M.signature_to_octets first = M.signature_to_octets hedged);
    List.iter (fun signature ->
      Alcotest.(check bool) "generated message verifies" true
        (M.verify ~context public ~message signature);
      Alcotest.(check bool) "changed message fails" false
        (M.verify ~context public ~message:(message ^ "\000") signature);
      let wrong_context = if context = "" then "\000" else mutate context in
      Alcotest.(check bool) "changed context fails" false
        (M.verify ~context:wrong_context public ~message signature);
      let encoded = M.signature_to_octets signature in
      List.iter (fun offset ->
        let corrupt = Bytes.of_string encoded in
        Bytes.set corrupt offset (Char.chr (Char.code (Bytes.get corrupt offset) lxor 1));
        let corrupt = M.signature_of_octets (Bytes.to_string corrupt) |> result_ok in
        Alcotest.(check bool) (Printf.sprintf "corruption at byte %d fails" offset) false
          (M.verify ~context public ~message corrupt))
        [ 0; M.seed_size / 3; M.signature_size / 2; M.signature_size - 1 ])
      [ first; hedged ])
    [ 0, 0; 1, 255; 136, 1; 1024, 32 ]

let () =
  Alcotest.run "SLH-DSA"
    [
      ( "NIST ACVP",
        [
          Alcotest.test_case "key generation" `Slow test_keygen;
          Alcotest.test_case "signature generation" `Slow test_siggen;
          Alcotest.test_case "signature verification" `Slow test_sigver;
        ] );
      "decoding", [ Alcotest.test_case "length checks" `Quick test_decoding ];
      "additional NIST signing vectors",
        List.map (fun (name, _) ->
          Alcotest.test_case name `Slow (fun () -> test_extra_siggen name)) variants;
      "generated messages",
        List.map (fun name ->
          Alcotest.test_case name `Slow (fun () -> test_generated_messages name))
          [ "SLH-DSA-SHA2-128f"; "SLH-DSA-SHAKE-128f" ];
    ]
