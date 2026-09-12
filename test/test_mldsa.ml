module type VARIANT = sig
  type error
  type signing_key
  type verification_key
  type signature

  val seed_size : int
  val signing_key_size : int
  val verification_key_size : int
  val signature_size : int

  val generate :
    random:(int -> string) -> unit -> signing_key * verification_key

  val signing_key_of_seed : string -> (signing_key, error) result
  val signing_key_to_seed : signing_key -> string option
  val signing_key_of_octets : string -> (signing_key, error) result
  val signing_key_to_octets : signing_key -> string
  val verification_key_of_signing_key : signing_key -> verification_key
  val verification_key_of_octets : string -> (verification_key, error) result
  val verification_key_to_octets : verification_key -> string
  val signature_of_octets : string -> (signature, error) result
  val signature_to_octets : signature -> string

  val sign :
    ?context:string ->
    random:(int -> string) ->
    signing_key ->
    message:string ->
    (signature, error) result

  val sign_deterministic :
    ?context:string -> signing_key -> message:string -> (signature, error) result

  val sign_internal :
    signing_key:string ->
    formatted_message:string ->
    randomness:string ->
    (string, error) result

  val sign_mu :
    signing_key:string ->
    mu:string ->
    randomness:string ->
    (string, error) result

  val verify_internal :
    verification_key:string ->
    formatted_message:string ->
    signature:string ->
    bool

  val verify_mu :
    verification_key:string ->
    mu:string ->
    signature:string ->
    bool

  val verify :
    ?context:string ->
    verification_key ->
    message:string ->
    signature ->
    bool
end

let hex_value = function
  | '0' .. '9' as value -> Char.code value - Char.code '0'
  | 'a' .. 'f' as value -> Char.code value - Char.code 'a' + 10
  | 'A' .. 'F' as value -> Char.code value - Char.code 'A' + 10
  | _ -> invalid_arg "invalid hexadecimal test vector"

let decode_hex input =
  if String.length input mod 2 <> 0 then invalid_arg "odd hexadecimal test vector";
  let output = Bytes.create (String.length input / 2) in
  for index = 0 to Bytes.length output - 1 do
    let high = hex_value input.[2 * index] in
    let low = hex_value input.[(2 * index) + 1] in
    Bytes.set output index (Char.chr ((high lsl 4) lor low))
  done;
  Bytes.unsafe_to_string output

let read_vectors path =
  let channel = open_in path in
  let finish current vectors =
    if current = [] then vectors else List.rev current :: vectors
  in
  let rec loop current vectors =
    match input_line channel with
    | line ->
        let line = String.trim line in
        if line = "" then loop [] (finish current vectors)
        else if line.[0] = '#' then loop current vectors
        else begin
          match String.index_opt line ':' with
          | None -> failwith ("invalid vector line: " ^ line)
          | Some colon ->
              let key = String.sub line 0 colon |> String.trim in
              let value =
                String.sub line (colon + 1) (String.length line - colon - 1)
                |> String.trim
              in
              loop ((key, value) :: current) vectors
        end
    | exception End_of_file ->
        close_in channel;
        List.rev (finish current vectors)
  in
  loop [] []

let raw_field name vector =
  match List.assoc_opt name vector with
  | Some value -> value
  | None -> failwith ("missing vector field " ^ name)

let field name vector = decode_hex (raw_field name vector)

let vector_path name =
  let local = Filename.concat "mldsa_vectors" name in
  if Sys.file_exists local then local
  else Filename.concat "test/mldsa_vectors" name

let wycheproof_path name =
  let local = Filename.concat "wycheproof/mldsa" name in
  if Sys.file_exists local then local
  else Filename.concat "test/wycheproof/mldsa" name

let result_ok = function
  | Ok value -> value
  | Error _ -> Alcotest.fail "operation unexpectedly returned an error"

let run_keygen (module M : VARIANT) path =
  List.iteri
    (fun index vector ->
      let seed = field "seed" vector in
      let expected_public = field "pub" vector in
      let expected_private = field "priv" vector in
      let private_key = M.signing_key_of_seed seed |> result_ok in
      let public_key = M.verification_key_of_signing_key private_key in
      Alcotest.(check string)
        (Format.sprintf "public key %d" index)
        expected_public (M.verification_key_to_octets public_key);
      Alcotest.(check string)
        (Format.sprintf "private key %d" index)
        expected_private (M.signing_key_to_octets private_key))
    (read_vectors path)

let run_siggen (module M : VARIANT) path =
  List.iteri
    (fun index vector ->
      let private_key_octets = field "sk" vector in
      let private_key = private_key_octets |> M.signing_key_of_octets |> result_ok in
      let public_key = M.verification_key_of_signing_key private_key in
      let public_key_octets = M.verification_key_to_octets public_key in
      let message = field "message" vector in
      let expected = field "signature" vector in
      let actual =
        M.sign_internal ~signing_key:private_key_octets
          ~formatted_message:message ~randomness:(String.make 32 '\000')
        |> result_ok
      in
      Alcotest.(check string)
        (Format.sprintf "signature %d" index)
        expected actual;
      ignore (M.signature_of_octets expected |> result_ok);
      Alcotest.(check bool)
        (Format.sprintf "verification %d" index)
        true
        (M.verify_internal ~verification_key:public_key_octets
           ~formatted_message:message ~signature:expected))
    (read_vectors path)

let formatted_message context message =
  String.make 1 '\000'
  ^ String.make 1 (Char.unsafe_chr (String.length context))
  ^ context ^ message

let run_wycheproof_sign (module M : VARIANT) ~seed_key path =
  let current_private = ref None in
  let current_public = ref None in
  List.iter
    (fun vector ->
      if String.equal (raw_field "group" vector) "new" then begin
        current_private := Some (field "private_key" vector);
        current_public := Some (field "public_key" vector)
      end;
      let private_key = Option.get !current_private in
      let expected_public = Option.get !current_public in
      let id = raw_field "id" vector in
      let flags = raw_field "flags" vector in
      let expected_valid = String.equal (raw_field "result" vector) "valid" in
      let randomness =
        match field "randomness" vector with
        | "" -> String.make 32 '\000'
        | value -> value
      in
      let signing_key =
        if seed_key then M.signing_key_of_seed private_key
        else M.signing_key_of_octets private_key
      in
      let actual =
        match signing_key with
        | Error _ -> None
        | Ok signing_key ->
            let expanded = M.signing_key_to_octets signing_key in
            let public_key = M.verification_key_of_signing_key signing_key in
            if expected_valid then
              Alcotest.(check string)
                (Format.sprintf "Wycheproof public key %s" id)
                expected_public (M.verification_key_to_octets public_key);
            if String.equal (raw_field "interface" vector) "internal" then
              begin match
                M.sign_mu ~signing_key:expanded ~mu:(field "mu" vector)
                  ~randomness
              with
              | Error _ -> None
              | Ok signature -> Some signature
              end
            else
              let context = field "context" vector in
              if String.length context > 255 then None
              else
                begin match
                  M.sign_internal ~signing_key:expanded
                    ~formatted_message:
                      (formatted_message context (field "message" vector))
                    ~randomness
                with
                | Error _ -> None
                | Ok signature -> Some signature
                end
      in
      match expected_valid, actual with
      | false, None -> ()
      | false, Some _ ->
          Alcotest.failf "Wycheproof signing vector %s (%s) was accepted" id flags
      | true, None ->
          Alcotest.failf "Wycheproof signing vector %s (%s) was rejected" id flags
      | true, Some actual ->
          let expected = field "signature" vector in
          Alcotest.(check string)
            (Format.sprintf "Wycheproof signature %s (%s)" id flags)
            expected actual;
          let verified =
            if String.equal (raw_field "interface" vector) "internal" then
              M.verify_mu ~verification_key:expected_public ~mu:(field "mu" vector)
                ~signature:actual
            else
              M.verify_internal ~verification_key:expected_public
                ~formatted_message:
                  (formatted_message (field "context" vector) (field "message" vector))
                ~signature:actual
          in
          Alcotest.(check bool)
            (Format.sprintf "Wycheproof generated signature %s verifies" id)
            true verified)
    (read_vectors path)

let run_wycheproof_verify (module M : VARIANT) path =
  let current_public = ref None in
  List.iter
    (fun vector ->
      if String.equal (raw_field "group" vector) "new" then
        current_public := Some (field "public_key" vector);
      let public_key = Option.get !current_public in
      let context = field "context" vector in
      let actual =
        if String.length context > 255 then false
        else
          M.verify_internal ~verification_key:public_key
            ~formatted_message:(formatted_message context (field "message" vector))
            ~signature:(field "signature" vector)
      in
      let expected = String.equal (raw_field "result" vector) "valid" in
      Alcotest.(check bool)
        (Format.sprintf "Wycheproof verification %s (%s)"
           (raw_field "id" vector) (raw_field "flags" vector))
        expected actual)
    (read_vectors path)

let expect_error message = function
  | Error _ -> ()
  | Ok _ -> Alcotest.fail message

let test_api (module M : VARIANT) =
  let seed = String.init M.seed_size (fun index -> Char.chr index) in
  let signing_key = M.signing_key_of_seed seed |> result_ok in
  let verification_key = M.verification_key_of_signing_key signing_key in
  Alcotest.(check int) "seed size" 32 M.seed_size;
  Alcotest.(check (option string)) "seed round trip" (Some seed)
    (M.signing_key_to_seed signing_key);
  Alcotest.(check int) "encoded signing key size" M.signing_key_size
    (String.length (M.signing_key_to_octets signing_key));
  Alcotest.(check int) "encoded verification key size" M.verification_key_size
    (String.length (M.verification_key_to_octets verification_key));
  let message = "pure OCaml ML-DSA" in
  let deterministic = M.sign_deterministic signing_key ~message |> result_ok in
  Alcotest.(check int) "signature size" M.signature_size
    (String.length (M.signature_to_octets deterministic));
  Alcotest.(check bool) "deterministic signature verifies" true
    (M.verify verification_key ~message deterministic);
  Alcotest.(check bool) "wrong message fails" false
    (M.verify verification_key ~message:(message ^ "!") deterministic);
  let contextual =
    M.sign_deterministic ~context:"ocaml-pq" signing_key ~message |> result_ok
  in
  Alcotest.(check bool) "matching context verifies" true
    (M.verify ~context:"ocaml-pq" verification_key ~message contextual);
  Alcotest.(check bool) "wrong context fails" false
    (M.verify ~context:"other" verification_key ~message contextual);
  let hedged =
    M.sign ~random:(fun length -> String.make length '\165') signing_key ~message
    |> result_ok
  in
  Alcotest.(check bool) "hedged signature verifies" true
    (M.verify verification_key ~message hedged);
  Alcotest.(check bool) "hedged signature differs" false
    (String.equal (M.signature_to_octets deterministic) (M.signature_to_octets hedged));
  expect_error "long signing context accepted"
    (M.sign_deterministic ~context:(String.make 256 'x') signing_key ~message);
  let random_called = ref false in
  expect_error "long hedged signing context accepted"
    (M.sign ~context:(String.make 256 'x')
       ~random:(fun length ->
         random_called := true;
         String.make length '\000')
       signing_key ~message);
  Alcotest.(check bool) "invalid context does not consume randomness" false
    !random_called;
  Alcotest.(check bool) "long verification context fails" false
    (M.verify ~context:(String.make 256 'x') verification_key ~message deterministic);
  expect_error "short seed accepted" (M.signing_key_of_seed "short");
  expect_error "short signing key accepted" (M.signing_key_of_octets "short");
  expect_error "short verification key accepted" (M.verification_key_of_octets "short");
  expect_error "short signature accepted" (M.signature_of_octets "short");
  let imported =
    M.signing_key_to_octets signing_key |> M.signing_key_of_octets |> result_ok
  in
  Alcotest.(check (option string)) "expanded import has no seed" None
    (M.signing_key_to_seed imported);
  let corrupt_key = Bytes.of_string (M.signing_key_to_octets signing_key) in
  Bytes.set corrupt_key 64 (Char.chr (Char.code (Bytes.get corrupt_key 64) lxor 1));
  expect_error "inconsistent signing key accepted"
    (M.signing_key_of_octets (Bytes.unsafe_to_string corrupt_key));
  let malformed = Bytes.of_string (M.signature_to_octets deterministic) in
  Bytes.set malformed (M.signature_size - 1) (Char.chr 255);
  expect_error "malformed hint accepted"
    (M.signature_of_octets (Bytes.unsafe_to_string malformed));
  match M.generate ~random:(fun _ -> "x") () with
  | exception Invalid_argument _ -> ()
  | _ -> Alcotest.fail "short randomness callback accepted"

let () =
  let module M44 = struct
    include Mldsa.Mldsa44
    let sign_internal = Mldsa_for_testing.sign_internal_44
    let sign_mu = Mldsa_for_testing.sign_mu_44
    let verify_internal = Mldsa_for_testing.verify_internal_44
    let verify_mu = Mldsa_for_testing.verify_mu_44
  end in
  let module M65 = struct
    include Mldsa.Mldsa65
    let sign_internal = Mldsa_for_testing.sign_internal_65
    let sign_mu = Mldsa_for_testing.sign_mu_65
    let verify_internal = Mldsa_for_testing.verify_internal_65
    let verify_mu = Mldsa_for_testing.verify_mu_65
  end in
  let module M87 = struct
    include Mldsa.Mldsa87
    let sign_internal = Mldsa_for_testing.sign_internal_87
    let sign_mu = Mldsa_for_testing.sign_mu_87
    let verify_internal = Mldsa_for_testing.verify_internal_87
    let verify_mu = Mldsa_for_testing.verify_mu_87
  end in
  Alcotest.run "ML-DSA"
    [ ( "ML-DSA-44",
        [ Alcotest.test_case "NIST key generation" `Slow (fun () ->
              run_keygen (module M44)
                (vector_path "mldsa_nist_keygen_44_tests.txt"));
          Alcotest.test_case "NIST deterministic signatures" `Slow (fun () ->
              run_siggen (module M44)
                (vector_path "mldsa_nist_siggen_44_tests.txt"));
          Alcotest.test_case "Wycheproof seed signing" `Slow (fun () ->
              run_wycheproof_sign (module M44) ~seed_key:true
                (wycheproof_path "mldsa_44_sign_seed_test.txt"));
          Alcotest.test_case "Wycheproof expanded-key signing" `Slow (fun () ->
              run_wycheproof_sign (module M44) ~seed_key:false
                (wycheproof_path "mldsa_44_sign_noseed_test.txt"));
          Alcotest.test_case "Wycheproof verification" `Slow (fun () ->
              run_wycheproof_verify (module M44)
                (wycheproof_path "mldsa_44_verify_test.txt"));
          Alcotest.test_case "typed API and validation" `Slow (fun () ->
              test_api (module M44)) ] );
      ( "ML-DSA-65",
        [ Alcotest.test_case "NIST key generation" `Slow (fun () ->
              run_keygen (module M65)
                (vector_path "mldsa_nist_keygen_65_tests.txt"));
          Alcotest.test_case "NIST deterministic signatures" `Slow (fun () ->
              run_siggen (module M65)
                (vector_path "mldsa_nist_siggen_65_tests.txt"));
          Alcotest.test_case "Wycheproof seed signing" `Slow (fun () ->
              run_wycheproof_sign (module M65) ~seed_key:true
                (wycheproof_path "mldsa_65_sign_seed_test.txt"));
          Alcotest.test_case "Wycheproof expanded-key signing" `Slow (fun () ->
              run_wycheproof_sign (module M65) ~seed_key:false
                (wycheproof_path "mldsa_65_sign_noseed_test.txt"));
          Alcotest.test_case "Wycheproof verification" `Slow (fun () ->
              run_wycheproof_verify (module M65)
                (wycheproof_path "mldsa_65_verify_test.txt"));
          Alcotest.test_case "typed API and validation" `Slow (fun () ->
              test_api (module M65)) ] );
      ( "ML-DSA-87",
        [ Alcotest.test_case "NIST key generation" `Slow (fun () ->
              run_keygen (module M87)
                (vector_path "mldsa_nist_keygen_87_tests.txt"));
          Alcotest.test_case "NIST deterministic signatures" `Slow (fun () ->
              run_siggen (module M87)
                (vector_path "mldsa_nist_siggen_87_tests.txt"));
          Alcotest.test_case "Wycheproof seed signing" `Slow (fun () ->
              run_wycheproof_sign (module M87) ~seed_key:true
                (wycheproof_path "mldsa_87_sign_seed_test.txt"));
          Alcotest.test_case "Wycheproof expanded-key signing" `Slow (fun () ->
              run_wycheproof_sign (module M87) ~seed_key:false
                (wycheproof_path "mldsa_87_sign_noseed_test.txt"));
          Alcotest.test_case "Wycheproof verification" `Slow (fun () ->
              run_wycheproof_verify (module M87)
                (wycheproof_path "mldsa_87_verify_test.txt"));
          Alcotest.test_case "typed API and validation" `Slow (fun () ->
              test_api (module M87)) ] ) ]
