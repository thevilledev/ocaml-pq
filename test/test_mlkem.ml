module E512 = Mlkem.Mlkem512
module E768 = Mlkem.Mlkem768
module E1024 = Mlkem.Mlkem1024
module E = E768
module T = Mlkem_for_testing
module K = Mlkem_for_testing

let hex_value = function
  | '0' .. '9' as c -> Char.code c - Char.code '0'
  | 'a' .. 'f' as c -> 10 + Char.code c - Char.code 'a'
  | 'A' .. 'F' as c -> 10 + Char.code c - Char.code 'A'
  | c -> invalid_arg (Printf.sprintf "invalid hexadecimal digit %C" c)

let decode_hex value =
  let value = String.trim value in
  if String.length value mod 2 <> 0 then invalid_arg "odd-length hexadecimal value";
  String.init (String.length value / 2) (fun i ->
      Char.chr ((hex_value value.[2 * i] lsl 4) lor hex_value value.[(2 * i) + 1]))

let trim = String.trim

let split_field line =
  let colon = String.index_opt line ':' and equal = String.index_opt line '=' in
  let index =
    match colon, equal with
    | Some a, Some b -> min a b
    | Some a, None | None, Some a -> a
    | None, None -> invalid_arg ("invalid vector line: " ^ line)
  in
  trim (String.sub line 0 index),
  trim (String.sub line (index + 1) (String.length line - index - 1))

let read_blocks path =
  let channel = open_in path in
  let finish block blocks = if block = [] then blocks else List.rev block :: blocks in
  let rec loop block blocks =
    match input_line channel with
    | line when trim line = "" -> loop [] (finish block blocks)
    | line when String.length (trim line) > 0 && (trim line).[0] = '#' ->
        loop block blocks
    | line -> loop (split_field line :: block) blocks
    | exception End_of_file ->
        close_in channel;
        List.rev (finish block blocks)
  in
  loop [] []

let field name block =
  match List.assoc_opt name block with
  | Some value -> value
  | None -> Alcotest.failf "test vector is missing field %S" name

let vector_path name =
  let local = Filename.concat "vectors" name in
  if Sys.file_exists local then local else Filename.concat "test/vectors" name

let wycheproof_path name =
  let local = Filename.concat "wycheproof/mlkem" name in
  if Sys.file_exists local then local
  else Filename.concat "test/wycheproof/mlkem" name

let require_ok label = function
  | Ok value -> value
  | Error error -> Alcotest.failf "%s: %a" label E.pp_error error

let check_bytes label expected actual =
  if not (String.equal expected actual) then
    Alcotest.failf "%s differs (expected %d bytes, got %d bytes)"
      label (String.length expected) (String.length actual)

let test_keccak () =
  check_bytes "SHA3-256(empty)"
    (decode_hex "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a")
    (K.sha3_256 "");
  check_bytes "SHA3-512(empty)"
    (decode_hex
       "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a6\
        15b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26")
    (K.sha3_512 "");
  check_bytes "SHAKE128(empty, 256 bits)"
    (decode_hex "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26")
    (K.shake128 ~output_length:32 "");
  check_bytes "SHAKE256(empty, 512 bits)"
    (decode_hex
       "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f\
        d75dc4ddd8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be")
    (K.shake256 ~output_length:64 "")

let test_nist_keygen () =
  read_blocks (vector_path "mlkem768-keygen.txt")
  |> List.iteri (fun index vector ->
      let d = decode_hex (field "d" vector) in
      let z = decode_hex (field "z" vector) in
      let expected_ek = decode_hex (field "ek" vector) in
      let expected_dk = decode_hex (field "dk" vector) in
      let actual_dk, actual_ek = require_ok "key generation" (T.keygen_768 ~d ~z) in
      check_bytes (Printf.sprintf "keygen vector %d encapsulation key" index)
        expected_ek actual_ek;
      check_bytes (Printf.sprintf "keygen vector %d decapsulation key" index)
        expected_dk actual_dk)

let test_encapsulation_vectors () =
  read_blocks (vector_path "mlkem768-encap.txt")
  |> List.iteri (fun index vector ->
      let ek = decode_hex (field "public_key" vector) in
      let randomness = decode_hex (field "entropy" vector) in
      match field "result" vector with
      | "pass" ->
          let ciphertext, shared =
            require_ok "encapsulation" (T.encapsulate_768 ~encapsulation_key:ek ~randomness)
          in
          check_bytes (Printf.sprintf "encapsulation vector %d ciphertext" index)
            (decode_hex (field "ciphertext" vector)) ciphertext;
          check_bytes (Printf.sprintf "encapsulation vector %d shared secret" index)
            (decode_hex (field "shared_secret" vector)) shared
      | "fail" ->
          begin match T.encapsulate_768 ~encapsulation_key:ek ~randomness with
          | Error _ -> ()
          | Ok _ -> Alcotest.failf "encapsulation vector %d should be rejected" index
          end
      | result -> Alcotest.failf "encapsulation vector %d has result %S" index result)

let test_decapsulation_vectors () =
  read_blocks (vector_path "mlkem768-decap.txt")
  |> List.iteri (fun index vector ->
      let dk = decode_hex (field "private_key" vector) in
      let ciphertext = decode_hex (field "ciphertext" vector) in
      match field "result" vector with
      | "pass" ->
          let shared =
            require_ok "decapsulation"
              (T.decapsulate_768 ~expanded_decapsulation_key:dk ~ciphertext)
          in
          check_bytes (Printf.sprintf "decapsulation vector %d shared secret" index)
            (decode_hex (field "shared_secret" vector)) shared
      | "fail" ->
          begin match T.decapsulate_768 ~expanded_decapsulation_key:dk ~ciphertext with
          | Error _ -> ()
          | Ok _ -> Alcotest.failf "decapsulation vector %d should be rejected" index
          end
      | result -> Alcotest.failf "decapsulation vector %d has result %S" index result)

let test_seeded_vectors_512 () =
  read_blocks (vector_path "mlkem512-seed-decap.txt")
  |> List.iteri (fun index vector ->
      let seed = decode_hex (field "seed" vector) in
      let ciphertext = decode_hex (field "ciphertext" vector) in
      match field "result" vector with
      | "pass" ->
          let dk = require_ok "ML-KEM-512 seed" (E512.decapsulation_key_of_seed seed) in
          let ek = E512.encapsulation_key_of_decapsulation_key dk in
          check_bytes (Printf.sprintf "ML-KEM-512 vector %d encapsulation key" index)
            (decode_hex (field "public_key" vector))
            (E512.encapsulation_key_to_octets ek);
          let ciphertext =
            require_ok "ML-KEM-512 ciphertext" (E512.ciphertext_of_octets ciphertext)
          in
          check_bytes (Printf.sprintf "ML-KEM-512 vector %d shared secret" index)
            (decode_hex (field "shared_secret" vector))
            (E512.shared_secret_to_octets (E512.decapsulate dk ciphertext))
      | "fail" ->
          begin match E512.decapsulation_key_of_seed seed with
          | Error _ -> ()
          | Ok _ ->
              begin match E512.ciphertext_of_octets ciphertext with
              | Error _ -> ()
              | Ok _ -> Alcotest.failf "ML-KEM-512 vector %d should be rejected" index
              end
          end
      | result -> Alcotest.failf "ML-KEM-512 vector %d has result %S" index result)

let test_encapsulation_vectors_512 () =
  read_blocks (vector_path "mlkem512-encap.txt")
  |> List.iteri (fun index vector ->
      let ek = decode_hex (field "public_key" vector) in
      let randomness = decode_hex (field "entropy" vector) in
      match field "result" vector with
      | "pass" ->
          let ciphertext, shared =
            require_ok "ML-KEM-512 encapsulation"
              (T.encapsulate_512 ~encapsulation_key:ek ~randomness)
          in
          check_bytes (Printf.sprintf "ML-KEM-512 encapsulation %d ciphertext" index)
            (decode_hex (field "ciphertext" vector)) ciphertext;
          check_bytes (Printf.sprintf "ML-KEM-512 encapsulation %d shared secret" index)
            (decode_hex (field "shared_secret" vector)) shared
      | "fail" ->
          begin match T.encapsulate_512 ~encapsulation_key:ek ~randomness with
          | Error _ -> ()
          | Ok _ -> Alcotest.failf "ML-KEM-512 encapsulation %d should be rejected" index
          end
      | result -> Alcotest.failf "ML-KEM-512 encapsulation %d has result %S" index result)

let test_decapsulation_vectors_512 () =
  read_blocks (vector_path "mlkem512-decap.txt")
  |> List.iteri (fun index vector ->
      let dk = decode_hex (field "private_key" vector) in
      let ciphertext = decode_hex (field "ciphertext" vector) in
      match field "result" vector with
      | "pass" ->
          let shared =
            require_ok "ML-KEM-512 decapsulation"
              (T.decapsulate_512 ~expanded_decapsulation_key:dk ~ciphertext)
          in
          check_bytes (Printf.sprintf "ML-KEM-512 decapsulation %d shared secret" index)
            (decode_hex (field "shared_secret" vector)) shared
      | "fail" ->
          begin match T.decapsulate_512 ~expanded_decapsulation_key:dk ~ciphertext with
          | Error _ -> ()
          | Ok _ -> Alcotest.failf "ML-KEM-512 decapsulation %d should be rejected" index
          end
      | result -> Alcotest.failf "ML-KEM-512 decapsulation %d has result %S" index result)

let test_nist_keygen_1024 () =
  read_blocks (vector_path "mlkem1024-keygen.txt")
  |> List.iteri (fun index vector ->
      let d = decode_hex (field "d" vector) in
      let z = decode_hex (field "z" vector) in
      let expected_ek = decode_hex (field "ek" vector) in
      let expected_dk = decode_hex (field "dk" vector) in
      let actual_dk, actual_ek =
        require_ok "ML-KEM-1024 key generation" (T.keygen_1024 ~d ~z)
      in
      check_bytes (Printf.sprintf "ML-KEM-1024 keygen %d encapsulation key" index)
        expected_ek actual_ek;
      check_bytes (Printf.sprintf "ML-KEM-1024 keygen %d decapsulation key" index)
        expected_dk actual_dk)

let test_encapsulation_vectors_1024 () =
  read_blocks (vector_path "mlkem1024-encap.txt")
  |> List.iteri (fun index vector ->
      let ek = decode_hex (field "public_key" vector) in
      let randomness = decode_hex (field "entropy" vector) in
      match field "result" vector with
      | "pass" ->
          let ciphertext, shared =
            require_ok "ML-KEM-1024 encapsulation"
              (T.encapsulate_1024 ~encapsulation_key:ek ~randomness)
          in
          check_bytes (Printf.sprintf "ML-KEM-1024 encapsulation %d ciphertext" index)
            (decode_hex (field "ciphertext" vector)) ciphertext;
          check_bytes (Printf.sprintf "ML-KEM-1024 encapsulation %d shared secret" index)
            (decode_hex (field "shared_secret" vector)) shared
      | "fail" ->
          begin match T.encapsulate_1024 ~encapsulation_key:ek ~randomness with
          | Error _ -> ()
          | Ok _ -> Alcotest.failf "ML-KEM-1024 encapsulation %d should be rejected" index
          end
      | result -> Alcotest.failf "ML-KEM-1024 encapsulation %d has result %S" index result)

let test_decapsulation_vectors_1024 () =
  read_blocks (vector_path "mlkem1024-decap.txt")
  |> List.iteri (fun index vector ->
      let dk = decode_hex (field "private_key" vector) in
      let ciphertext = decode_hex (field "ciphertext" vector) in
      match field "result" vector with
      | "pass" ->
          let shared =
            require_ok "ML-KEM-1024 decapsulation"
              (T.decapsulate_1024 ~expanded_decapsulation_key:dk ~ciphertext)
          in
          check_bytes (Printf.sprintf "ML-KEM-1024 decapsulation %d shared secret" index)
            (decode_hex (field "shared_secret" vector)) shared
      | "fail" ->
          begin match T.decapsulate_1024 ~expanded_decapsulation_key:dk ~ciphertext with
          | Error _ -> ()
          | Ok _ -> Alcotest.failf "ML-KEM-1024 decapsulation %d should be rejected" index
          end
      | result -> Alcotest.failf "ML-KEM-1024 decapsulation %d has result %S" index result)

module type WYCHEPROOF_VARIANT = sig
  val keygen : seed:string -> ((string * string), unit) result
  val encapsulate :
    public_key:string -> randomness:string -> ((string * string), unit) result
  val decapsulate_expanded :
    private_key:string -> ciphertext:string -> (string, unit) result
  val decapsulate_seed :
    seed:string -> ciphertext:string -> ((string * string), unit) result
end

let without_error result = Result.map_error (fun _ -> ()) result

module W512 : WYCHEPROOF_VARIANT = struct
  let keygen ~seed =
    if String.length seed <> 64 then Error ()
    else
      T.keygen_512 ~d:(String.sub seed 0 32) ~z:(String.sub seed 32 32)
      |> without_error

  let encapsulate ~public_key ~randomness =
    T.encapsulate_512 ~encapsulation_key:public_key ~randomness
    |> without_error

  let decapsulate_expanded ~private_key ~ciphertext =
    T.decapsulate_512 ~expanded_decapsulation_key:private_key ~ciphertext
    |> without_error

  let decapsulate_seed ~seed ~ciphertext =
    match E512.decapsulation_key_of_seed seed,
          E512.ciphertext_of_octets ciphertext with
    | Ok private_key, Ok ciphertext ->
        let public_key = E512.encapsulation_key_of_decapsulation_key private_key in
        let shared_secret = E512.decapsulate private_key ciphertext in
        Ok (E512.encapsulation_key_to_octets public_key,
            E512.shared_secret_to_octets shared_secret)
    | Error _, _ | _, Error _ -> Error ()
end

module W768 : WYCHEPROOF_VARIANT = struct
  let keygen ~seed =
    if String.length seed <> 64 then Error ()
    else
      T.keygen_768 ~d:(String.sub seed 0 32) ~z:(String.sub seed 32 32)
      |> without_error

  let encapsulate ~public_key ~randomness =
    T.encapsulate_768 ~encapsulation_key:public_key ~randomness
    |> without_error

  let decapsulate_expanded ~private_key ~ciphertext =
    T.decapsulate_768 ~expanded_decapsulation_key:private_key ~ciphertext
    |> without_error

  let decapsulate_seed ~seed ~ciphertext =
    match E768.decapsulation_key_of_seed seed,
          E768.ciphertext_of_octets ciphertext with
    | Ok private_key, Ok ciphertext ->
        let public_key = E768.encapsulation_key_of_decapsulation_key private_key in
        let shared_secret = E768.decapsulate private_key ciphertext in
        Ok (E768.encapsulation_key_to_octets public_key,
            E768.shared_secret_to_octets shared_secret)
    | Error _, _ | _, Error _ -> Error ()
end

module W1024 : WYCHEPROOF_VARIANT = struct
  let keygen ~seed =
    if String.length seed <> 64 then Error ()
    else
      T.keygen_1024 ~d:(String.sub seed 0 32) ~z:(String.sub seed 32 32)
      |> without_error

  let encapsulate ~public_key ~randomness =
    T.encapsulate_1024 ~encapsulation_key:public_key ~randomness
    |> without_error

  let decapsulate_expanded ~private_key ~ciphertext =
    T.decapsulate_1024 ~expanded_decapsulation_key:private_key ~ciphertext
    |> without_error

  let decapsulate_seed ~seed ~ciphertext =
    match E1024.decapsulation_key_of_seed seed,
          E1024.ciphertext_of_octets ciphertext with
    | Ok private_key, Ok ciphertext ->
        let public_key = E1024.encapsulation_key_of_decapsulation_key private_key in
        let shared_secret = E1024.decapsulate private_key ciphertext in
        Ok (E1024.encapsulation_key_to_octets public_key,
            E1024.shared_secret_to_octets shared_secret)
    | Error _, _ | _, Error _ -> Error ()
end

let wycheproof_id vector =
  let flags = Option.value ~default:"" (List.assoc_opt "flags" vector) in
  Format.sprintf "%s (%s)" (field "id" vector) flags

let is_valid vector = String.equal (field "result" vector) "valid"

let run_wycheproof_keygen (module M : WYCHEPROOF_VARIANT) path =
  read_blocks path
  |> List.iter (fun vector ->
      let id = wycheproof_id vector in
      match is_valid vector, M.keygen ~seed:(decode_hex (field "seed" vector)) with
      | true, Ok (private_key, public_key) ->
          check_bytes ("Wycheproof private key " ^ id)
            (decode_hex (field "private_key" vector)) private_key;
          check_bytes ("Wycheproof public key " ^ id)
            (decode_hex (field "public_key" vector)) public_key
      | false, Error () -> ()
      | true, Error () -> Alcotest.failf "Wycheproof keygen %s was rejected" id
      | false, Ok _ -> Alcotest.failf "Wycheproof keygen %s was accepted" id)

let run_wycheproof_encapsulation (module M : WYCHEPROOF_VARIANT) path =
  read_blocks path
  |> List.iter (fun vector ->
      let id = wycheproof_id vector in
      let actual =
        M.encapsulate
          ~public_key:(decode_hex (field "public_key" vector))
          ~randomness:(decode_hex (field "randomness" vector))
      in
      match is_valid vector, actual with
      | true, Ok (ciphertext, shared_secret) ->
          check_bytes ("Wycheproof ciphertext " ^ id)
            (decode_hex (field "ciphertext" vector)) ciphertext;
          check_bytes ("Wycheproof shared secret " ^ id)
            (decode_hex (field "shared_secret" vector)) shared_secret
      | false, Error () -> ()
      | true, Error () -> Alcotest.failf "Wycheproof encapsulation %s was rejected" id
      | false, Ok _ ->
          Alcotest.failf "Wycheproof encapsulation %s was accepted" id)

let run_wycheproof_expanded_decapsulation
    (module M : WYCHEPROOF_VARIANT) path =
  read_blocks path
  |> List.iter (fun vector ->
      let id = wycheproof_id vector in
      let actual =
        M.decapsulate_expanded
          ~private_key:(decode_hex (field "private_key" vector))
          ~ciphertext:(decode_hex (field "ciphertext" vector))
      in
      match is_valid vector, actual with
      | true, Ok shared_secret ->
          check_bytes ("Wycheproof shared secret " ^ id)
            (decode_hex (field "shared_secret" vector)) shared_secret
      | false, Error () -> ()
      | true, Error () ->
          Alcotest.failf "Wycheproof expanded decapsulation %s was rejected" id
      | false, Ok _ ->
          Alcotest.failf "Wycheproof expanded decapsulation %s was accepted" id)

let run_wycheproof_seed_decapsulation (module M : WYCHEPROOF_VARIANT) path =
  read_blocks path
  |> List.iter (fun vector ->
      let id = wycheproof_id vector in
      let actual =
        M.decapsulate_seed
          ~seed:(decode_hex (field "seed" vector))
          ~ciphertext:(decode_hex (field "ciphertext" vector))
      in
      match is_valid vector, actual with
      | true, Ok (public_key, shared_secret) ->
          check_bytes ("Wycheproof public key " ^ id)
            (decode_hex (field "public_key" vector)) public_key;
          check_bytes ("Wycheproof shared secret " ^ id)
            (decode_hex (field "shared_secret" vector)) shared_secret
      | false, Error () -> ()
      | true, Error () ->
          Alcotest.failf "Wycheproof seed decapsulation %s was rejected" id
      | false, Ok _ ->
          Alcotest.failf "Wycheproof seed decapsulation %s was accepted" id)

let run_wycheproof parameter (module M : WYCHEPROOF_VARIANT) =
  let path suffix = wycheproof_path ("mlkem_" ^ parameter ^ suffix) in
  run_wycheproof_keygen (module M) (path "_keygen_seed_test.txt");
  run_wycheproof_encapsulation (module M) (path "_encaps_test.txt");
  run_wycheproof_expanded_decapsulation (module M)
    (path "_semi_expanded_decaps_test.txt");
  run_wycheproof_seed_decapsulation (module M) (path "_test.txt")

let deterministic_random =
  let counter = ref 0 in
  fun length ->
    let start = !counter in
    counter := start + length;
    String.init length (fun i -> Char.chr ((start + i) land 0xff))

let test_safe_api_roundtrip () =
  let dk, ek = Mlkem.Mlkem768.generate ~random:deterministic_random () in
  let ciphertext, shared = Mlkem.Mlkem768.encapsulate ~random:deterministic_random ek in
  let shared' = Mlkem.Mlkem768.decapsulate dk ciphertext in
  check_bytes "round-trip shared secret"
    (Mlkem.Mlkem768.shared_secret_to_octets shared)
    (Mlkem.Mlkem768.shared_secret_to_octets shared');
  let seed = Mlkem.Mlkem768.decapsulation_key_to_seed dk in
  Alcotest.(check int) "seed size" Mlkem.Mlkem768.seed_size (String.length seed);
  let reparsed = require_ok "seed key parse"
      (Mlkem.Mlkem768.decapsulation_key_of_seed seed) in
  let shared'' = Mlkem.Mlkem768.decapsulate reparsed ciphertext in
  check_bytes "seed-key round trip"
    (Mlkem.Mlkem768.shared_secret_to_octets shared)
    (Mlkem.Mlkem768.shared_secret_to_octets shared'')

let test_safe_api_roundtrip_512 () =
  let dk, ek = E512.generate ~random:deterministic_random () in
  let ciphertext, shared = E512.encapsulate ~random:deterministic_random ek in
  let shared' = E512.decapsulate dk ciphertext in
  check_bytes "ML-KEM-512 round-trip shared secret"
    (E512.shared_secret_to_octets shared) (E512.shared_secret_to_octets shared');
  Alcotest.(check int) "ML-KEM-512 encapsulation key size" 800
    (String.length (E512.encapsulation_key_to_octets ek));
  Alcotest.(check int) "ML-KEM-512 ciphertext size" 768
    (String.length (E512.ciphertext_to_octets ciphertext))

let test_safe_api_roundtrip_1024 () =
  let dk, ek = E1024.generate ~random:deterministic_random () in
  let ciphertext, shared = E1024.encapsulate ~random:deterministic_random ek in
  let shared' = E1024.decapsulate dk ciphertext in
  check_bytes "ML-KEM-1024 round-trip shared secret"
    (E1024.shared_secret_to_octets shared) (E1024.shared_secret_to_octets shared');
  Alcotest.(check int) "ML-KEM-1024 encapsulation key size" 1568
    (String.length (E1024.encapsulation_key_to_octets ek));
  Alcotest.(check int) "ML-KEM-1024 ciphertext size" 1568
    (String.length (E1024.ciphertext_to_octets ciphertext))

let test_strict_decoding () =
  let dk, ek = Mlkem.Mlkem768.generate ~random:deterministic_random () in
  let encoded = Mlkem.Mlkem768.encapsulation_key_to_octets ek in
  begin match Mlkem.Mlkem768.encapsulation_key_of_octets (encoded ^ "\000") with
  | Error (Invalid_length _) -> ()
  | _ -> Alcotest.fail "an oversized encapsulation key was not rejected"
  end;
  let unreduced = Bytes.of_string encoded in
  Bytes.set unreduced 0 '\001';
  Bytes.set unreduced 1
    (Char.chr ((Char.code (Bytes.get unreduced 1) land 0xf0) lor 0x0d));
  begin match Mlkem.Mlkem768.encapsulation_key_of_octets (Bytes.to_string unreduced) with
  | Error (Invalid_encoding _) -> ()
  | _ -> Alcotest.fail "an unreduced public-key coefficient was not rejected"
  end;
  let seed = Mlkem.Mlkem768.decapsulation_key_to_seed dk in
  let expanded, _ = require_ok "expanded test key"
      (T.keygen_768 ~d:(String.sub seed 0 32) ~z:(String.sub seed 32 32)) in
  let expanded = Bytes.of_string expanded in
  let hash_offset = (3 * 384) + Mlkem.Mlkem768.encapsulation_key_size in
  Bytes.set expanded hash_offset (Char.chr (Char.code (Bytes.get expanded hash_offset) lxor 1));
  begin match
    T.decapsulate_768 ~expanded_decapsulation_key:(Bytes.to_string expanded)
      ~ciphertext:(String.make Mlkem.Mlkem768.ciphertext_size '\000')
  with
  | Error (Invalid_encoding _) -> ()
  | _ -> Alcotest.fail "an inconsistent H(ek) was not rejected"
  end

let test_implicit_rejection () =
  let dk, ek = Mlkem.Mlkem768.generate ~random:deterministic_random () in
  let ciphertext, shared = Mlkem.Mlkem768.encapsulate ~random:deterministic_random ek in
  let changed = Bytes.of_string (Mlkem.Mlkem768.ciphertext_to_octets ciphertext) in
  Bytes.set changed 0 (Char.chr (Char.code (Bytes.get changed 0) lxor 1));
  let changed = require_ok "changed ciphertext parse"
      (Mlkem.Mlkem768.ciphertext_of_octets (Bytes.to_string changed)) in
  let rejected_1 = Mlkem.Mlkem768.decapsulate dk changed in
  let rejected_2 = Mlkem.Mlkem768.decapsulate dk changed in
  let valid = Mlkem.Mlkem768.shared_secret_to_octets shared in
  let invalid_1 = Mlkem.Mlkem768.shared_secret_to_octets rejected_1 in
  let invalid_2 = Mlkem.Mlkem768.shared_secret_to_octets rejected_2 in
  Alcotest.(check bool) "changed ciphertext does not recover the valid secret"
    false (String.equal valid invalid_1);
  check_bytes "implicit rejection is deterministic" invalid_1 invalid_2

let test_randomness_contract () =
  Alcotest.check_raises "short randomness callback"
    (Invalid_argument "Mlkem768: randomness callback returned 63 bytes, expected 64")
    (fun () -> ignore (Mlkem.Mlkem768.generate ~random:(fun n -> String.make (n - 1) '\000') ()))

let () =
  Alcotest.run "mlkem"
    [ "primitives", [ Alcotest.test_case "Keccak known answers" `Quick test_keccak ];
      "FIPS 203 / ML-KEM-512",
      [ Alcotest.test_case "seed and decapsulation corpus" `Slow test_seeded_vectors_512;
        Alcotest.test_case "encapsulation corpus" `Slow test_encapsulation_vectors_512;
        Alcotest.test_case "expanded decapsulation corpus" `Slow
          test_decapsulation_vectors_512;
        Alcotest.test_case "Wycheproof corpus" `Slow (fun () ->
            run_wycheproof "512" (module W512)) ];
      "FIPS 203 / ML-KEM-768",
      [ Alcotest.test_case "NIST key generation" `Slow test_nist_keygen;
        Alcotest.test_case "encapsulation corpus" `Slow test_encapsulation_vectors;
        Alcotest.test_case "decapsulation corpus" `Slow test_decapsulation_vectors;
        Alcotest.test_case "Wycheproof corpus" `Slow (fun () ->
            run_wycheproof "768" (module W768)) ];
      "FIPS 203 / ML-KEM-1024",
      [ Alcotest.test_case "NIST key generation" `Slow test_nist_keygen_1024;
        Alcotest.test_case "encapsulation corpus" `Slow test_encapsulation_vectors_1024;
        Alcotest.test_case "decapsulation corpus" `Slow test_decapsulation_vectors_1024;
        Alcotest.test_case "Wycheproof corpus" `Slow (fun () ->
            run_wycheproof "1024" (module W1024)) ];
      "API",
      [ Alcotest.test_case "round trip" `Quick test_safe_api_roundtrip;
        Alcotest.test_case "ML-KEM-512 round trip and sizes" `Quick
          test_safe_api_roundtrip_512;
        Alcotest.test_case "ML-KEM-1024 round trip and sizes" `Quick
          test_safe_api_roundtrip_1024;
        Alcotest.test_case "strict decoding" `Quick test_strict_decoding;
        Alcotest.test_case "implicit rejection" `Quick test_implicit_rejection;
        Alcotest.test_case "randomness contract" `Quick test_randomness_contract ] ]
