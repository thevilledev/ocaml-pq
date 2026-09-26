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

(* The public extendable-output functions, against answers computed with
   OpenSSL. Input lengths sit on either side of the rate of each sponge, 168
   bytes for SHAKE128 and 136 for SHAKE256, where the padding changes shape, and
   the longer outputs span several squeezed blocks. Those are compared by their
   last 32 bytes. Inputs are the bytes [i mod 251]. *)
let test_fips202 () =
  let input length = String.init length (fun i -> Char.chr (i mod 251)) in
  let check name shake reference (input_length, output_length, expected_tail) =
    let label = Printf.sprintf "%s(%d bytes, %d)" name input_length output_length in
    let output = shake ~output_length (input input_length) in
    if String.length output <> output_length then
      Alcotest.failf "%s returned %d bytes" label (String.length output);
    let expected_tail = decode_hex expected_tail in
    let tail = String.length expected_tail in
    check_bytes label expected_tail (String.sub output (output_length - tail) tail);
    (* An extendable output is a prefix of every longer one. *)
    check_bytes (label ^ " prefix")
      (shake ~output_length:(output_length / 2) (input input_length))
      (String.sub output 0 (output_length / 2));
    (* It is the function ML-KEM itself runs on. *)
    check_bytes (label ^ " internal") (reference ~output_length (input input_length)) output
  in
  List.iter (check "SHAKE128" Mlkem.Fips202.shake128 K.shake128)
    [ 0, 32, "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26";
      0, 0, "";
      1, 1, "0b";
      167, 64,
      "1e552791cc4e93a0d4a8dc47ae49228c2faa869e40e628f6ace477aec3f1ca7a\
       efe1c1245cf82c265168ad2985121aedd72335ae1187a36742c746cf2b40cb30";
      168, 64,
      "f15277eb61c4908d44a2853f3cde071ae2ed7a23461fbe162a1a98cf6875059c\
       06ffeebfca31afd9976e5592a3e7e5e94a665a8befa4b64a7f089cc0f3572403";
      169, 64,
      "015be3338c986d9846affa0f94b4afc2a76bc289c709e1a596ec9eccf090a773\
       e4d69101b3a0516bfc556ffb886673b491f447926204119fed2933aea2d6091a";
      336, 169, "4e6d7fae075d1d34799184e2872d16c885ab51f97dd228e55ea216e0914cf402";
      337, 400, "5f043d5e81eff5b175f42711f1a0e63af423b6adc3a4576de37ec7afe2792917" ];
  List.iter (check "SHAKE256" Mlkem.Fips202.shake256 K.shake256)
    [ 0, 32, "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f";
      0, 0, "";
      1, 1, "b8";
      135, 64,
      "c45dae624ad8a2f5aa7bac9d7557737fd91c96eedb70a6be5574d57a844eade0\
       7f4056bf081a1098101cea8132188c422136feb4687d1e2209f3fd28bedfb8f4";
      136, 64,
      "b7ff4073b3f5a8eabd6e17705ca7f6761a31058f9df781a6a47e3a3063b9d67a\
       757e8dbf043dac48d2154e46d59c0b9e8bc36ba035153691fbe83b9eff5dae4a";
      137, 64,
      "01d90952c642a5eb2a8fc9d713f843a45d7ac05132dddcb2efc9bebc27e37bcb\
       e42130c36f3540250ab11796980e773683f28d07f0f838606fb9c45e452bd38f";
      272, 137, "19259dbb2a44b20d499865dda38ac387c32b820a9462bbaf208c2303eac7f7d8";
      273, 300, "a11afbe4536702607493aa49091d5384f97c81ba4bb7b08a63fd2565c11891bb" ];
  List.iter (fun (name, shake) ->
      match shake ~output_length:(-1) "" with
      | exception Invalid_argument message ->
          let prefix = "Mlkem.Fips202." ^ name in
          if not (String.length message >= String.length prefix
                  && String.sub message 0 (String.length prefix) = prefix) then
            Alcotest.failf "%s: unexpected message %S" name message
      | _ -> Alcotest.failf "%s accepted a negative output length" name)
    [ "shake128", Mlkem.Fips202.shake128; "shake256", Mlkem.Fips202.shake256 ]

(* TurboSHAKE (RFC 9861). [ptn n] is the pattern of RFC 9861, Section 5: the
   bytes [i mod 251]. The RFC's cases are its Section 5 in full except for the
   24 MB input ptn(17^6); the edge cases put the input on either side of the
   rate, where the padding changes shape, run the output over several squeezed
   blocks, and let the domain byte 0x7F share the last byte with the padding
   bit. Long outputs are compared by their last 32 bytes. *)
let ptn n = String.init n (fun i -> Char.chr (i mod 251))

(* Generated with pycryptodome 3.23, whose own suite holds it to the
   RFC 9861 vectors. *)
let turboshake128_rfc =
  [
    ("", 0x1f, 32, "1e415f1c5983aff2169217277d17bb538cd945a397ddec541f1ce41af2c1b74c");
    ("", 0x1f, 64, "1e415f1c5983aff2169217277d17bb538cd945a397ddec541f1ce41af2c1b74c3e8ccae2a4dae56c84a04c2385c03c15e8193bdf58737363321691c05462c8df");
    ("", 0x1f, 10032, "a3b9b0385900ce761f22aed548e754da10a5242d62e8c658e3f3a923a7555607");
    ((ptn 1), 0x1f, 32, "55cedd6f60af7bb29a4042ae832ef3f58db7299f893ebb9247247d856958daa9");
    ((ptn 17), 0x1f, 32, "9c97d036a3bac819db70ede0ca554ec6e4c2a1a4ffbfd9ec269ca6a111161233");
    ((ptn 289), 0x1f, 32, "96c77c279e0126f7fc07c9b07f5cdae1e0be60bdbe10620040e75d7223a624d2");
    ((ptn 4913), 0x1f, 32, "d4976eb56bcf118520582b709f73e1d6853e001fdaf80e1b13e0d0599d5fb372");
    ((ptn 83521), 0x1f, 32, "da67c7039e98bf530cf7a37830c6664e14cbab7f540f58403b1b82951318ee5c");
    ((ptn 1419857), 0x1f, 32, "b97a906fbf83ef7c812517abf3b2d0aea0c4f60318ce11cf103925127f59eecd");
    ((String.make 3 '\xff'), 0x01, 32, "bf323f940494e88ee1c540fe660be8a0c93f43d15ec006998462fa994eed5dab");
    ((String.make 1 '\xff'), 0x06, 32, "8ec9c66465ed0d4a6c35d13506718d687a25cb05c74cca1e42501abd83874a67");
    ((String.make 3 '\xff'), 0x07, 32, "b658576001cad9b1e5f399a9f77723bba05458042d68206f7252682dba3663ed");
    ((String.make 7 '\xff'), 0x0b, 32, "8deeaa1aec47ccee569f659c21dfa8e112db3cee37b18178b2acd805b799cc37");
    ((String.make 1 '\xff'), 0x30, 32, "553122e2135e363c3292bed2c6421fa232bab03daa07c7d6636603286506325b");
    ((String.make 3 '\xff'), 0x7f, 32, "16274cc656d44cefd422395d0f9053bda6d28e122aba15c765e5ad0e6eaf26f9");
  ]

let turboshake128_edge =
  [
    ((ptn 167), 0x1f, 64, "87dcddbaf9edd6f3b53a7c7a37bc11ae214b6b537ac6cca7bf638ac3152b04a9");
    ((ptn 167), 0x7f, 509, "15dd631c05228400963d04fc6a6535cd46a5e031eb697895f2cc163dbace7dab");
    ((ptn 168), 0x1f, 64, "fd8cefecb9248166f0a9a6ee5992397c06c70bc843ba0076b3ec42192ef71cce");
    ((ptn 168), 0x7f, 509, "4d6aa34e9198b86879eb0089bf8043335abc5f17b97c23fd7b5614faf131e156");
    ((ptn 169), 0x1f, 64, "64e288084227faaa693d90c7919dfdb17344d4bcc6cb40f2b592d62c8fff7729");
    ((ptn 169), 0x7f, 509, "fbc7df7598fe6b5663d0b493e553d76b746225aa01dce5b8ee9420519465b6ad");
    ((ptn 336), 0x1f, 64, "4218776d549feb9f241f27e7ea8f87ed5b9f5a3186fc23fe0f5c00f113c5c6a1");
    ((ptn 336), 0x7f, 509, "2d9124f78d89e7de9ea0f734be110eee4e921774c6c90891decf0291cb19669e");
  ]

let turboshake256_rfc =
  [
    ("", 0x1f, 64, "367a329dafea871c7802ec67f905ae13c57695dc2c6663c61035f59a18f8e7db11edc0e12e91ea60eb6b32df06dd7f002fbafabb6e13ec1cc20d995547600db0");
    ("", 0x1f, 64, "367a329dafea871c7802ec67f905ae13c57695dc2c6663c61035f59a18f8e7db11edc0e12e91ea60eb6b32df06dd7f002fbafabb6e13ec1cc20d995547600db0");
    ("", 0x1f, 10032, "abefa11630c661269249742685ec082f207265dccf2f43534e9c61ba0c9d1d75");
    ((ptn 1), 0x1f, 64, "3e1712f928f8eaf1054632b2aa0a246ed8b0c378728f60bc970410155c28820e90cc90d8a3006aa2372c5c5ea176b0682bf22bae7467ac94f74d43d39b0482e2");
    ((ptn 17), 0x1f, 64, "b3bab0300e6a191fbe6137939835923578794ea54843f5011090fa2f3780a9e5cb22c59d78b40a0fbff9e672c0fbe0970bd2c845091c6044d687054da5d8e9c7");
    ((ptn 289), 0x1f, 64, "66b810db8e90780424c0847372fdc95710882fde31c6df75beb9d4cd9305cfcae35e7b83e8b7e6eb4b78605880116316fe2c078a09b94ad7b8213c0a738b65c0");
    ((ptn 4913), 0x1f, 64, "c74ebc919a5b3b0dd1228185ba02d29ef442d69d3d4276a93efe0bf9a16a7dc0cd4eabadab8cd7a5edd96695f5d360abe09e2c6511a3ec397da3b76b9e1674fb");
    ((ptn 83521), 0x1f, 64, "02cc3a8897e6f4f6ccb6fd46631b1f5207b66c6de9c7b55b2d1a23134a170afdac234eaba9a77cff88c1f020b73724618c5687b362c430b248cd38647f848a1d");
    ((ptn 1419857), 0x1f, 64, "add53b06543e584b5823f626996aee50fe45ed15f20243a7165485acb4aa76b4ffda75cedf6d8cdc95c332bd56f4b986b58bb17d1778bfc1b1a97545cdf4ec9f");
    ((String.make 3 '\xff'), 0x01, 64, "d21c6fbbf587fa2282f29aea620175fb0257413af78a0b1b2a87419ce031d933ae7a4d383327a8a17641a34f8a1d1003ad7da6b72dba84bb62fef28f62f12424");
    ((String.make 1 '\xff'), 0x06, 64, "738d7b4e37d18b7f22ad1b5313e357e3dd7d07056a26a303c433fa3533455280f4f5a7d4f700efb437fe6d281405e07be32a0a972e22e63adc1b090daefe004b");
    ((String.make 3 '\xff'), 0x07, 64, "18b3b5b7061c2e67c1753a00e6ad7ed7ba1c906cf93efb7092eaf27fbeebb755ae6e292493c110e48d260028492b8e09b5500612b8f2578985ded5357d00ec67");
    ((String.make 7 '\xff'), 0x0b, 64, "bb36764951ec97e9d85f7ee9a67a7718fc005cf42556be79ce12c0bde50e5736d6632b0d0dfb202d1bbb8ffe3dd74cb00834fa756cb03471bab13a1e2c16b3c0");
    ((String.make 1 '\xff'), 0x30, 64, "f3fe12873d34bcbb2e608779d6b70e7f86bec7e90bf113cbd4fdd0c4e2f4625e148dd7ee1a52776cf77f240514d9ccfc3b5ddab8ee255e39ee389072962c111a");
    ((String.make 3 '\xff'), 0x7f, 64, "abe569c1f77ec340f02705e7d37c9ab7e155516e4a6a150021d70b6fac0bb40c069f9a9828a0d575cd99f9bae435ab1acf7ed9110ba97ce0388d074bac768776");
  ]

let turboshake256_edge =
  [
    ((ptn 135), 0x1f, 64, "8ccc694d4407f1dafb514f50c26f6a6fe8d1a2c09449413f7eeb3579be011e71");
    ((ptn 135), 0x7f, 413, "fec4c417dbb89481d4284bf72c89259dbb1ab93c5d000b6accf78fb8c1a8056d");
    ((ptn 136), 0x1f, 64, "753a6687d226f3db8bf0823cce510553c56832a87240a4b3bfab340a7a5df352");
    ((ptn 136), 0x7f, 413, "e74744b7abd0d35e0bcf5455055669370c32283170308ca3cbea450cf7c9a943");
    ((ptn 137), 0x1f, 64, "0b55cd24ec32c5c5344b4ca9ffd43973924a5dcd18fecd36e0a5ba4f58520394");
    ((ptn 137), 0x7f, 413, "b1fe38979b605be5e7b1fd680f8e69eaf58b1683d2f9770802ef79fa4d3eb10b");
    ((ptn 272), 0x1f, 64, "bf1a7a50bba32935a16f9dc0c8844b2258e2f39dc7ac1b928936a3bcb9d1c9ee");
    ((ptn 272), 0x7f, 413, "6701a3be1511e2731737f52725b20cbcd4a78a0d7988d6ff1703439561359b2d");
  ]

let test_rfc9861 () =
  let check name turboshake (input, domain, output_length, expected) =
    let label =
      Printf.sprintf "%s(%d bytes, D=0x%02x, %d)" name (String.length input)
        domain output_length
    in
    let output = turboshake ~domain ~output_length input in
    if String.length output <> output_length then
      Alcotest.failf "%s returned %d bytes" label (String.length output);
    let expected = decode_hex expected in
    let tail = String.length expected in
    check_bytes label expected (String.sub output (output_length - tail) tail);
    check_bytes (label ^ " prefix")
      (turboshake ~domain ~output_length:(output_length / 2) input)
      (String.sub output 0 (output_length / 2))
  in
  let turboshake128 ~domain ~output_length input =
    Mlkem.Rfc9861.turboshake128 ~domain ~output_length input
  and turboshake256 ~domain ~output_length input =
    Mlkem.Rfc9861.turboshake256 ~domain ~output_length input
  in
  List.iter (check "TurboSHAKE128" turboshake128)
    (turboshake128_rfc @ turboshake128_edge);
  List.iter (check "TurboSHAKE256" turboshake256)
    (turboshake256_rfc @ turboshake256_edge);
  (* The default domain is 0x1F, and a domain differs from SHAKE. *)
  check_bytes "TurboSHAKE128 default domain"
    (Mlkem.Rfc9861.turboshake128 ~domain:0x1f ~output_length:32 "")
    (Mlkem.Rfc9861.turboshake128 ~output_length:32 "");
  check_bytes "TurboSHAKE256 default domain"
    (Mlkem.Rfc9861.turboshake256 ~domain:0x1f ~output_length:64 "")
    (Mlkem.Rfc9861.turboshake256 ~output_length:64 "");
  if Mlkem.Rfc9861.turboshake128 ~output_length:32 ""
     = Mlkem.Fips202.shake128 ~output_length:32 ""
  then Alcotest.fail "TurboSHAKE128 is SHAKE128";
  List.iter
    (fun (name, turboshake) ->
      let expect_invalid label f =
        match f () with
        | exception Invalid_argument message ->
            let prefix = "Mlkem.Rfc9861." ^ name in
            if
              not
                (String.length message >= String.length prefix
                && String.sub message 0 (String.length prefix) = prefix)
            then Alcotest.failf "%s %s: unexpected message %S" name label message
        | _ -> Alcotest.failf "%s accepted %s" name label
      in
      expect_invalid "a negative output length" (fun () ->
          turboshake ~domain:0x1f ~output_length:(-1) "");
      List.iter
        (fun domain ->
          expect_invalid (Printf.sprintf "domain 0x%02x" domain) (fun () ->
              turboshake ~domain ~output_length:1 ""))
        [ 0x00; 0x80; 0xff; -1; 0x100 ];
      List.iter
        (fun domain ->
          ignore (turboshake ~domain ~output_length:1 ""))
        [ 0x01; 0x7f ])
    [ ("turboshake128", turboshake128); ("turboshake256", turboshake256) ]

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

let test_ct_equal () =
  let ciphertext = String.init 1088 (fun index -> Char.chr (index land 0xff)) in
  let flip index =
    String.mapi
      (fun position c ->
        if position = index then Char.chr (Char.code c lxor 0x80) else c)
      ciphertext
  in
  Alcotest.(check int) "equal" 1 (T.ct_equal ciphertext ciphertext);
  Alcotest.(check int) "empty" 1 (T.ct_equal "" "");
  Alcotest.(check int) "first byte differs" 0 (T.ct_equal ciphertext (flip 0));
  Alcotest.(check int) "last byte differs" 0 (T.ct_equal ciphertext (flip 1087));
  (* Unequal lengths never reach the byte loop, which would otherwise read
     the shorter string out of bounds. *)
  Alcotest.(check int) "second shorter" 0
    (T.ct_equal ciphertext (String.sub ciphertext 0 1087));
  Alcotest.(check int) "second empty" 0 (T.ct_equal ciphertext "");
  Alcotest.(check int) "second longer" 0 (T.ct_equal ciphertext (ciphertext ^ "\000"))

let test_randomness_contract () =
  Alcotest.check_raises "short randomness callback"
    (Invalid_argument "Mlkem768: randomness callback returned 63 bytes, expected 64")
    (fun () -> ignore (Mlkem.Mlkem768.generate ~random:(fun n -> String.make (n - 1) '\000') ()))

let () =
  Alcotest.run "mlkem"
    [ "primitives",
      [ Alcotest.test_case "Keccak known answers" `Quick test_keccak;
        Alcotest.test_case "public SHAKE known answers" `Quick test_fips202;
        Alcotest.test_case "public TurboSHAKE known answers" `Quick test_rfc9861 ];
      "FIPS 203 - ML-KEM-512",
      [ Alcotest.test_case "seed and decapsulation corpus" `Slow test_seeded_vectors_512;
        Alcotest.test_case "encapsulation corpus" `Slow test_encapsulation_vectors_512;
        Alcotest.test_case "expanded decapsulation corpus" `Slow
          test_decapsulation_vectors_512;
        Alcotest.test_case "Wycheproof corpus" `Slow (fun () ->
            run_wycheproof "512" (module W512)) ];
      "FIPS 203 - ML-KEM-768",
      [ Alcotest.test_case "NIST key generation" `Slow test_nist_keygen;
        Alcotest.test_case "encapsulation corpus" `Slow test_encapsulation_vectors;
        Alcotest.test_case "decapsulation corpus" `Slow test_decapsulation_vectors;
        Alcotest.test_case "Wycheproof corpus" `Slow (fun () ->
            run_wycheproof "768" (module W768)) ];
      "FIPS 203 - ML-KEM-1024",
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
        Alcotest.test_case "ciphertext comparison" `Quick test_ct_equal;
        Alcotest.test_case "randomness contract" `Quick test_randomness_contract ] ]
