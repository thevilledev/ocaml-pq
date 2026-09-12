let add_kem_tests name decode_ek encode_ek decode_ct decode_seed encode_seed =
  Crowbar.add_test ~name:(name ^ ": public-key and ciphertext decoding is total")
    [ Crowbar.bytes ]
    (fun input ->
      ignore (decode_ek input);
      ignore (decode_ct input));
  Crowbar.add_test ~name:(name ^ ": accepted public keys round trip canonically")
    [ Crowbar.bytes ]
    (fun input ->
      match decode_ek input with
      | Error _ -> ()
      | Ok key ->
          if encode_ek key <> input then
            Crowbar.fail "accepted public key did not round trip");
  Crowbar.add_test ~name:(name ^ ": seed expansion is total and stable")
    [ Crowbar.bytes ]
    (fun seed ->
      match decode_seed seed with
      | Error _ -> ()
      | Ok key ->
          if encode_seed key <> seed then
            Crowbar.fail "accepted decapsulation seed did not round trip")

let add_signature_tests name decode_vk encode_vk decode_sk encode_sk decode_sig
    encode_sig decode_seed encode_seed =
  Crowbar.add_test ~name:(name ^ ": key and signature decoding is total")
    [ Crowbar.bytes ]
    (fun input ->
      ignore (decode_vk input);
      ignore (decode_sk input);
      ignore (decode_sig input));
  Crowbar.add_test ~name:(name ^ ": accepted verification keys round trip")
    [ Crowbar.bytes ]
    (fun input ->
      match decode_vk input with
      | Error _ -> ()
      | Ok key ->
          if encode_vk key <> input then
            Crowbar.fail "accepted verification key did not round trip");
  Crowbar.add_test ~name:(name ^ ": accepted signing keys round trip")
    [ Crowbar.bytes ]
    (fun input ->
      match decode_sk input with
      | Error _ -> ()
      | Ok key ->
          if encode_sk key <> input then
            Crowbar.fail "accepted signing key did not round trip");
  Crowbar.add_test ~name:(name ^ ": accepted signatures round trip")
    [ Crowbar.bytes ]
    (fun input ->
      match decode_sig input with
      | Error _ -> ()
      | Ok signature ->
          if encode_sig signature <> input then
            Crowbar.fail "accepted signature did not round trip");
  Crowbar.add_test ~name:(name ^ ": seed expansion is total and stable")
    [ Crowbar.bytes ]
    (fun seed ->
      match decode_seed seed with
      | Error _ -> ()
      | Ok key ->
          if encode_seed key <> Some seed then
            Crowbar.fail "accepted signing seed did not round trip")

let wrong_length expected input =
  if String.length input = expected then input ^ "\000" else input

let add_slhdsa_tests name ~signing_key_size ~seed_size decode_vk encode_vk
    decode_sk decode_sig encode_sig decode_seed =
  Crowbar.add_test ~name:(name ^ ": cheap public decoding is total")
    [ Crowbar.bytes ]
    (fun input ->
      ignore (decode_vk input);
      ignore (decode_sig input);
      (* Exact-length SLH-DSA private-key imports reconstruct a Merkle root.
         Keep that deliberately expensive path in fuzz_slhdsa_keys. *)
      ignore (decode_sk (wrong_length signing_key_size input));
      ignore (decode_seed (wrong_length seed_size input)));
  Crowbar.add_test ~name:(name ^ ": accepted verification keys round trip")
    [ Crowbar.bytes ]
    (fun input ->
      match decode_vk input with
      | Error _ -> ()
      | Ok key ->
          if encode_vk key <> input then
            Crowbar.fail "accepted verification key did not round trip");
  Crowbar.add_test ~name:(name ^ ": accepted signatures round trip")
    [ Crowbar.bytes ]
    (fun input ->
      match decode_sig input with
      | Error _ -> ()
      | Ok signature ->
          if encode_sig signature <> input then
            Crowbar.fail "accepted signature did not round trip")

let add_slhdsa_key_tests name ~signing_key_size ~seed_size decode_sk encode_sk
    decode_seed encode_seed =
  Crowbar.add_test ~name:(name ^ ": exact-length signing-key import is total")
    [ Crowbar.bytes_fixed signing_key_size ]
    (fun input ->
      match decode_sk input with
      | Error _ -> ()
      | Ok key ->
          if encode_sk key <> input then
            Crowbar.fail "accepted signing key did not round trip");
  Crowbar.add_test ~name:(name ^ ": exact-length seed expansion is stable")
    [ Crowbar.bytes_fixed seed_size ]
    (fun seed ->
      match decode_seed seed with
      | Error _ -> Crowbar.fail "exact-length signing seed was rejected"
      | Ok key ->
          if encode_seed key <> Some seed then
            Crowbar.fail "accepted signing seed did not round trip")
