let add_tests name decode_ek encode_ek decode_ct decode_seed encode_seed =
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

let () =
  let module M = Mlkem.Mlkem512 in
  add_tests "ML-KEM-512" M.encapsulation_key_of_octets
    M.encapsulation_key_to_octets M.ciphertext_of_octets
    M.decapsulation_key_of_seed M.decapsulation_key_to_seed;
  let module M = Mlkem.Mlkem768 in
  add_tests "ML-KEM-768" M.encapsulation_key_of_octets
    M.encapsulation_key_to_octets M.ciphertext_of_octets
    M.decapsulation_key_of_seed M.decapsulation_key_to_seed;
  let module M = Mlkem.Mlkem1024 in
  add_tests "ML-KEM-1024" M.encapsulation_key_of_octets
    M.encapsulation_key_to_octets M.ciphertext_of_octets
    M.decapsulation_key_of_seed M.decapsulation_key_to_seed;
  let module M = Mldsa.Mldsa44 in
  add_signature_tests "ML-DSA-44" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Mldsa.Mldsa65 in
  add_signature_tests "ML-DSA-65" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Mldsa.Mldsa87 in
  add_signature_tests "ML-DSA-87" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Sha2_128s in
  add_signature_tests "SLH-DSA-SHA2-128s" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Sha2_128f in
  add_signature_tests "SLH-DSA-SHA2-128f" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Sha2_192s in
  add_signature_tests "SLH-DSA-SHA2-192s" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Sha2_192f in
  add_signature_tests "SLH-DSA-SHA2-192f" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Sha2_256s in
  add_signature_tests "SLH-DSA-SHA2-256s" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Sha2_256f in
  add_signature_tests "SLH-DSA-SHA2-256f" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Shake_128s in
  add_signature_tests "SLH-DSA-SHAKE-128s" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Shake_128f in
  add_signature_tests "SLH-DSA-SHAKE-128f" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Shake_192s in
  add_signature_tests "SLH-DSA-SHAKE-192s" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Shake_192f in
  add_signature_tests "SLH-DSA-SHAKE-192f" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Shake_256s in
  add_signature_tests "SLH-DSA-SHAKE-256s" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Shake_256f in
  add_signature_tests "SLH-DSA-SHAKE-256f" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed
