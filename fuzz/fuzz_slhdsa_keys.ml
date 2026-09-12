let () =
  let add name signing_key_size seed_size decode_sk encode_sk decode_seed
      encode_seed =
    Fuzz_helpers.add_slhdsa_key_tests name ~signing_key_size ~seed_size
      decode_sk encode_sk decode_seed encode_seed
  in
  let module M = Slhdsa.Sha2_128s in
  add "SLH-DSA-SHA2-128s" M.signing_key_size M.seed_size
    M.signing_key_of_octets M.signing_key_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Sha2_128f in
  add "SLH-DSA-SHA2-128f" M.signing_key_size M.seed_size
    M.signing_key_of_octets M.signing_key_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Sha2_192s in
  add "SLH-DSA-SHA2-192s" M.signing_key_size M.seed_size
    M.signing_key_of_octets M.signing_key_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Sha2_192f in
  add "SLH-DSA-SHA2-192f" M.signing_key_size M.seed_size
    M.signing_key_of_octets M.signing_key_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Sha2_256s in
  add "SLH-DSA-SHA2-256s" M.signing_key_size M.seed_size
    M.signing_key_of_octets M.signing_key_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Sha2_256f in
  add "SLH-DSA-SHA2-256f" M.signing_key_size M.seed_size
    M.signing_key_of_octets M.signing_key_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Shake_128s in
  add "SLH-DSA-SHAKE-128s" M.signing_key_size M.seed_size
    M.signing_key_of_octets M.signing_key_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Shake_128f in
  add "SLH-DSA-SHAKE-128f" M.signing_key_size M.seed_size
    M.signing_key_of_octets M.signing_key_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Shake_192s in
  add "SLH-DSA-SHAKE-192s" M.signing_key_size M.seed_size
    M.signing_key_of_octets M.signing_key_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Shake_192f in
  add "SLH-DSA-SHAKE-192f" M.signing_key_size M.seed_size
    M.signing_key_of_octets M.signing_key_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Shake_256s in
  add "SLH-DSA-SHAKE-256s" M.signing_key_size M.seed_size
    M.signing_key_of_octets M.signing_key_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Slhdsa.Shake_256f in
  add "SLH-DSA-SHAKE-256f" M.signing_key_size M.seed_size
    M.signing_key_of_octets M.signing_key_to_octets M.signing_key_of_seed
    M.signing_key_to_seed
