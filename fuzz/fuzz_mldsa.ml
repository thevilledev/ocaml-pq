let () =
  let module M = Mldsa.Mldsa44 in
  Fuzz_helpers.add_signature_tests "ML-DSA-44" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Mldsa.Mldsa65 in
  Fuzz_helpers.add_signature_tests "ML-DSA-65" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed;
  let module M = Mldsa.Mldsa87 in
  Fuzz_helpers.add_signature_tests "ML-DSA-87" M.verification_key_of_octets
    M.verification_key_to_octets M.signing_key_of_octets M.signing_key_to_octets
    M.signature_of_octets M.signature_to_octets M.signing_key_of_seed
    M.signing_key_to_seed
