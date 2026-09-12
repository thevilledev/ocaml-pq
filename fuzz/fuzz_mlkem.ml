let () =
  let module M = Mlkem.Mlkem512 in
  Fuzz_helpers.add_kem_tests "ML-KEM-512" M.encapsulation_key_of_octets
    M.encapsulation_key_to_octets M.ciphertext_of_octets
    M.decapsulation_key_of_seed M.decapsulation_key_to_seed;
  let module M = Mlkem.Mlkem768 in
  Fuzz_helpers.add_kem_tests "ML-KEM-768" M.encapsulation_key_of_octets
    M.encapsulation_key_to_octets M.ciphertext_of_octets
    M.decapsulation_key_of_seed M.decapsulation_key_to_seed;
  let module M = Mlkem.Mlkem1024 in
  Fuzz_helpers.add_kem_tests "ML-KEM-1024" M.encapsulation_key_of_octets
    M.encapsulation_key_to_octets M.ciphertext_of_octets
    M.decapsulation_key_of_seed M.decapsulation_key_to_seed
