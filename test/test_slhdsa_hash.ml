let hex s =
  let digits = "0123456789abcdef" in
  String.init (2 * String.length s) (fun i ->
      let byte = Char.code (String.unsafe_get s (i / 2)) in
      String.unsafe_get digits
        (if i land 1 = 0 then byte lsr 4 else byte land 0x0f))

let expect name expected actual =
  if actual <> expected then
    failwith (Printf.sprintf "%s: expected %s, got %s" name expected actual)

let () =
  expect "SHA-256(empty)"
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    (hex (Slhdsa_for_testing.sha256 ""));
  expect "SHA-256(abc)"
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    (hex (Slhdsa_for_testing.sha256 "abc"));
  expect "SHA-512(empty)"
    ("cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce"
     ^ "47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")
    (hex (Slhdsa_for_testing.sha512 ""));
  expect "SHA-512(abc)"
    ("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a"
     ^ "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
    (hex (Slhdsa_for_testing.sha512 "abc"));
  let key = String.make 20 '\x0b' in
  expect "HMAC-SHA-256"
    "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
    (hex (Slhdsa_for_testing.hmac_sha256 key "Hi There"));
  expect "HMAC-SHA-512"
    ("87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cde"
     ^ "daa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854")
    (hex (Slhdsa_for_testing.hmac_sha512 key "Hi There"));
  expect "SHAKE-256(empty)"
    ("46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f"
     ^ "d75dc4ddd8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be")
    (hex (Slhdsa_for_testing.shake256 ~output_length:64 ""));
  print_endline "SLH-DSA hash primitive tests passed"
