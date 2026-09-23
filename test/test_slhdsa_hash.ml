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
  (* MGF1 answers computed with Python's hashlib. *)
  expect "MGF1-SHA-256(abc, 50)"
    ("cf2db1ac9867debdf8ce91f99f141e5544bf26ca36b3fd4f8e4035eec42cab0d"
     ^ "46c386ebccef82ba0bb0b095aaa5548b03cd")
    (hex (Slhdsa_for_testing.mgf1_sha256 ~output_length:50 "abc"));
  expect "MGF1-SHA-512(abc, 130)"
    ("7231a01ead7829a9af72bc1022b1021d69302e97d7888bf7e06e00dee9826108"
     ^ "b5a092e9eca7623bde11f0486e3d47c64e78754d9277e6d689557a75b6be7a8b"
     ^ "f79e6e2ad34ad32a3c37e3dfba8c50bd4605c5bbaf6e1fd9fe1dc6172d9121e0"
     ^ "280bf1c5f6cd4d3c6aba9966d3f68d4d725ff6f5ae9fbafad15c8127ea3f79ca"
     ^ "81c1")
    (hex (Slhdsa_for_testing.mgf1_sha512 ~output_length:130 "abc"));
  expect "MGF1-SHA-256(abc, 0)" ""
    (hex (Slhdsa_for_testing.mgf1_sha256 ~output_length:0 "abc"));
  let rejects name f =
    match f () with
    | exception Invalid_argument _ -> ()
    | _ -> failwith (name ^ ": expected Invalid_argument")
  in
  rejects "MGF1 negative length" (fun () ->
      Slhdsa_for_testing.mgf1_sha256 ~output_length:(-1) "abc");
  (* A mask one byte past 2^32 blocks is representable only with 63-bit
     ints. The check fires before anything is allocated. *)
  if Sys.int_size > 40 then begin
    let limit = (1 lsl 32) * 32 in
    rejects "MGF1-SHA-256 mask too long" (fun () ->
        Slhdsa_for_testing.mgf1_sha256 ~output_length:(limit + 1) "abc");
    rejects "MGF1-SHA-512 mask too long" (fun () ->
        Slhdsa_for_testing.mgf1_sha512 ~output_length:((2 * limit) + 1) "abc")
  end;
  print_endline "SLH-DSA hash primitive tests passed"
