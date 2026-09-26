let round_constants =
  [|
    0x0000000000000001L; 0x0000000000008082L;
    0x800000000000808aL; 0x8000000080008000L;
    0x000000000000808bL; 0x0000000080000001L;
    0x8000000080008081L; 0x8000000000008009L;
    0x000000000000008aL; 0x0000000000000088L;
    0x0000000080008009L; 0x000000008000000aL;
    0x000000008000808bL; 0x800000000000008bL;
    0x8000000000008089L; 0x8000000000008003L;
    0x8000000000008002L; 0x8000000000000080L;
    0x000000000000800aL; 0x800000008000000aL;
    0x8000000080008081L; 0x8000000000008080L;
    0x0000000080000001L; 0x8000000080008008L;
  |]

let rotation =
  [|
     0;  1; 62; 28; 27;
    36; 44;  6; 55; 20;
     3; 10; 43; 25; 39;
    41; 45; 15; 21;  8;
    18;  2; 61; 56; 14;
  |]

let rotl x n =
  if n = 0 then x
  else Int64.logor (Int64.shift_left x n) (Int64.shift_right_logical x (64 - n))

(* Rounds [first] to 23 of KECCAK-f[1600], which is KECCAK-p[1600, 24 - first]
   (FIPS 202, Section 3.3): the whole permutation from round 0, the one of
   TurboSHAKE (RFC 9861) from round 12. *)
let permute_from first a =
  let c = Array.make 5 0L in
  let d = Array.make 5 0L in
  let b = Array.make 25 0L in
  for round = first to 23 do
    for x = 0 to 4 do
      c.(x) <-
        Int64.logxor a.(x)
          (Int64.logxor a.(x + 5)
             (Int64.logxor a.(x + 10)
                (Int64.logxor a.(x + 15) a.(x + 20))))
    done;
    for x = 0 to 4 do
      d.(x) <- Int64.logxor c.((x + 4) mod 5) (rotl c.((x + 1) mod 5) 1)
    done;
    for y = 0 to 4 do
      for x = 0 to 4 do
        a.(x + (5 * y)) <- Int64.logxor a.(x + (5 * y)) d.(x)
      done
    done;
    for y = 0 to 4 do
      for x = 0 to 4 do
        let new_x = y in
        let new_y = ((2 * x) + (3 * y)) mod 5 in
        b.(new_x + (5 * new_y)) <- rotl a.(x + (5 * y)) rotation.(x + (5 * y))
      done
    done;
    for y = 0 to 4 do
      for x = 0 to 4 do
        a.(x + (5 * y)) <-
          Int64.logxor b.(x + (5 * y))
            (Int64.logand (Int64.lognot b.(((x + 1) mod 5) + (5 * y)))
               b.(((x + 2) mod 5) + (5 * y)))
      done
    done;
    a.(0) <- Int64.logxor a.(0) round_constants.(round)
  done

let permute a = permute_from 0 a

let load64_le s off =
  let r = ref 0L in
  for i = 0 to 7 do
    r := Int64.logor !r
        (Int64.shift_left (Int64.of_int (Char.code (String.unsafe_get s (off + i)))) (8 * i))
  done;
  !r

let store64_le b off x =
  for i = 0 to 7 do
    Bytes.unsafe_set b (off + i)
      (Char.unsafe_chr (Int64.to_int (Int64.logand (Int64.shift_right_logical x (8 * i)) 0xffL)))
  done

let xor_block state block =
  for i = 0 to (String.length block / 8) - 1 do
    state.(i) <- Int64.logxor state.(i) (load64_le block (8 * i))
  done

let sponge_with ~permute ~rate ~suffix ~output_length input =
  let state = Array.make 25 0L in
  let full_blocks = String.length input / rate in
  for block = 0 to full_blocks - 1 do
    xor_block state (String.sub input (block * rate) rate);
    permute state
  done;
  let rem = String.length input mod rate in
  let tail = Bytes.make rate '\000' in
  Bytes.blit_string input (full_blocks * rate) tail 0 rem;
  Bytes.set tail rem (Char.unsafe_chr suffix);
  Bytes.set tail (rate - 1)
    (Char.unsafe_chr (Char.code (Bytes.get tail (rate - 1)) lor 0x80));
  xor_block state (Bytes.unsafe_to_string tail);
  permute state;
  let out = Bytes.create output_length in
  let produced = ref 0 in
  while !produced < output_length do
    let take = min rate (output_length - !produced) in
    let block = Bytes.create rate in
    for i = 0 to (rate / 8) - 1 do
      store64_le block (8 * i) state.(i)
    done;
    Bytes.blit block 0 out !produced take;
    produced := !produced + take;
    if !produced < output_length then permute state
  done;
  Bytes.fill tail 0 rate '\000';
  Bytes.unsafe_to_string out

let sponge ~rate ~suffix ~output_length input =
  sponge_with ~permute ~rate ~suffix ~output_length input

let shake128 ~output_length input = sponge ~rate:168 ~suffix:0x1f ~output_length input
let shake256 ~output_length input = sponge ~rate:136 ~suffix:0x1f ~output_length input

let get_u32_be s off =
  let byte i = Int32.of_int (Char.code (String.unsafe_get s (off + i))) in
  Int32.logor (Int32.shift_left (byte 0) 24)
    (Int32.logor (Int32.shift_left (byte 1) 16)
       (Int32.logor (Int32.shift_left (byte 2) 8) (byte 3)))

let set_u32_be b off x =
  Bytes.unsafe_set b off
    (Char.unsafe_chr
       (Int32.to_int (Int32.logand (Int32.shift_right_logical x 24) 0xffl)));
  Bytes.unsafe_set b (off + 1)
    (Char.unsafe_chr
       (Int32.to_int (Int32.logand (Int32.shift_right_logical x 16) 0xffl)));
  Bytes.unsafe_set b (off + 2)
    (Char.unsafe_chr
       (Int32.to_int (Int32.logand (Int32.shift_right_logical x 8) 0xffl)));
  Bytes.unsafe_set b (off + 3)
    (Char.unsafe_chr (Int32.to_int (Int32.logand x 0xffl)))

let rotr32 x n =
  Int32.logor (Int32.shift_right_logical x n) (Int32.shift_left x (32 - n))

let sha256_constants =
  [|
    0x428a2f98l; 0x71374491l; 0xb5c0fbcfl; 0xe9b5dba5l;
    0x3956c25bl; 0x59f111f1l; 0x923f82a4l; 0xab1c5ed5l;
    0xd807aa98l; 0x12835b01l; 0x243185bel; 0x550c7dc3l;
    0x72be5d74l; 0x80deb1fel; 0x9bdc06a7l; 0xc19bf174l;
    0xe49b69c1l; 0xefbe4786l; 0x0fc19dc6l; 0x240ca1ccl;
    0x2de92c6fl; 0x4a7484aal; 0x5cb0a9dcl; 0x76f988dal;
    0x983e5152l; 0xa831c66dl; 0xb00327c8l; 0xbf597fc7l;
    0xc6e00bf3l; 0xd5a79147l; 0x06ca6351l; 0x14292967l;
    0x27b70a85l; 0x2e1b2138l; 0x4d2c6dfcl; 0x53380d13l;
    0x650a7354l; 0x766a0abbl; 0x81c2c92el; 0x92722c85l;
    0xa2bfe8a1l; 0xa81a664bl; 0xc24b8b70l; 0xc76c51a3l;
    0xd192e819l; 0xd6990624l; 0xf40e3585l; 0x106aa070l;
    0x19a4c116l; 0x1e376c08l; 0x2748774cl; 0x34b0bcb5l;
    0x391c0cb3l; 0x4ed8aa4al; 0x5b9cca4fl; 0x682e6ff3l;
    0x748f82eel; 0x78a5636fl; 0x84c87814l; 0x8cc70208l;
    0x90befffal; 0xa4506cebl; 0xbef9a3f7l; 0xc67178f2l;
  |]

let sha256 input =
  let input_length = String.length input in
  let padded_length = ((input_length + 9 + 63) / 64) * 64 in
  let padded = Bytes.make padded_length '\000' in
  Bytes.blit_string input 0 padded 0 input_length;
  Bytes.unsafe_set padded input_length '\x80';
  let bit_length = Int64.mul (Int64.of_int input_length) 8L in
  for i = 0 to 7 do
    Bytes.unsafe_set padded (padded_length - 1 - i)
      (Char.unsafe_chr
         (Int64.to_int
            (Int64.logand (Int64.shift_right_logical bit_length (8 * i)) 0xffL)))
  done;
  let h =
    [|
      0x6a09e667l; 0xbb67ae85l; 0x3c6ef372l; 0xa54ff53al;
      0x510e527fl; 0x9b05688cl; 0x1f83d9abl; 0x5be0cd19l;
    |]
  in
  let w = Array.make 64 0l in
  for block = 0 to (padded_length / 64) - 1 do
    let base = block * 64 in
    for i = 0 to 15 do
      w.(i) <- get_u32_be (Bytes.unsafe_to_string padded) (base + (4 * i))
    done;
    for i = 16 to 63 do
      let x = w.(i - 15) and y = w.(i - 2) in
      let s0 =
        Int32.logxor (rotr32 x 7)
          (Int32.logxor (rotr32 x 18) (Int32.shift_right_logical x 3))
      and s1 =
        Int32.logxor (rotr32 y 17)
          (Int32.logxor (rotr32 y 19) (Int32.shift_right_logical y 10))
      in
      w.(i) <- Int32.add (Int32.add w.(i - 16) s0) (Int32.add w.(i - 7) s1)
    done;
    let a = ref h.(0) and b = ref h.(1) and c = ref h.(2) and d = ref h.(3)
    and e = ref h.(4) and f = ref h.(5) and g = ref h.(6) and hh = ref h.(7) in
    for i = 0 to 63 do
      let s1 = Int32.logxor (rotr32 !e 6) (Int32.logxor (rotr32 !e 11) (rotr32 !e 25)) in
      let ch = Int32.logxor (Int32.logand !e !f) (Int32.logand (Int32.lognot !e) !g) in
      let t1 =
        Int32.add !hh
          (Int32.add s1 (Int32.add ch (Int32.add sha256_constants.(i) w.(i))))
      in
      let s0 = Int32.logxor (rotr32 !a 2) (Int32.logxor (rotr32 !a 13) (rotr32 !a 22)) in
      let maj =
        Int32.logxor (Int32.logand !a !b)
          (Int32.logxor (Int32.logand !a !c) (Int32.logand !b !c))
      in
      let t2 = Int32.add s0 maj in
      hh := !g; g := !f; f := !e; e := Int32.add !d t1;
      d := !c; c := !b; b := !a; a := Int32.add t1 t2
    done;
    h.(0) <- Int32.add h.(0) !a; h.(1) <- Int32.add h.(1) !b;
    h.(2) <- Int32.add h.(2) !c; h.(3) <- Int32.add h.(3) !d;
    h.(4) <- Int32.add h.(4) !e; h.(5) <- Int32.add h.(5) !f;
    h.(6) <- Int32.add h.(6) !g; h.(7) <- Int32.add h.(7) !hh
  done;
  let result = Bytes.create 32 in
  Array.iteri (fun i x -> set_u32_be result (4 * i) x) h;
  Bytes.unsafe_to_string result

let get_u64_be s off =
  let r = ref 0L in
  for i = 0 to 7 do
    r :=
      Int64.logor (Int64.shift_left !r 8)
        (Int64.of_int (Char.code (String.unsafe_get s (off + i))))
  done;
  !r

let set_u64_be b off x =
  for i = 0 to 7 do
    Bytes.unsafe_set b (off + i)
      (Char.unsafe_chr
         (Int64.to_int
            (Int64.logand (Int64.shift_right_logical x (8 * (7 - i))) 0xffL)))
  done

let rotr64 x n =
  Int64.logor (Int64.shift_right_logical x n) (Int64.shift_left x (64 - n))

let sha512_constants =
  [|
    0x428a2f98d728ae22L; 0x7137449123ef65cdL; 0xb5c0fbcfec4d3b2fL; 0xe9b5dba58189dbbcL;
    0x3956c25bf348b538L; 0x59f111f1b605d019L; 0x923f82a4af194f9bL; 0xab1c5ed5da6d8118L;
    0xd807aa98a3030242L; 0x12835b0145706fbeL; 0x243185be4ee4b28cL; 0x550c7dc3d5ffb4e2L;
    0x72be5d74f27b896fL; 0x80deb1fe3b1696b1L; 0x9bdc06a725c71235L; 0xc19bf174cf692694L;
    0xe49b69c19ef14ad2L; 0xefbe4786384f25e3L; 0x0fc19dc68b8cd5b5L; 0x240ca1cc77ac9c65L;
    0x2de92c6f592b0275L; 0x4a7484aa6ea6e483L; 0x5cb0a9dcbd41fbd4L; 0x76f988da831153b5L;
    0x983e5152ee66dfabL; 0xa831c66d2db43210L; 0xb00327c898fb213fL; 0xbf597fc7beef0ee4L;
    0xc6e00bf33da88fc2L; 0xd5a79147930aa725L; 0x06ca6351e003826fL; 0x142929670a0e6e70L;
    0x27b70a8546d22ffcL; 0x2e1b21385c26c926L; 0x4d2c6dfc5ac42aedL; 0x53380d139d95b3dfL;
    0x650a73548baf63deL; 0x766a0abb3c77b2a8L; 0x81c2c92e47edaee6L; 0x92722c851482353bL;
    0xa2bfe8a14cf10364L; 0xa81a664bbc423001L; 0xc24b8b70d0f89791L; 0xc76c51a30654be30L;
    0xd192e819d6ef5218L; 0xd69906245565a910L; 0xf40e35855771202aL; 0x106aa07032bbd1b8L;
    0x19a4c116b8d2d0c8L; 0x1e376c085141ab53L; 0x2748774cdf8eeb99L; 0x34b0bcb5e19b48a8L;
    0x391c0cb3c5c95a63L; 0x4ed8aa4ae3418acbL; 0x5b9cca4f7763e373L; 0x682e6ff3d6b2b8a3L;
    0x748f82ee5defb2fcL; 0x78a5636f43172f60L; 0x84c87814a1f0ab72L; 0x8cc702081a6439ecL;
    0x90befffa23631e28L; 0xa4506cebde82bde9L; 0xbef9a3f7b2c67915L; 0xc67178f2e372532bL;
    0xca273eceea26619cL; 0xd186b8c721c0c207L; 0xeada7dd6cde0eb1eL; 0xf57d4f7fee6ed178L;
    0x06f067aa72176fbaL; 0x0a637dc5a2c898a6L; 0x113f9804bef90daeL; 0x1b710b35131c471bL;
    0x28db77f523047d84L; 0x32caab7b40c72493L; 0x3c9ebe0a15c9bebcL; 0x431d67c49c100d4cL;
    0x4cc5d4becb3e42b6L; 0x597f299cfc657e2aL; 0x5fcb6fab3ad6faecL; 0x6c44198c4a475817L;
  |]

let sha512 input =
  let input_length = String.length input in
  let padded_length = ((input_length + 17 + 127) / 128) * 128 in
  let padded = Bytes.make padded_length '\000' in
  Bytes.blit_string input 0 padded 0 input_length;
  Bytes.unsafe_set padded input_length '\x80';
  let bit_length = Int64.mul (Int64.of_int input_length) 8L in
  set_u64_be padded (padded_length - 8) bit_length;
  let h =
    [|
      0x6a09e667f3bcc908L; 0xbb67ae8584caa73bL; 0x3c6ef372fe94f82bL; 0xa54ff53a5f1d36f1L;
      0x510e527fade682d1L; 0x9b05688c2b3e6c1fL; 0x1f83d9abfb41bd6bL; 0x5be0cd19137e2179L;
    |]
  in
  let w = Array.make 80 0L in
  for block = 0 to (padded_length / 128) - 1 do
    let base = block * 128 in
    for i = 0 to 15 do
      w.(i) <- get_u64_be (Bytes.unsafe_to_string padded) (base + (8 * i))
    done;
    for i = 16 to 79 do
      let x = w.(i - 15) and y = w.(i - 2) in
      let s0 = Int64.logxor (rotr64 x 1) (Int64.logxor (rotr64 x 8) (Int64.shift_right_logical x 7))
      and s1 = Int64.logxor (rotr64 y 19) (Int64.logxor (rotr64 y 61) (Int64.shift_right_logical y 6)) in
      w.(i) <- Int64.add (Int64.add w.(i - 16) s0) (Int64.add w.(i - 7) s1)
    done;
    let a = ref h.(0) and b = ref h.(1) and c = ref h.(2) and d = ref h.(3)
    and e = ref h.(4) and f = ref h.(5) and g = ref h.(6) and hh = ref h.(7) in
    for i = 0 to 79 do
      let s1 = Int64.logxor (rotr64 !e 14) (Int64.logxor (rotr64 !e 18) (rotr64 !e 41)) in
      let ch = Int64.logxor (Int64.logand !e !f) (Int64.logand (Int64.lognot !e) !g) in
      let t1 = Int64.add !hh (Int64.add s1 (Int64.add ch (Int64.add sha512_constants.(i) w.(i)))) in
      let s0 = Int64.logxor (rotr64 !a 28) (Int64.logxor (rotr64 !a 34) (rotr64 !a 39)) in
      let maj = Int64.logxor (Int64.logand !a !b)
          (Int64.logxor (Int64.logand !a !c) (Int64.logand !b !c)) in
      let t2 = Int64.add s0 maj in
      hh := !g; g := !f; f := !e; e := Int64.add !d t1;
      d := !c; c := !b; b := !a; a := Int64.add t1 t2
    done;
    h.(0) <- Int64.add h.(0) !a; h.(1) <- Int64.add h.(1) !b;
    h.(2) <- Int64.add h.(2) !c; h.(3) <- Int64.add h.(3) !d;
    h.(4) <- Int64.add h.(4) !e; h.(5) <- Int64.add h.(5) !f;
    h.(6) <- Int64.add h.(6) !g; h.(7) <- Int64.add h.(7) !hh
  done;
  let result = Bytes.create 64 in
  Array.iteri (fun i x -> set_u64_be result (8 * i) x) h;
  Bytes.unsafe_to_string result

let xor_with byte s =
  String.init (String.length s) (fun i ->
      Char.unsafe_chr (Char.code (String.unsafe_get s i) lxor byte))

let hmac ~block_size hash key message =
  let key = if String.length key > block_size then hash key else key in
  let key = key ^ String.make (block_size - String.length key) '\000' in
  hash (xor_with 0x5c key ^ hash (xor_with 0x36 key ^ message))

let hmac_sha256 key message = hmac ~block_size:64 sha256 key message
let hmac_sha512 key message = hmac ~block_size:128 sha512 key message

let mgf1 hash ~digest_size ~output_length seed =
  if output_length < 0 then invalid_arg "MGF1: negative mask length";
  (* RFC 8017 B.2.1 limits the mask to 2^32 blocks, the range of the 4-byte
     counter. Shift in two steps: a single [lsr 32] is a no-op under
     js_of_ocaml, where no reachable length comes near the limit anyway. *)
  if output_length > 0
     && (((output_length - 1) / digest_size) lsr 16) lsr 16 <> 0
  then invalid_arg "MGF1: mask too long";
  let blocks = (output_length + digest_size - 1) / digest_size in
  let result = Buffer.create (blocks * digest_size) in
  for counter = 0 to blocks - 1 do
    let encoded = Bytes.create 4 in
    set_u32_be encoded 0 (Int32.of_int counter);
    Buffer.add_string result (hash (seed ^ Bytes.unsafe_to_string encoded))
  done;
  String.sub (Buffer.contents result) 0 output_length

let mgf1_sha256 ~output_length seed = mgf1 sha256 ~digest_size:32 ~output_length seed
let mgf1_sha512 ~output_length seed = mgf1 sha512 ~digest_size:64 ~output_length seed
