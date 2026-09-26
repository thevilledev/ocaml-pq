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

let sha3_256 input = sponge ~rate:136 ~suffix:0x06 ~output_length:32 input
let sha3_512 input = sponge ~rate:72 ~suffix:0x06 ~output_length:64 input
let shake128 ~output_length input = sponge ~rate:168 ~suffix:0x1f ~output_length input
let shake256 ~output_length input = sponge ~rate:136 ~suffix:0x1f ~output_length input

(* TurboSHAKE (RFC 9861): the sponge of SHAKE over KECCAK-p[1600, 12], with the
   domain separation byte [domain] as its suffix. *)
let turboshake128 ~domain ~output_length input =
  sponge_with ~permute:(permute_from 12) ~rate:168 ~suffix:domain ~output_length input
let turboshake256 ~domain ~output_length input =
  sponge_with ~permute:(permute_from 12) ~rate:136 ~suffix:domain ~output_length input
