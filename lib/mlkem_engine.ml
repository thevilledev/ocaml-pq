type error =
  | Invalid_length of { what : string; expected : int; actual : int }
  | Invalid_encoding of string

let pp_error ppf = function
  | Invalid_length { what; expected; actual } ->
      Format.fprintf ppf "%s has length %d, expected %d" what actual expected
  | Invalid_encoding message -> Format.pp_print_string ppf message

module type PARAMETERS = sig
  val k : int
  val eta1 : int
  val eta2 : int
  val du : int
  val dv : int
end

module type S = sig
  type nonrec error = error =
    | Invalid_length of { what : string; expected : int; actual : int }
    | Invalid_encoding of string

  val pp_error : Format.formatter -> error -> unit

  type encapsulation_key
  type decapsulation_key
  type ciphertext
  type shared_secret

  val seed_size : int
  val encapsulation_key_size : int
  val expanded_decapsulation_key_size : int
  val ciphertext_size : int
  val shared_secret_size : int

  val decapsulation_key_of_seed : string -> (decapsulation_key, error) result
  val decapsulation_key_to_seed : decapsulation_key -> string option
  val decapsulation_key_of_expanded : string -> (decapsulation_key, error) result
  val decapsulation_key_to_expanded : decapsulation_key -> string
  val encapsulation_key_of_decapsulation_key : decapsulation_key -> encapsulation_key
  val encapsulation_key_of_octets : string -> (encapsulation_key, error) result
  val encapsulation_key_to_octets : encapsulation_key -> string
  val ciphertext_of_octets : string -> (ciphertext, error) result
  val ciphertext_to_octets : ciphertext -> string
  val shared_secret_to_octets : shared_secret -> string

  val keygen_internal : d:string -> z:string -> (decapsulation_key, error) result
  val encapsulate_internal : encapsulation_key -> randomness:string ->
    (ciphertext * shared_secret, error) result
  val decapsulate : decapsulation_key -> ciphertext -> shared_secret

  val ct_equal_for_testing : string -> string -> int
end

module Make (P : PARAMETERS) = struct
type nonrec error = error =
  | Invalid_length of { what : string; expected : int; actual : int }
  | Invalid_encoding of string

let pp_error = pp_error

let n = 256
let q = 3329
let k = P.k
let eta1 = P.eta1
let eta2 = P.eta2
let du = P.du
let dv = P.dv
let encoding_size_12 = 384
let encoding_size_u = n * du / 8
let encoding_size_v = n * dv / 8
let seed_size = 64
let encapsulation_key_size = (k * encoding_size_12) + 32
let expanded_decapsulation_key_size =
  (k * encoding_size_12) + encapsulation_key_size + 64
let ciphertext_size = (k * encoding_size_u) + encoding_size_v
let shared_secret_size = 32

(** Polynomials use canonical representatives from zero through [q - 1]. Secret
    operations below use fixed bounds and arithmetic masking. *)
type poly = int array

type encapsulation_key = {
  t : poly array;
  a : poly array array;
  rho : string;
  h : string;
  encoded : string;
}

type decapsulation_key = {
  seed : string option;
  z : string;
  s : poly array;
  ek : encapsulation_key;
}

type ciphertext = string
type shared_secret = string

let invalid_length what expected actual =
  Error (Invalid_length { what; expected; actual })

let get_u8 s i = Char.code (String.unsafe_get s i)
let set_u8 b i x = Bytes.unsafe_set b i (Char.unsafe_chr (x land 0xff))

let field_reduce_once a =
  let x = a - q in
  let sign = Int32.to_int (Int32.shift_right (Int32.of_int x) 31) in
  x + (sign land q)

let field_add a b = field_reduce_once (a + b)
let field_sub a b = field_reduce_once (a - b + q)

let field_reduce a =
  let open Int64 in
  let a64 = of_int a in
  let quotient = shift_right_logical (mul a64 5039L) 24 in
  field_reduce_once (to_int (sub a64 (mul quotient 3329L)))

let field_mul a b = field_reduce (a * b)

let field_mul_sub a b c = field_reduce (a * (b - c + q))

let field_add_mul a b c d = field_reduce ((a * b) + (c * d))

let compress x d =
  let open Int64 in
  let dividend = shift_left (of_int x) d in
  let quotient = shift_right_logical (mul dividend 5039L) 24 in
  let remainder = sub dividend (mul quotient 3329L) in
  let inc threshold =
    to_int (logand (shift_right_logical (sub (of_int threshold) remainder) 63) 1L)
  in
  (to_int quotient + inc (q / 2) + inc (q + (q / 2))) land ((1 lsl d) - 1)

let decompress y d =
  let dividend = y * q in
  (dividend lsr d) + ((dividend lsr (d - 1)) land 1)

let poly_zero () = Array.make n 0

let poly_add a b =
  Array.init n (fun i -> field_add (Array.unsafe_get a i) (Array.unsafe_get b i))

let poly_sub a b =
  Array.init n (fun i -> field_sub (Array.unsafe_get a i) (Array.unsafe_get b i))

let zetas =
  [|
    1;1729;2580;3289;2642;630;1897;848;1062;1919;193;797;2786;3260;569;1746;
    296;2447;1339;1476;3046;56;2240;1333;1426;2094;535;2882;2393;2879;1974;821;
    289;331;3253;1756;1197;2304;2277;2055;650;1977;2513;632;2865;33;1320;1915;
    2319;1435;807;452;1438;2868;1534;2402;2647;2617;1481;648;2474;3110;1227;910;
    17;2761;583;2649;1637;723;2288;1100;1409;2662;3281;233;756;2156;3015;3050;
    1703;1651;2789;1789;1847;952;1461;2687;939;2308;2437;2388;733;2337;268;641;
    1584;2298;2037;3220;375;2549;2090;1645;1063;319;2773;757;2099;561;2466;2594;
    2804;1092;403;1026;1143;2150;2775;886;1722;1212;1874;1029;2110;2935;885;2154;
  |]

let gammas =
  [|
    17;3312;2761;568;583;2746;2649;680;1637;1692;723;2606;2288;1041;1100;2229;
    1409;1920;2662;667;3281;48;233;3096;756;2573;2156;1173;3015;314;3050;279;
    1703;1626;1651;1678;2789;540;1789;1540;1847;1482;952;2377;1461;1868;2687;642;
    939;2390;2308;1021;2437;892;2388;941;733;2596;2337;992;268;3061;641;2688;
    1584;1745;2298;1031;2037;1292;3220;109;375;2954;2549;780;2090;1239;1645;1684;
    1063;2266;319;3010;2773;556;757;2572;2099;1230;561;2768;2466;863;2594;735;
    2804;525;1092;2237;403;2926;1026;2303;1143;2186;2150;1179;2775;554;886;2443;
    1722;1607;1212;2117;1874;1455;1029;2300;2110;1219;2935;394;885;2444;2154;1175;
  |]

(** FIPS 203 Algorithms 9 and 10. The loop schedule and table indices are
    independent of polynomial coefficients. *)
let ntt input =
  let f = Array.copy input in
  let zeta_index = ref 1 in
  let len = ref 128 in
  while !len >= 2 do
    let start = ref 0 in
    while !start < n do
      let zeta = Array.unsafe_get zetas !zeta_index in
      incr zeta_index;
      for j = !start to !start + !len - 1 do
        let t = field_mul zeta (Array.unsafe_get f (j + !len)) in
        let fj = Array.unsafe_get f j in
        Array.unsafe_set f (j + !len) (field_sub fj t);
        Array.unsafe_set f j (field_add fj t)
      done;
      start := !start + (2 * !len)
    done;
    len := !len / 2
  done;
  f

let inverse_ntt input =
  let f = Array.copy input in
  let zeta_index = ref 127 in
  let len = ref 2 in
  while !len <= 128 do
    let start = ref 0 in
    while !start < n do
      let zeta = Array.unsafe_get zetas !zeta_index in
      decr zeta_index;
      for j = !start to !start + !len - 1 do
        let t = Array.unsafe_get f j in
        let upper = Array.unsafe_get f (j + !len) in
        Array.unsafe_set f j (field_add t upper);
        Array.unsafe_set f (j + !len) (field_mul_sub zeta upper t)
      done;
      start := !start + (2 * !len)
    done;
    len := !len * 2
  done;
  for i = 0 to n - 1 do
    Array.unsafe_set f i (field_mul (Array.unsafe_get f i) 3303)
  done;
  f

let ntt_mul f g =
  let h = poly_zero () in
  for i = 0 to 127 do
    let j = 2 * i in
    let a0 = Array.unsafe_get f j and a1 = Array.unsafe_get f (j + 1) in
    let b0 = Array.unsafe_get g j and b1 = Array.unsafe_get g (j + 1) in
    Array.unsafe_set h j
      (field_add_mul a0 b0 (field_mul a1 b1) (Array.unsafe_get gammas i));
    Array.unsafe_set h (j + 1) (field_add_mul a0 b1 a1 b0)
  done;
  h

let encode_12 f =
  let out = Bytes.create encoding_size_12 in
  for i = 0 to 127 do
    let a = Array.unsafe_get f (2 * i) in
    let b = Array.unsafe_get f ((2 * i) + 1) in
    let x = a lor (b lsl 12) in
    set_u8 out (3 * i) x;
    set_u8 out ((3 * i) + 1) (x lsr 8);
    set_u8 out ((3 * i) + 2) (x lsr 16)
  done;
  Bytes.unsafe_to_string out

let decode_12 ~what s off =
  let out = poly_zero () in
  let valid = ref true in
  for i = 0 to 127 do
    let p = off + (3 * i) in
    let x = get_u8 s p lor (get_u8 s (p + 1) lsl 8) lor (get_u8 s (p + 2) lsl 16) in
    let a = x land 0xfff and b = x lsr 12 in
    valid := !valid && a < q && b < q;
    Array.unsafe_set out (2 * i) a;
    Array.unsafe_set out ((2 * i) + 1) b
  done;
  if !valid then Ok out else Error (Invalid_encoding (what ^ " contains an unreduced coefficient"))

let encode_compressed d f =
  let output_length = n * d / 8 in
  let out = Bytes.make output_length '\000' in
  let accumulator = ref 0L and bits = ref 0 and pos = ref 0 in
  for i = 0 to n - 1 do
    accumulator := Int64.logor !accumulator
        (Int64.shift_left (Int64.of_int (compress (Array.unsafe_get f i) d)) !bits);
    bits := !bits + d;
    while !bits >= 8 do
      set_u8 out !pos (Int64.to_int !accumulator);
      incr pos;
      accumulator := Int64.shift_right_logical !accumulator 8;
      bits := !bits - 8
    done
  done;
  Bytes.unsafe_to_string out

let decode_compressed d s off =
  let out = poly_zero () in
  let mask = (1 lsl d) - 1 in
  let accumulator = ref 0L and bits = ref 0 and pos = ref off in
  for i = 0 to n - 1 do
    while !bits < d do
      accumulator := Int64.logor !accumulator
          (Int64.shift_left (Int64.of_int (get_u8 s !pos)) !bits);
      incr pos;
      bits := !bits + 8
    done;
    Array.unsafe_set out i (decompress (Int64.to_int !accumulator land mask) d);
    accumulator := Int64.shift_right_logical !accumulator d;
    bits := !bits - d
  done;
  out

let encode_message f = encode_compressed 1 f
let decode_message s = decode_compressed 1 s 0

(** FIPS 203 Algorithm 8. The bit schedule is fixed by the public parameter
    [eta]. *)
let sample_cbd eta seed nonce =
  let stream = Keccak.shake256 ~output_length:(64 * eta)
      (seed ^ String.make 1 (Char.unsafe_chr nonce)) in
  let out = poly_zero () in
  for i = 0 to 255 do
    let bit offset =
      let index = (2 * eta * i) + offset in
      (get_u8 stream (index lsr 3) lsr (index land 7)) land 1
    in
    let a = ref 0 and b = ref 0 in
    for j = 0 to eta - 1 do
      a := !a + bit j;
      b := !b + bit (eta + j)
    done;
    Array.unsafe_set out i (field_sub !a !b)
  done;
  out

let sample_ntt rho i j =
  let input = rho ^ String.make 1 (Char.unsafe_chr i) ^ String.make 1 (Char.unsafe_chr j) in
  (* Recompute a longer prefix only in the exceptionally unlikely event that
     the initial XOF prefix does not contain 256 reduced coefficients. The
     amount of work depends only on public [rho]. *)
  let rec draw output_length =
    let stream = Keccak.shake128 ~output_length input in
    let out = poly_zero () in
    let count = ref 0 and off = ref 0 in
    while !count < n && !off + 2 < output_length do
      let d1 = (get_u8 stream !off lor (get_u8 stream (!off + 1) lsl 8)) land 0xfff in
      let d2 = (get_u8 stream (!off + 1) lor (get_u8 stream (!off + 2) lsl 8)) lsr 4 in
      off := !off + 3;
      if d1 < q && !count < n then begin
        Array.unsafe_set out !count d1;
        incr count
      end;
      if d2 < q && !count < n then begin
        Array.unsafe_set out !count d2;
        incr count
      end
    done;
    if !count = n then out else draw (output_length * 2)
  in
  draw 840

let encode_ek t rho =
  let out = Bytes.create encapsulation_key_size in
  for i = 0 to k - 1 do
    Bytes.blit_string (encode_12 (Array.unsafe_get t i)) 0 out (i * encoding_size_12) encoding_size_12
  done;
  Bytes.blit_string rho 0 out (k * encoding_size_12) 32;
  Bytes.unsafe_to_string out

let parse_ek encoded =
  if String.length encoded <> encapsulation_key_size then
    invalid_length "encapsulation key" encapsulation_key_size (String.length encoded)
  else
    let rec parse acc i =
      if i = k then Ok (Array.of_list (List.rev acc))
      else match decode_12 ~what:"encapsulation key" encoded (i * encoding_size_12) with
        | Error _ as e -> e
        | Ok p -> parse (p :: acc) (i + 1)
    in
    match parse [] 0 with
    | Error _ as e -> e
    | Ok t ->
        let rho = String.sub encoded (k * encoding_size_12) 32 in
        let a = Array.init k (fun row -> Array.init k (fun col -> sample_ntt rho col row)) in
        Ok { t; a; rho; h = Keccak.sha3_256 encoded; encoded }

let keygen_internal ~d ~z =
  if String.length d <> 32 then invalid_length "key-generation seed d" 32 (String.length d)
  else if String.length z <> 32 then invalid_length "implicit-rejection seed z" 32 (String.length z)
  else
    let expanded = Keccak.sha3_512 (d ^ String.make 1 (Char.unsafe_chr k)) in
    let rho = String.sub expanded 0 32 and sigma = String.sub expanded 32 32 in
    let a = Array.init k (fun row -> Array.init k (fun col -> sample_ntt rho col row)) in
    let nonce = ref 0 in
    let sample_secret () =
      let p = ntt (sample_cbd eta1 sigma !nonce) in
      incr nonce;
      p
    in
    let s = Array.init k (fun _ -> sample_secret ()) in
    let e = Array.init k (fun _ -> sample_secret ()) in
    let t = Array.init k (fun row ->
        let total = ref (Array.unsafe_get e row) in
        for col = 0 to k - 1 do
          total := poly_add !total
              (ntt_mul (Array.unsafe_get (Array.unsafe_get a row) col) (Array.unsafe_get s col))
        done;
        !total)
    in
    let encoded = encode_ek t rho in
    let ek = { t; a; rho; h = Keccak.sha3_256 encoded; encoded } in
    Ok { seed = Some (d ^ z); z; s; ek }

let decapsulation_key_of_seed seed =
  if String.length seed <> seed_size then
    invalid_length "decapsulation key seed" seed_size (String.length seed)
  else keygen_internal ~d:(String.sub seed 0 32) ~z:(String.sub seed 32 32)

let decapsulation_key_to_seed dk = Option.map (fun x -> String.sub x 0 (String.length x)) dk.seed

let encapsulation_key_of_decapsulation_key dk = dk.ek
let encapsulation_key_of_octets = parse_ek
let encapsulation_key_to_octets ek = String.sub ek.encoded 0 encapsulation_key_size

let decapsulation_key_to_expanded dk =
  let out = Bytes.create expanded_decapsulation_key_size in
  for i = 0 to k - 1 do
    Bytes.blit_string (encode_12 (Array.unsafe_get dk.s i)) 0 out (i * encoding_size_12) encoding_size_12
  done;
  Bytes.blit_string dk.ek.encoded 0 out (k * encoding_size_12) encapsulation_key_size;
  Bytes.blit_string dk.ek.h 0 out (k * encoding_size_12 + encapsulation_key_size) 32;
  Bytes.blit_string dk.z 0 out (expanded_decapsulation_key_size - 32) 32;
  Bytes.unsafe_to_string out

let ct_equal a b =
  let diff = ref 0 in
  for i = 0 to String.length a - 1 do
    diff := !diff lor (get_u8 a i lxor get_u8 b i)
  done;
  let d = Int32.of_int !diff in
  Int32.to_int (Int32.logand (Int32.shift_right_logical (Int32.logor d (Int32.neg d)) 31) 1l) lxor 1

(* [ct_equal] reads [b] with [unsafe_get] at [a]'s length. Lengths are public,
   so compare them here and let only equal-length inputs reach the
   constant-time loop, whose native-code shape CI reviews. *)
let ct_equal_checked a b =
  if String.length a <> String.length b then 0 else ct_equal a b

let ct_equal_for_testing = ct_equal_checked

let decapsulation_key_of_expanded encoded =
  if String.length encoded <> expanded_decapsulation_key_size then
    invalid_length "expanded decapsulation key" expanded_decapsulation_key_size (String.length encoded)
  else
    let rec parse_s acc i =
      if i = k then Ok (Array.of_list (List.rev acc))
      else match decode_12 ~what:"expanded decapsulation key" encoded (i * encoding_size_12) with
        | Error _ as e -> e
        | Ok p -> parse_s (p :: acc) (i + 1)
    in
    match parse_s [] 0 with
    | Error _ as e -> e
    | Ok s ->
        let ek_offset = k * encoding_size_12 in
        let ek_bytes = String.sub encoded ek_offset encapsulation_key_size in
        begin match parse_ek ek_bytes with
        | Error _ as e -> e
        | Ok ek ->
            let h_offset = ek_offset + encapsulation_key_size in
            let h = String.sub encoded h_offset 32 in
            if ct_equal_checked h ek.h <> 1 then Error (Invalid_encoding "expanded decapsulation key has inconsistent H(ek)")
            else
              let z = String.sub encoded (h_offset + 32) 32 in
              Ok { seed = None; z; s; ek }
        end

let ciphertext_of_octets encoded =
  if String.length encoded <> ciphertext_size then
    invalid_length "ciphertext" ciphertext_size (String.length encoded)
  else Ok (String.sub encoded 0 ciphertext_size)

let ciphertext_to_octets c = String.sub c 0 ciphertext_size
let shared_secret_to_octets s = String.sub s 0 shared_secret_size

let pke_encrypt ek message randomness =
  let nonce = ref 0 in
  let sample_ntt_secret () =
    let p = ntt (sample_cbd eta1 randomness !nonce) in
    incr nonce;
    p
  in
  let sample_ring_secret () =
    let p = sample_cbd eta2 randomness !nonce in
    incr nonce;
    p
  in
  let r = Array.init k (fun _ -> sample_ntt_secret ()) in
  let e1 = Array.init k (fun _ -> sample_ring_secret ()) in
  let e2 = sample_ring_secret () in
  let u = Array.init k (fun col ->
      let total = ref (Array.unsafe_get e1 col) in
      for row = 0 to k - 1 do
        total := poly_add !total
            (inverse_ntt
               (ntt_mul (Array.unsafe_get (Array.unsafe_get ek.a row) col)
                  (Array.unsafe_get r row)))
      done;
      !total)
  in
  let v_ntt = ref (poly_zero ()) in
  for i = 0 to k - 1 do
    v_ntt := poly_add !v_ntt (ntt_mul (Array.unsafe_get ek.t i) (Array.unsafe_get r i))
  done;
  let v = poly_add (poly_add (inverse_ntt !v_ntt) e2) (decode_message message) in
  let out = Bytes.create ciphertext_size in
  for i = 0 to k - 1 do
    Bytes.blit_string (encode_compressed du (Array.unsafe_get u i)) 0 out
      (i * encoding_size_u) encoding_size_u
  done;
  Bytes.blit_string (encode_compressed dv v) 0 out (k * encoding_size_u) encoding_size_v;
  Bytes.unsafe_to_string out

let encapsulate_internal ek ~randomness =
  if String.length randomness <> 32 then
    invalid_length "encapsulation randomness" 32 (String.length randomness)
  else
    let g = Keccak.sha3_512 (randomness ^ ek.h) in
    let secret = String.sub g 0 32 and coins = String.sub g 32 32 in
    Ok (pke_encrypt ek randomness coins, secret)

let pke_decrypt dk ciphertext =
  let u = Array.init k (fun i -> decode_compressed du ciphertext (i * encoding_size_u)) in
  let v = decode_compressed dv ciphertext (k * encoding_size_u) in
  let mask = ref (poly_zero ()) in
  for i = 0 to k - 1 do
    mask := poly_add !mask (ntt_mul (Array.unsafe_get dk.s i) (ntt (Array.unsafe_get u i)))
  done;
  encode_message (poly_sub v (inverse_ntt !mask))

let select_secret ~choose_left left right =
  let nz = choose_left lxor 1 in
  let mask = -nz in
  let out = Bytes.create shared_secret_size in
  for i = 0 to shared_secret_size - 1 do
    let l = get_u8 left i and r = get_u8 right i in
    set_u8 out i ((l land (lnot mask)) lor (r land mask))
  done;
  Bytes.unsafe_to_string out

let decapsulate dk ciphertext =
  let message = pke_decrypt dk ciphertext in
  let g = Keccak.sha3_512 (message ^ dk.ek.h) in
  let candidate = String.sub g 0 32 and coins = String.sub g 32 32 in
  let rejection = Keccak.shake256 ~output_length:32 (dk.z ^ ciphertext) in
  let expected = pke_encrypt dk.ek message coins in
  select_secret ~choose_left:(ct_equal_checked ciphertext expected) candidate rejection
end

module Mlkem512 = Make (struct
  let k = 2
  let eta1 = 3
  let eta2 = 2
  let du = 10
  let dv = 4
end)

module Mlkem768 = Make (struct
  let k = 3
  let eta1 = 2
  let eta2 = 2
  let du = 10
  let dv = 4
end)

module Mlkem1024 = Make (struct
  let k = 4
  let eta1 = 2
  let eta2 = 2
  let du = 11
  let dv = 5
end)
