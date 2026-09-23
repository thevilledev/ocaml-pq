type error =
  | Invalid_length of { what : string; expected : int; actual : int }
  | Invalid_encoding of string
  | Context_too_long of int
  | Signing_failed

let pp_error formatter = function
  | Invalid_length { what; expected; actual } ->
      Format.fprintf formatter "%s has length %d, expected %d" what actual expected
  | Invalid_encoding message -> Format.pp_print_string formatter message
  | Context_too_long length ->
      Format.fprintf formatter "context has length %d, expected at most 255" length
  | Signing_failed ->
      Format.pp_print_string formatter
        "ML-DSA rejection sampling exceeded the FIPS 204 iteration limit"

(* FIPS 204 IntegerToBytes(value, 2), the nonce encoding of ExpandA, ExpandS
   and ExpandMask. Every nonce the engine derives is below 2^16; reject
   anything else rather than truncate it into a repeated nonce. *)
let u16_le value =
  if value < 0 || value > 0xffff then
    invalid_arg (Printf.sprintf "ML-DSA: nonce %d does not fit in 16 bits" value);
  let bytes = Bytes.create 2 in
  Bytes.unsafe_set bytes 0 (Char.unsafe_chr (value land 0xff));
  Bytes.unsafe_set bytes 1 (Char.unsafe_chr (value lsr 8));
  Bytes.unsafe_to_string bytes

module type PARAMETERS = sig
  val name : string
  val k : int
  val l : int
  val eta : int
  val tau : int
  val gamma1 : int
  val gamma2 : int
  val omega : int
  val c_tilde_bytes : int
end

module type S = sig
  type nonrec error = error =
    | Invalid_length of { what : string; expected : int; actual : int }
    | Invalid_encoding of string
    | Context_too_long of int
    | Signing_failed

  val pp_error : Format.formatter -> error -> unit

  type signing_key
  type verification_key
  type signature

  val seed_size : int
  val signing_key_size : int
  val verification_key_size : int
  val signature_size : int

  val generate :
    random:(int -> string) -> unit -> signing_key * verification_key

  val signing_key_of_seed : string -> (signing_key, error) result
  val signing_key_to_seed : signing_key -> string option
  val signing_key_of_octets : string -> (signing_key, error) result
  val signing_key_to_octets : signing_key -> string

  val verification_key_of_signing_key : signing_key -> verification_key
  val verification_key_of_octets : string -> (verification_key, error) result
  val verification_key_to_octets : verification_key -> string

  val signature_of_octets : string -> (signature, error) result
  val signature_to_octets : signature -> string

  val sign :
    ?context:string ->
    random:(int -> string) ->
    signing_key ->
    message:string ->
    (signature, error) result

  val sign_deterministic :
    ?context:string -> signing_key -> message:string -> (signature, error) result

  val verify :
    ?context:string ->
    verification_key ->
    message:string ->
    signature ->
    bool
end

module type INTERNAL = sig
  include S

  val sign_internal_for_testing :
    signing_key ->
    formatted_message:string ->
    randomness:string ->
    (signature, error) result

  val sign_mu_for_testing :
    signing_key ->
    mu:string ->
    randomness:string ->
    (signature, error) result

  val verify_internal_for_testing :
    verification_key -> formatted_message:string -> signature -> bool

  val verify_mu_for_testing :
    verification_key -> mu:string -> signature -> bool

  val use_hint_for_testing : int -> int -> int

  val encode_signature_for_testing :
    c_tilde:string -> z:int array array -> hint:int array array -> string
end

module Make (P : PARAMETERS) : INTERNAL = struct
  type nonrec error = error =
    | Invalid_length of { what : string; expected : int; actual : int }
    | Invalid_encoding of string
    | Context_too_long of int
    | Signing_failed

  let pp_error = pp_error

  let q = 8_380_417
  let n = 256
  let d = 13
  let beta = P.tau * P.eta
  let seed_size = 32
  let tr_bytes = 64
  let eta_bits = if P.eta = 2 then 3 else 4
  let eta_packed_bytes = n * eta_bits / 8
  let t0_packed_bytes = 416
  let t1_packed_bytes = 320
  let z_bits = if P.gamma1 = 1 lsl 17 then 18 else 20
  let z_packed_bytes = n * z_bits / 8
  let w1_bits = if P.gamma2 = (q - 1) / 88 then 6 else 4
  let verification_key_size = seed_size + (P.k * t1_packed_bytes)

  let signing_key_size =
    (2 * seed_size) + tr_bytes
    + ((P.l + P.k) * eta_packed_bytes)
    + (P.k * t0_packed_bytes)

  let signature_size =
    P.c_tilde_bytes + (P.l * z_packed_bytes) + P.omega + P.k

  type poly = int array
  type polyvec = poly array

  type expanded_signing_key = {
    rho : string;
    key : string;
    tr : string;
    s1 : polyvec;
    s2 : polyvec;
    t0 : polyvec;
  }

  type verification_key = string

  type signing_key = {
    seed : string option;
    expanded_octets : string;
    expanded : expanded_signing_key;
    verification_key : verification_key;
  }

  type signature = string

  let invalid_length what expected value =
    Error (Invalid_length { what; expected; actual = String.length value })

  let get_u8 string index = Char.code (String.unsafe_get string index)
  let set_u8 bytes index value = Bytes.unsafe_set bytes index (Char.unsafe_chr value)

  let sub string offset length = String.sub string offset length

  let norm value =
    let value = value mod q in
    if value < 0 then value + q else value

  let center value =
    let value = norm value in
    if value > (q - 1) / 2 then value - q else value

  let add_mod left right = norm (left + right)
  let sub_mod left right = norm (left - right)

  let mul_mod left right =
    Int64.(to_int (rem (mul (of_int (norm left)) (of_int (norm right))) (of_int q)))

  let pow_mod base exponent =
    let rec loop accumulator base exponent =
      if exponent = 0 then accumulator
      else
        let accumulator =
          if exponent land 1 = 1 then mul_mod accumulator base else accumulator
        in
        loop accumulator (mul_mod base base) (exponent lsr 1)
    in
    loop 1 base exponent

  let bit_reverse_8 value =
    let result = ref 0 in
    for bit = 0 to 7 do
      result := (!result lsl 1) lor ((value lsr bit) land 1)
    done;
    !result

  let zetas = Array.init n (fun index -> pow_mod 1753 (bit_reverse_8 index))
  let inverse_n = pow_mod n (q - 2)

  let ntt polynomial =
    let result = Array.map norm polynomial in
    let index = ref 0 in
    let length = ref 128 in
    while !length > 0 do
      let start = ref 0 in
      while !start < n do
        incr index;
        let zeta = zetas.(!index) in
        for j = !start to !start + !length - 1 do
          let t = mul_mod zeta result.(j + !length) in
          let value = result.(j) in
          result.(j) <- add_mod value t;
          result.(j + !length) <- sub_mod value t
        done;
        start := !start + (2 * !length)
      done;
      length := !length / 2
    done;
    result

  let inverse_ntt polynomial =
    let result = Array.map norm polynomial in
    let index = ref n in
    let length = ref 1 in
    while !length < n do
      let start = ref 0 in
      while !start < n do
        decr index;
        let zeta = norm (-zetas.(!index)) in
        for j = !start to !start + !length - 1 do
          let left = result.(j) in
          let right = result.(j + !length) in
          result.(j) <- add_mod left right;
          result.(j + !length) <- mul_mod zeta (sub_mod left right)
        done;
        start := !start + (2 * !length)
      done;
      length := !length * 2
    done;
    Array.map (mul_mod inverse_n) result

  let pointwise left right = Array.init n (fun i -> mul_mod left.(i) right.(i))

  let matrix_vector_ntt matrix vector =
    Array.init P.k (fun row ->
        let accumulator = Array.make n 0 in
        for column = 0 to P.l - 1 do
          let product = pointwise matrix.(row).(column) vector.(column) in
          for coefficient = 0 to n - 1 do
            accumulator.(coefficient) <-
              add_mod accumulator.(coefficient) product.(coefficient)
          done
        done;
        accumulator)

  let poly_product_ntt challenge vector =
    Array.map (fun polynomial -> pointwise challenge polynomial) vector

  let pack_codes ~bits codes =
    let output = Bytes.make (Array.length codes * bits / 8) '\000' in
    let accumulator = ref 0 in
    let available = ref 0 in
    let position = ref 0 in
    Array.iter
      (fun value ->
        accumulator := !accumulator lor (value lsl !available);
        available := !available + bits;
        while !available >= 8 do
          set_u8 output !position (!accumulator land 0xff);
          incr position;
          accumulator := !accumulator lsr 8;
          available := !available - 8
        done)
      codes;
    Bytes.unsafe_to_string output

  let unpack_codes ~bits input =
    let count = String.length input * 8 / bits in
    let mask = (1 lsl bits) - 1 in
    let output = Array.make count 0 in
    let accumulator = ref 0 in
    let available = ref 0 in
    let position = ref 0 in
    for index = 0 to count - 1 do
      while !available < bits do
        accumulator := !accumulator lor (get_u8 input !position lsl !available);
        incr position;
        available := !available + 8
      done;
      output.(index) <- !accumulator land mask;
      accumulator := !accumulator lsr bits;
      available := !available - bits
    done;
    output

  let pack_eta polynomial =
    pack_codes ~bits:eta_bits (Array.map (fun value -> P.eta - value) polynomial)

  let unpack_eta input =
    let codes = unpack_codes ~bits:eta_bits input in
    if Array.exists (fun value -> value > 2 * P.eta) codes then
      Error (Invalid_encoding "ML-DSA signing key has a non-canonical eta encoding")
    else Ok (Array.map (fun value -> P.eta - value) codes)

  let pack_t0 polynomial =
    pack_codes ~bits:13 (Array.map (fun value -> (1 lsl 12) - value) polynomial)

  let unpack_t0 input =
    Array.map (fun value -> (1 lsl 12) - value) (unpack_codes ~bits:13 input)

  let pack_t1 polynomial = pack_codes ~bits:10 polynomial
  let unpack_t1 input = unpack_codes ~bits:10 input

  let pack_z polynomial =
    pack_codes ~bits:z_bits (Array.map (fun value -> P.gamma1 - value) polynomial)

  let unpack_z input =
    Array.map (fun value -> P.gamma1 - value) (unpack_codes ~bits:z_bits input)

  let pack_w1 polynomial = pack_codes ~bits:w1_bits polynomial

  let rec uniform_polynomial seed nonce output_length =
    let stream =
      Mldsa_keccak.shake128 ~output_length (seed ^ u16_le nonce)
    in
    let coefficients = Array.make n 0 in
    let count = ref 0 in
    let position = ref 0 in
    while !count < n && !position + 2 < String.length stream do
      let value =
        (get_u8 stream !position)
        lor (get_u8 stream (!position + 1) lsl 8)
        lor ((get_u8 stream (!position + 2) land 0x7f) lsl 16)
      in
      position := !position + 3;
      if value < q then begin
        coefficients.(!count) <- value;
        incr count
      end
    done;
    if !count = n then coefficients
    else uniform_polynomial seed nonce (2 * output_length)

  let rec eta_polynomial seed nonce output_length =
    let stream =
      Mldsa_keccak.shake256 ~output_length (seed ^ u16_le nonce)
    in
    let coefficients = Array.make n 0 in
    let count = ref 0 in
    let accept value =
      if !count < n then
        if P.eta = 2 then begin
          if value < 15 then begin
            let reduced = value - (((205 * value) lsr 10) * 5) in
            coefficients.(!count) <- 2 - reduced;
            incr count
          end
        end else if value < 9 then begin
          coefficients.(!count) <- 4 - value;
          incr count
        end
    in
    for position = 0 to String.length stream - 1 do
      let byte = get_u8 stream position in
      accept (byte land 0x0f);
      accept (byte lsr 4)
    done;
    if !count = n then coefficients
    else eta_polynomial seed nonce (2 * output_length)

  let mask_polynomial seed nonce =
    let stream =
      Mldsa_keccak.shake256 ~output_length:z_packed_bytes (seed ^ u16_le nonce)
    in
    unpack_z stream

  let rec challenge_polynomial seed output_length =
    let stream = Mldsa_keccak.shake256 ~output_length seed in
    let signs = ref 0L in
    for index = 0 to 7 do
      signs :=
        Int64.logor !signs
          (Int64.shift_left (Int64.of_int (get_u8 stream index)) (8 * index))
    done;
    let position = ref 8 in
    let coefficients = Array.make n 0 in
    let complete = ref true in
    for index = n - P.tau to n - 1 do
      if !complete then begin
        let selected = ref (-1) in
        while !selected < 0 && !complete do
          if !position >= String.length stream then complete := false
          else begin
            let candidate = get_u8 stream !position in
            incr position;
            if candidate <= index then selected := candidate
          end
        done;
        if !complete then begin
          coefficients.(index) <- coefficients.(!selected);
          coefficients.(!selected) <-
            if Int64.logand !signs 1L = 0L then 1 else -1;
          signs := Int64.shift_right_logical !signs 1
        end
      end
    done;
    if !complete then coefficients
    else challenge_polynomial seed (2 * output_length)

  let expand_matrix rho =
    Array.init P.k (fun row ->
        Array.init P.l (fun column ->
            uniform_polynomial rho ((row lsl 8) + column) 840))

  let expand_secret seed =
    let s1 = Array.init P.l (fun index -> eta_polynomial seed index 272) in
    let s2 = Array.init P.k (fun index -> eta_polynomial seed (P.l + index) 272) in
    s1, s2

  let power2round value =
    let value = norm value in
    let high = (value + (1 lsl (d - 1)) - 1) lsr d in
    high, value - (high lsl d)

  let decompose value =
    let value = norm value in
    let alpha = 2 * P.gamma2 in
    let modulus = (q - 1) / alpha in
    let high = (value + (alpha / 2) - 1) / alpha in
    if high = modulus then 0, value - q else high, value - (high * alpha)

  (* FIPS 204 Algorithm 40 moves the high bits only for a hint of 1. Decoded
     hints are always 0 or 1, but test for 1 rather than for nonzero. *)
  let use_hint value hint =
    let high, low = decompose value in
    if hint <> 1 then high
    else
      let modulus = (q - 1) / (2 * P.gamma2) in
      if low > 0 then (high + 1) mod modulus
      else (high + modulus - 1) mod modulus

  let make_hint low high =
    if low > P.gamma2 || low < -P.gamma2
       || (low = -P.gamma2 && high <> 0)
    then 1
    else 0

  (* Scan complete vectors before deciding whether to reject a signing
     candidate.  This does not make ML-DSA signing constant-time -- the FIPS
     rejection loop still has a variable number of attempts -- but avoids
     exposing the position of the first coefficient that exceeds a bound. *)
  let norm_violation_flag polynomial bound =
    let violation = ref 0 in
    for index = 0 to Array.length polynomial - 1 do
      let exceeds = if abs (center polynomial.(index)) >= bound then 1 else 0 in
      violation := !violation lor exceeds
    done;
    !violation

  let vector_norm_violation_flag vector bound =
    let violation = ref 0 in
    for index = 0 to Array.length vector - 1 do
      violation := !violation lor norm_violation_flag vector.(index) bound
    done;
    !violation

  let encode_verification_key rho t1 =
    rho ^ String.concat "" (Array.to_list (Array.map pack_t1 t1))

  let decode_verification_key octets =
    if String.length octets <> verification_key_size then
      invalid_length "ML-DSA verification key" verification_key_size octets
    else
      let rho = sub octets 0 seed_size in
      let t1 =
        Array.init P.k (fun index ->
            unpack_t1
              (sub octets
                 (seed_size + (index * t1_packed_bytes))
                 t1_packed_bytes))
      in
      Ok (rho, t1)

  let encode_expanded_signing_key expanded =
    String.concat ""
      [ expanded.rho; expanded.key; expanded.tr;
        String.concat "" (Array.to_list (Array.map pack_eta expanded.s1));
        String.concat "" (Array.to_list (Array.map pack_eta expanded.s2));
        String.concat "" (Array.to_list (Array.map pack_t0 expanded.t0)) ]

  let decode_expanded_signing_key octets =
    if String.length octets <> signing_key_size then
      invalid_length "ML-DSA signing key" signing_key_size octets
    else
      let rho = sub octets 0 seed_size in
      let key = sub octets seed_size seed_size in
      let tr = sub octets (2 * seed_size) tr_bytes in
      let position = ref ((2 * seed_size) + tr_bytes) in
      let decode_eta_vector length =
        let output = Array.make length [||] in
        let error = ref None in
        for index = 0 to length - 1 do
          let encoded = sub octets !position eta_packed_bytes in
          position := !position + eta_packed_bytes;
          match unpack_eta encoded with
          | Ok polynomial -> output.(index) <- polynomial
          | Error value -> error := Some value
        done;
        match !error with None -> Ok output | Some value -> Error value
      in
      match decode_eta_vector P.l with
      | Error _ as error -> error
      | Ok s1 -> begin
          match decode_eta_vector P.k with
          | Error _ as error -> error
          | Ok s2 ->
              let t0 =
                Array.init P.k (fun index ->
                    let encoded = sub octets !position t0_packed_bytes in
                    position := !position + t0_packed_bytes;
                    let _ = index in
                    unpack_t0 encoded)
              in
              Ok { rho; key; tr; s1; s2; t0 }
        end

  let compute_public_parts expanded =
    let matrix = expand_matrix expanded.rho in
    let s1_ntt = Array.map ntt expanded.s1 in
    let product = matrix_vector_ntt matrix s1_ntt in
    let t =
      Array.mapi
        (fun row polynomial ->
          let polynomial = inverse_ntt polynomial in
          Array.init n (fun index -> add_mod polynomial.(index) expanded.s2.(row).(index)))
        product
    in
    let t1 = Array.make P.k [||] in
    let t0 = Array.make P.k [||] in
    Array.iteri
      (fun row polynomial ->
        let high = Array.make n 0 in
        let low = Array.make n 0 in
        for index = 0 to n - 1 do
          let high_value, low_value = power2round polynomial.(index) in
          high.(index) <- high_value;
          low.(index) <- low_value
        done;
        t1.(row) <- high;
        t0.(row) <- low)
      t;
    t1, t0

  let equal_string left right =
    if String.length left <> String.length right then false
    else
      let difference = ref 0 in
      for index = 0 to String.length left - 1 do
        difference := !difference lor (get_u8 left index lxor get_u8 right index)
      done;
      !difference = 0

  let equal_polyvec left right =
    Array.length left = Array.length right
    &&
    let difference = ref 0 in
    for row = 0 to Array.length left - 1 do
      for index = 0 to n - 1 do
        difference := !difference lor (left.(row).(index) lxor right.(row).(index))
      done
    done;
    !difference = 0

  let build_signing_key ?seed expanded =
    let t1, expected_t0 = compute_public_parts expanded in
    let verification_key = encode_verification_key expanded.rho t1 in
    let expected_tr =
      Mldsa_keccak.shake256 ~output_length:tr_bytes verification_key
    in
    if not (equal_string expanded.tr expected_tr) then
      Error (Invalid_encoding "ML-DSA signing key has an inconsistent public-key hash")
    else if not (equal_polyvec expanded.t0 expected_t0) then
      Error (Invalid_encoding "ML-DSA signing key has an inconsistent t0 vector")
    else
      Ok
        { seed; expanded_octets = encode_expanded_signing_key expanded;
          expanded; verification_key }

  let keypair_from_seed seed =
    let expanded_seed =
      Mldsa_keccak.shake256 ~output_length:128
        (seed ^ String.make 1 (Char.unsafe_chr P.k)
         ^ String.make 1 (Char.unsafe_chr P.l))
    in
    let rho = sub expanded_seed 0 seed_size in
    let rho_prime = sub expanded_seed seed_size 64 in
    let key = sub expanded_seed 96 seed_size in
    let s1, s2 = expand_secret rho_prime in
    let provisional =
      { rho; key; tr = String.make tr_bytes '\000'; s1; s2;
        t0 = Array.make P.k [||] }
    in
    let t1, t0 = compute_public_parts provisional in
    let verification_key = encode_verification_key rho t1 in
    let tr = Mldsa_keccak.shake256 ~output_length:tr_bytes verification_key in
    let expanded = { provisional with tr; t0 } in
    { seed = Some seed; expanded_octets = encode_expanded_signing_key expanded;
      expanded; verification_key }

  let signing_key_of_seed seed =
    if String.length seed <> seed_size then
      invalid_length "ML-DSA seed" seed_size seed
    else Ok (keypair_from_seed seed)

  let signing_key_to_seed key = Option.map (fun seed -> String.sub seed 0 seed_size) key.seed

  let signing_key_of_octets octets =
    match decode_expanded_signing_key octets with
    | Error _ as error -> error
    | Ok expanded -> build_signing_key expanded

  let signing_key_to_octets key = String.sub key.expanded_octets 0 signing_key_size
  let verification_key_of_signing_key key = key.verification_key

  let verification_key_of_octets octets =
    match decode_verification_key octets with
    | Error _ as error -> error
    | Ok _ -> Ok (String.sub octets 0 verification_key_size)

  let verification_key_to_octets key = String.sub key 0 verification_key_size

  type decoded_signature = {
    c_tilde : string;
    z : polyvec;
    hint : polyvec;
  }

  let decode_signature octets =
    if String.length octets <> signature_size then
      invalid_length "ML-DSA signature" signature_size octets
    else
      let c_tilde = sub octets 0 P.c_tilde_bytes in
      let z_offset = P.c_tilde_bytes in
      let z =
        Array.init P.l (fun index ->
            unpack_z
              (sub octets (z_offset + (index * z_packed_bytes)) z_packed_bytes))
      in
      let hint_offset = z_offset + (P.l * z_packed_bytes) in
      let hint = Array.init P.k (fun _ -> Array.make n 0) in
      let previous = ref 0 in
      let valid = ref true in
      for row = 0 to P.k - 1 do
        let endpoint = get_u8 octets (hint_offset + P.omega + row) in
        if endpoint < !previous || endpoint > P.omega then valid := false;
        if !valid then begin
          for index = !previous to endpoint - 1 do
            let coefficient = get_u8 octets (hint_offset + index) in
            if index > !previous
               && coefficient <= get_u8 octets (hint_offset + index - 1)
            then valid := false
            else hint.(row).(coefficient) <- 1
          done;
          previous := endpoint
        end
      done;
      for index = !previous to P.omega - 1 do
        if get_u8 octets (hint_offset + index) <> 0 then valid := false
      done;
      if not !valid then
        Error (Invalid_encoding "ML-DSA signature has a non-canonical hint encoding")
      else Ok { c_tilde; z; hint }

  let signature_of_octets octets =
    match decode_signature octets with
    | Error _ as error -> error
    | Ok _ -> Ok (String.sub octets 0 signature_size)

  let signature_to_octets signature = String.sub signature 0 signature_size

  let encode_signature c_tilde z hint =
    let output = Bytes.make signature_size '\000' in
    Bytes.blit_string c_tilde 0 output 0 P.c_tilde_bytes;
    let position = ref P.c_tilde_bytes in
    Array.iter
      (fun polynomial ->
        let encoded = pack_z polynomial in
        Bytes.blit_string encoded 0 output !position z_packed_bytes;
        position := !position + z_packed_bytes)
      z;
    let hint_offset = !position in
    let count = ref 0 in
    for row = 0 to P.k - 1 do
      for coefficient = 0 to n - 1 do
        if hint.(row).(coefficient) <> 0 then begin
          (* [set_u8] does not check bounds, and position [omega] starts the
             per-row counts. The signer never gets here with more than omega
             hints; fail loudly rather than write past the hint area. *)
          if !count = P.omega then
            invalid_arg (P.name ^ ": a signature holds at most omega hints");
          set_u8 output (hint_offset + !count) coefficient;
          incr count
        end
      done;
      set_u8 output (hint_offset + P.omega + row) !count
    done;
    Bytes.unsafe_to_string output

  let formatted_prefix context =
    String.make 1 '\000'
    ^ String.make 1 (Char.unsafe_chr (String.length context))
    ^ context

  let sign_mu_with_randomness key ~mu randomness =
    if String.length mu <> 64 then
      invalid_length "ML-DSA message representative" 64 mu
    else if String.length randomness <> 32 then
      invalid_length "ML-DSA signing randomness" 32 randomness
    else
      let expanded = key.expanded in
      let rho_prime =
        Mldsa_keccak.shake256 ~output_length:64
          (expanded.key ^ randomness ^ mu)
      in
      let matrix = expand_matrix expanded.rho in
      let s1_ntt = Array.map ntt expanded.s1 in
      let s2_ntt = Array.map ntt expanded.s2 in
      let t0_ntt = Array.map ntt expanded.t0 in
      let rec attempt iteration =
        if iteration >= 821 then Error Signing_failed
        else
          let kappa = iteration * P.l in
          let y = Array.init P.l (fun row -> mask_polynomial rho_prime (kappa + row)) in
          let w_ntt = matrix_vector_ntt matrix (Array.map ntt y) in
          let w = Array.map inverse_ntt w_ntt in
          let w1 = Array.make P.k [||] in
          let w0 = Array.make P.k [||] in
          for row = 0 to P.k - 1 do
            let high = Array.make n 0 in
            let low = Array.make n 0 in
            for index = 0 to n - 1 do
              let high_value, low_value = decompose w.(row).(index) in
              high.(index) <- high_value;
              low.(index) <- low_value
            done;
            w1.(row) <- high;
            w0.(row) <- low
          done;
          let encoded_w1 =
            String.concat "" (Array.to_list (Array.map pack_w1 w1))
          in
          let c_tilde =
            Mldsa_keccak.shake256 ~output_length:P.c_tilde_bytes (mu ^ encoded_w1)
          in
          let challenge_ntt = ntt (challenge_polynomial c_tilde 136) in
          let cs1 =
            Array.map
              (fun polynomial -> Array.map center (inverse_ntt polynomial))
              (poly_product_ntt challenge_ntt s1_ntt)
          in
          let z =
            Array.mapi
              (fun row polynomial ->
                Array.init n (fun index -> polynomial.(index) + cs1.(row).(index)))
              y
          in
          let rejection = ref (vector_norm_violation_flag z (P.gamma1 - beta)) in
          let cs2 =
            Array.map
              (fun polynomial -> Array.map center (inverse_ntt polynomial))
              (poly_product_ntt challenge_ntt s2_ntt)
          in
          let r0 =
            Array.mapi
              (fun row polynomial ->
                Array.init n (fun index -> center (polynomial.(index) - cs2.(row).(index))))
              w0
          in
          rejection := !rejection lor vector_norm_violation_flag r0 (P.gamma2 - beta);
          let ct0 =
            Array.map
              (fun polynomial -> Array.map center (inverse_ntt polynomial))
              (poly_product_ntt challenge_ntt t0_ntt)
          in
          rejection := !rejection lor vector_norm_violation_flag ct0 P.gamma2;
          let hints = Array.init P.k (fun _ -> Array.make n 0) in
          let hint_count = ref 0 in
          for row = 0 to P.k - 1 do
            for index = 0 to n - 1 do
              let low = center (r0.(row).(index) + ct0.(row).(index)) in
              let hint = make_hint low w1.(row).(index) in
              hints.(row).(index) <- hint;
              hint_count := !hint_count + hint
            done
          done;
          let too_many_hints = if !hint_count > P.omega then 1 else 0 in
          rejection := !rejection lor too_many_hints;
          if !rejection <> 0 then attempt (iteration + 1)
          else Ok (encode_signature c_tilde z hints)
      in
      attempt 0

  let sign_formatted_with_randomness key ~formatted_message randomness =
    let mu =
      Mldsa_keccak.shake256 ~output_length:64
        (key.expanded.tr ^ formatted_message)
    in
    sign_mu_with_randomness key ~mu randomness

  let sign_with_randomness ?(context = "") key ~message randomness =
    if String.length context > 255 then Error (Context_too_long (String.length context))
    else
      sign_formatted_with_randomness key
        ~formatted_message:(formatted_prefix context ^ message)
        randomness

  let sign_internal_for_testing key ~formatted_message ~randomness =
    sign_formatted_with_randomness key ~formatted_message randomness

  let sign_mu_for_testing key ~mu ~randomness =
    sign_mu_with_randomness key ~mu randomness

  let require_random operation random length =
    let value = random length in
    if String.length value <> length then
      invalid_arg
        (Format.sprintf "%s.%s: randomness callback returned %d bytes, expected %d"
           P.name operation (String.length value) length);
    value

  let generate ~random () =
    let seed = require_random "generate" random seed_size in
    let signing_key = keypair_from_seed seed in
    signing_key, signing_key.verification_key

  let sign ?(context = "") ~random key ~message =
    if String.length context > 255 then Error (Context_too_long (String.length context))
    else
      let randomness = require_random "sign" random 32 in
      sign_with_randomness ~context key ~message randomness

  let sign_deterministic ?context key ~message =
    sign_with_randomness ?context key ~message (String.make 32 '\000')

  let verify_mu verification_key ~mu signature =
    if String.length mu <> 64 then false
    else match decode_verification_key verification_key, decode_signature signature with
      | Ok (rho, t1), Ok decoded ->
          if vector_norm_violation_flag decoded.z (P.gamma1 - beta) <> 0 then false
          else
            let matrix = expand_matrix rho in
            let az = matrix_vector_ntt matrix (Array.map ntt decoded.z) in
            let challenge_ntt = ntt (challenge_polynomial decoded.c_tilde 136) in
            let shifted_t1 =
              Array.map
                (fun polynomial -> Array.map (fun value -> value lsl d) polynomial)
                t1
            in
            let ct1 =
              poly_product_ntt challenge_ntt (Array.map ntt shifted_t1)
            in
            let w_approx =
              Array.mapi
                (fun row polynomial ->
                  inverse_ntt
                    (Array.init n (fun index ->
                         sub_mod polynomial.(index) ct1.(row).(index))))
                az
            in
            let reconstructed_w1 =
              Array.mapi
                (fun row polynomial ->
                  Array.init n (fun index ->
                      use_hint polynomial.(index) decoded.hint.(row).(index)))
                w_approx
            in
            let encoded_w1 =
              String.concat "" (Array.to_list (Array.map pack_w1 reconstructed_w1))
            in
            let expected =
              Mldsa_keccak.shake256 ~output_length:P.c_tilde_bytes
                (mu ^ encoded_w1)
            in
            equal_string decoded.c_tilde expected
      | Error _, _ | _, Error _ -> false

  let verify_formatted verification_key ~formatted_message signature =
    let tr =
      Mldsa_keccak.shake256 ~output_length:tr_bytes verification_key
    in
    let mu =
      Mldsa_keccak.shake256 ~output_length:64
        (tr ^ formatted_message)
    in
    verify_mu verification_key ~mu signature

  let verify ?(context = "") verification_key ~message signature =
    if String.length context > 255 then false
    else
      verify_formatted verification_key
        ~formatted_message:(formatted_prefix context ^ message)
        signature

  let verify_internal_for_testing verification_key ~formatted_message signature =
    verify_formatted verification_key ~formatted_message signature

  let verify_mu_for_testing verification_key ~mu signature =
    verify_mu verification_key ~mu signature

  let use_hint_for_testing = use_hint

  let encode_signature_for_testing ~c_tilde ~z ~hint =
    encode_signature c_tilde z hint
end

module Mldsa44 = Make (struct
  let name = "Mldsa44"
  let k = 4
  let l = 4
  let eta = 2
  let tau = 39
  let gamma1 = 1 lsl 17
  let gamma2 = (8_380_417 - 1) / 88
  let omega = 80
  let c_tilde_bytes = 32
end)

module Mldsa65 = Make (struct
  let name = "Mldsa65"
  let k = 6
  let l = 5
  let eta = 4
  let tau = 49
  let gamma1 = 1 lsl 19
  let gamma2 = (8_380_417 - 1) / 32
  let omega = 55
  let c_tilde_bytes = 48
end)

module Mldsa87 = Make (struct
  let name = "Mldsa87"
  let k = 8
  let l = 7
  let eta = 2
  let tau = 60
  let gamma1 = 1 lsl 19
  let gamma2 = (8_380_417 - 1) / 32
  let omega = 75
  let c_tilde_bytes = 64
end)
