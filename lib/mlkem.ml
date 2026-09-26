module Mlkem512 = Mlkem512
module Mlkem768 = Mlkem768
module Mlkem1024 = Mlkem1024

module Fips202 = struct
  (* Checked here so that a negative length is reported before any of the
     input is absorbed, and under the name the caller used. *)
  let shake128 ~output_length input =
    if output_length < 0 then
      invalid_arg "Mlkem.Fips202.shake128: negative output length";
    Keccak.shake128 ~output_length input

  let shake256 ~output_length input =
    if output_length < 0 then
      invalid_arg "Mlkem.Fips202.shake256: negative output length";
    Keccak.shake256 ~output_length input
end

module Rfc9861 = struct
  (* Checked here, as in [Fips202], before any of the input is absorbed. A
     domain byte of 0x80 or more would collide with the final padding bit. *)
  let check name domain output_length =
    if output_length < 0 then
      invalid_arg ("Mlkem.Rfc9861." ^ name ^ ": negative output length");
    if domain < 0x01 || domain > 0x7f then
      invalid_arg ("Mlkem.Rfc9861." ^ name ^ ": domain outside 0x01-0x7F")

  let turboshake128 ?(domain = 0x1f) ~output_length input =
    check "turboshake128" domain output_length;
    Keccak.turboshake128 ~domain ~output_length input

  let turboshake256 ?(domain = 0x1f) ~output_length input =
    check "turboshake256" domain output_length;
    Keccak.turboshake256 ~domain ~output_length input
end
