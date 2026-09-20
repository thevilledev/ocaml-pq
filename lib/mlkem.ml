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
