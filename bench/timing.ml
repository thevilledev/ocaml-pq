module M = Mlkem.Mlkem768

let samples =
  if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 5_000

let random length = String.init length (fun i -> Char.chr ((73 * i + 41) land 0xff))

type moments = { mutable count : int; mutable sum : float; mutable squares : float }

let add moments value =
  moments.count <- moments.count + 1;
  moments.sum <- moments.sum +. value;
  moments.squares <- moments.squares +. (value *. value)

let mean moments = moments.sum /. float moments.count

let variance moments =
  let n = float moments.count in
  (moments.squares -. ((moments.sum *. moments.sum) /. n)) /. (n -. 1.)

let () =
  let dk, ek = M.generate ~random () in
  let valid, _ = M.encapsulate ~random ek in
  let invalid_bytes = Bytes.of_string (M.ciphertext_to_octets valid) in
  Bytes.set invalid_bytes 0 (Char.chr (Char.code (Bytes.get invalid_bytes 0) lxor 1));
  let invalid =
    match M.ciphertext_of_octets (Bytes.to_string invalid_bytes) with
    | Ok value -> value
    | Error _ -> assert false
  in
  for _ = 1 to 100 do
    ignore (M.decapsulate dk valid);
    ignore (M.decapsulate dk invalid)
  done;
  let valid_moments = { count = 0; sum = 0.; squares = 0. } in
  let invalid_moments = { count = 0; sum = 0.; squares = 0. } in
  for index = 0 to samples - 1 do
    let ciphertext, moments =
      if ((index * 1103515245) lxor (index lsr 3)) land 1 = 0
      then valid, valid_moments
      else invalid, invalid_moments
    in
    let started = Unix.gettimeofday () in
    for _ = 1 to 8 do ignore (M.decapsulate dk ciphertext) done;
    add moments ((Unix.gettimeofday () -. started) /. 8.)
  done;
  let valid_mean = mean valid_moments and invalid_mean = mean invalid_moments in
  let denominator =
    sqrt ((variance valid_moments /. float valid_moments.count) +.
          (variance invalid_moments /. float invalid_moments.count))
  in
  let t = (valid_mean -. invalid_mean) /. denominator in
  Printf.printf "valid %.3f us, invalid %.3f us, Welch t = %.2f (%d samples)\n%!"
    (valid_mean *. 1_000_000.) (invalid_mean *. 1_000_000.) t samples;
  if Float.is_nan t || Float.abs t >= 10. then begin
    prerr_endline "timing distributions differ beyond the regression threshold";
    exit 1
  end
