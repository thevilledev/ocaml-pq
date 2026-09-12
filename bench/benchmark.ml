module M = Mlkem.Mlkem768

let iterations =
  if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 100

let random length = String.init length (fun i -> Char.chr ((31 * i + 17) land 0xff))

let measure label count operation =
  Gc.compact ();
  let started = Unix.gettimeofday () in
  for _ = 1 to count do operation () done;
  let elapsed = Unix.gettimeofday () -. started in
  Printf.printf "%-14s %9.3f ms/op  (%d iterations)\n%!"
    label (elapsed *. 1_000. /. float count) count

let () =
  let dk, ek = M.generate ~random () in
  let ciphertext, _ = M.encapsulate ~random ek in
  measure "key generation" iterations (fun () -> ignore (M.generate ~random ()););
  measure "encapsulation" iterations (fun () -> ignore (M.encapsulate ~random ek));
  measure "decapsulation" iterations (fun () -> ignore (M.decapsulate dk ciphertext))
