---------------------------- MODULE MldsaRejNTTPoly ----------------------------
(***************************************************************************)
(* ML-DSA RejNTTPoly (uniform_polynomial) with the "prefix of length L,    *)
(* retry with 2L" restart.                                                 *)
(*                                                                         *)
(* OCaml modelled (mldsa/mldsa_engine.ml, uniform_polynomial, lines        *)
(* 328-348): the recursion on output_length, the while loop with guard     *)
(* `!count < n && !position + 2 < String.length stream`, the 23-bit value  *)
(* b0 lor (b1 lsl 8) lor ((b2 land 0x7f) lsl 16) and the `value < q` test. *)
(*                                                                         *)
(* Checked against FIPS 204 Algorithm 30 (RejNTTPoly) with Algorithm 14    *)
(* (CoeffFromThreeBytes), written below as a recursive function over the   *)
(* XOF stream.                                                             *)
(*                                                                         *)
(* The XOF stream grows lazily (TLC branches over Alphabet whenever the    *)
(* OCaml loop reads a position not chosen yet), is shared by all retries   *)
(* (Mldsa_keccak.shake128 ~output_length is a prefix of the stream, see    *)
(* KeccakSponge), and a retry beyond MaxLen ends in state "gaveup".        *)
(*                                                                         *)
(* Why a small alphabet suffices: both loops use a 3-byte group only via   *)
(* its value (test value < q, copy value).  The ASSUMEs check the OCaml    *)
(* bit expression against CoeffFromThreeBytes for every byte value: b2     *)
(* masking for all 256 values and b0 + 256 b1 for all 2^16 pairs (the      *)
(* three lor operands occupy disjoint bit ranges 0-7, 8-15, 16-22).  The   *)
(* stream then needs accepted and rejected groups with distinct values:    *)
(* Alphabet {0x00, 0x80, 0xFF} gives rejection exactly for (_, 0xFF, 0xFF) *)
(* and exercises the high-bit mask of b2 (0x80 -> 0, 0xFF -> 0x7F).        *)
(*                                                                         *)
(* Constants: N coefficients (256 real), Q = 8380417, InitLens (real 840), *)
(* MaxLen, Alphabet.                                                       *)
(*                                                                         *)
(* Properties: NoFault (reads below the prefix length, writes below n),    *)
(* CountInv (the OCaml state is FIPS on the bytes read so far), DoneOK,    *)
(* GaveUpOK, StepBound - as in MlkemSampleNTT.                             *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, TLC, BitOps

CONSTANTS N, Q, InitLens, MaxLen, Alphabet

ASSUME N >= 1 /\ InitLens \subseteq 1 .. MaxLen /\ Alphabet \subseteq 0 .. 255

Zeros == [i \in 0 .. N - 1 |-> 0]
Ext(k) == IF k <= 0 THEN {<<>>} ELSE [1 .. k -> Alphabet]

(* FIPS 204 Algorithm 14 CoeffFromThreeBytes(b0, b1, b2):                  *)
(*   b2' <- b2; if b2' > 127 then b2' <- b2' - 128                         *)
(*   z <- 2^16 b2' + 2^8 b1 + b0; if z < q then return z else bottom       *)
CoeffFromThreeBytes(b0, b1, b2) ==
  LET b2p == IF b2 > 127 THEN b2 - 128 ELSE b2
      z == 2 ^ 16 * b2p + 2 ^ 8 * b1 + b0
  IN IF z < Q THEN [ok |-> TRUE, z |-> z] ELSE [ok |-> FALSE, z |-> 0]

(* FIPS 204 Algorithm 30 RejNTTPoly on a finite stream S:                  *)
(*   j <- 0                                                                *)
(*   while j < 256:                                                        *)
(*     (ctx, s) <- G.Squeeze(ctx, 3)                                       *)
(*     a_j <- CoeffFromThreeBytes(s[0], s[1], s[2])                        *)
(*     if a_j != bottom then j <- j + 1                                    *)
RECURSIVE RejLoop(_, _, _, _)
RejLoop(S, pos, j, a) ==
  IF j >= N THEN [ok |-> TRUE, a |-> a, used |-> pos, j |-> j]
  ELSE IF pos + 3 > Len(S) THEN [ok |-> FALSE, a |-> a, used |-> pos, j |-> j]
  ELSE LET c == CoeffFromThreeBytes(S[pos + 1], S[pos + 2], S[pos + 3])
       IN IF c.ok THEN RejLoop(S, pos + 3, j + 1, [a EXCEPT ![j] = c.z])
          ELSE RejLoop(S, pos + 3, j, a)

RejNTTPoly(S) == RejLoop(S, 0, 0, Zeros)

\* OCaml: (get_u8 stream p) lor (get_u8 stream (p+1) lsl 8)
\*        lor ((get_u8 stream (p+2) land 0x7f) lsl 16)
OcamlValue(b0, b1, b2) == Lor(Lor(b0, Lsl(b1, 8)), Lsl(Land(b2, 127), 16))

ASSUME \A b2 \in 0 .. 255 : Land(b2, 127) = IF b2 > 127 THEN b2 - 128 ELSE b2
ASSUME \A b0, b1 \in 0 .. 255 : Lor(b0, Lsl(b1, 8)) = b0 + 2 ^ 8 * b1
ASSUME \A b0, b1, b2 \in Alphabet :
         OcamlValue(b0, b1, b2) = 2 ^ 16 * Land(b2, 127) + 2 ^ 8 * b1 + b0

VARIABLES stream, len, position, count, out, pc, draws, steps, fault

vars == <<stream, len, position, count, out, pc, draws, steps, fault>>

Init ==
  /\ stream = <<>>
  /\ len \in InitLens             \* uniform_polynomial rho nonce 840
  /\ position = 0 /\ count = 0 /\ out = Zeros
  /\ pc = "loop" /\ draws = 1 /\ steps = 0 /\ fault = "none"

Loop ==
  /\ pc = "loop"
  /\ IF count < N /\ position + 2 < len
     THEN \E ext \in Ext(position + 3 - Len(stream)) :
          LET s == stream \o ext
              value == OcamlValue(s[position + 1], s[position + 2], s[position + 3])
          IN /\ stream' = s
             /\ position' = position + 3
             /\ IF value < Q
                THEN /\ out' = [out EXCEPT ![count] = value]
                     /\ count' = count + 1
                     /\ fault' = IF count \notin 0 .. N - 1 THEN "write past n" ELSE fault
                ELSE UNCHANGED <<out, count, fault>>
             /\ UNCHANGED <<len, pc, draws>>
     ELSE IF count = N
          THEN /\ pc' = "done"
               /\ UNCHANGED <<stream, len, position, count, out, draws, fault>>
          ELSE IF 2 * len > MaxLen
          THEN /\ pc' = "gaveup"
               /\ UNCHANGED <<stream, len, position, count, out, draws, fault>>
          ELSE \* uniform_polynomial seed nonce (2 * output_length)
               /\ len' = 2 * len /\ position' = 0 /\ count' = 0 /\ out' = Zeros
               /\ draws' = draws + 1
               /\ UNCHANGED <<stream, pc, fault>>
  /\ steps' = steps + 1

Terminated == pc \in {"done", "gaveup"} /\ UNCHANGED vars
Next == Loop \/ Terminated
Spec == Init /\ [][Next]_vars

NoFault == fault = "none"

TypeOK ==
  /\ stream \in Seq(Alphabet) /\ Len(stream) <= MaxLen
  /\ count \in 0 .. N /\ out \in [0 .. N - 1 -> 0 .. Q - 1]

CountInv ==
  pc = "loop" =>
    LET f == RejLoop(SubSeq(stream, 1, position), 0, 0, Zeros)
    IN f.j = count /\ f.a = out

DoneOK ==
  pc = "done" =>
    LET f == RejNTTPoly(stream)
    IN f.ok /\ f.a = out /\ f.used = position /\ position <= len

GaveUpOK ==
  pc = "gaveup" => (~RejNTTPoly(stream).ok /\ Len(stream) + 3 > len)

StepBound == steps <= 2 * MaxLen + 2 * draws
=============================================================================
