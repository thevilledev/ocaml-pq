----------------------------- MODULE MlkemSampleNTT -----------------------------
(***************************************************************************)
(* ML-KEM SampleNTT with the "prefix of length L, retry with 2L" restart.  *)
(*                                                                         *)
(* OCaml modelled (lib/mlkem_engine.ml, sample_ntt, lines 312-336): the    *)
(* `draw output_length` recursion, the while loop over 3-byte groups with  *)
(* the guard `!count < n && !off + 2 < output_length`, the d1/d2           *)
(* extraction with lor/lsl/land/lsr, and both `count < n` write guards.    *)
(*                                                                         *)
(* Checked against FIPS 203 Algorithm 7 (SampleNTT), written below as a    *)
(* recursive function that consumes the XOF stream three bytes at a time.  *)
(*                                                                         *)
(* The XOF: Keccak.shake128 ~output_length returns the first output_length *)
(* bytes of one infinite stream (checked in KeccakSponge), so the model    *)
(* keeps a single stream that grows lazily: whenever the OCaml loop reads  *)
(* a position not yet chosen, TLC branches over every byte of Alphabet.    *)
(* Every stream over Alphabet is therefore explored, up to the point where *)
(* the OCaml code stops reading it.  A retry that would need a prefix      *)
(* longer than MaxLen ends the behaviour in state "gaveup" (a model bound, *)
(* not an OCaml behaviour), where FIPS must also still be incomplete.      *)
(*                                                                         *)
(* Constants: N = number of coefficients (256 in the real code); Q = 3329; *)
(* InitLens = initial output lengths (the real code uses 840 = 280 groups  *)
(* for 256 coefficients); MaxLen; Alphabet = the byte values the stream is *)
(* built from.                                                             *)
(*                                                                         *)
(* Why a small alphabet suffices: both loops use a 3-byte group only via   *)
(* (d1, d2) - they test d < q and copy d.  The ASSUME below checks, for    *)
(* all 2^16 (b0, b1) and all 2^16 (b1, b2), that the OCaml bit expressions *)
(* give exactly FIPS's d1 and d2, so the per-group arithmetic is verified  *)
(* for every byte value.  The stream exploration then only needs groups    *)
(* realising all four accept/reject patterns with distinct values:         *)
(* {0x00, 0x5A, 0xFF} gives d1 in {0,90,255,2560,2650,2815} or rejected    *)
(* (low nibble of b1 = 15) and d2 in {0,5,15,1440,1445,1455} or rejected   *)
(* (b2 = 0xFF).                                                            *)
(*                                                                         *)
(* Properties:                                                             *)
(*   NoFault    - reads below output_length, writes below n;               *)
(*   DoneOK     - the returned polynomial = FIPS SampleNTT on the stream,  *)
(*                which consumes exactly the bytes the final draw read;    *)
(*   GaveUpOK   - if OCaml needs a prefix longer than MaxLen, FIPS has not *)
(*                finished within the bytes read either;                   *)
(*   CountInv   - count <= n, and out[0..count-1] is FIPS's partial output;*)
(*   StepBound  - termination bound.                                       *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, TLC, BitOps

CONSTANTS N, Q, InitLens, MaxLen, Alphabet

ASSUME N >= 1 /\ InitLens \subseteq 1 .. MaxLen /\ Alphabet \subseteq 0 .. 255

Zeros == [i \in 0 .. N - 1 |-> 0]
Ext(k) == IF k <= 0 THEN {<<>>} ELSE [1 .. k -> Alphabet]

(***************************************************************************)
(* FIPS 203 Algorithm 7 SampleNTT on a finite byte sequence S.             *)
(*   j <- 0                                                                *)
(*   while j < 256:                                                        *)
(*     C <- XOF.Squeeze(ctx, 3)                                            *)
(*     d1 <- C[0] + 256 * (C[1] mod 16)                                    *)
(*     d2 <- floor(C[1] / 16) + 16 * C[2]                                  *)
(*     if d1 < q: a[j] <- d1; j <- j + 1                                   *)
(*     if d2 < q and j < 256: a[j] <- d2; j <- j + 1                       *)
(* Returns ok = FALSE if S runs out first; used = bytes squeezed.          *)
(***************************************************************************)
RECURSIVE SampleNTTLoop(_, _, _, _)
SampleNTTLoop(S, pos, j, a) ==
  IF j >= N THEN [ok |-> TRUE, a |-> a, used |-> pos, j |-> j]
  ELSE IF pos + 3 > Len(S) THEN [ok |-> FALSE, a |-> a, used |-> pos, j |-> j]
  ELSE LET C0 == S[pos + 1]
           C1 == S[pos + 2]
           C2 == S[pos + 3]
           d1 == C0 + 256 * (C1 % 16)
           d2 == (C1 \div 16) + 16 * C2
           a1 == IF d1 < Q THEN [a EXCEPT ![j] = d1] ELSE a
           j1 == IF d1 < Q THEN j + 1 ELSE j
           a2 == IF d2 < Q /\ j1 < N THEN [a1 EXCEPT ![j1] = d2] ELSE a1
           j2 == IF d2 < Q /\ j1 < N THEN j1 + 1 ELSE j1
       IN SampleNTTLoop(S, pos + 3, j2, a2)

SampleNTT(S) == SampleNTTLoop(S, 0, 0, Zeros)

\* Per-group arithmetic, all byte values (d1 uses only b0, b1; d2 only b1, b2)
OcamlD1(b0, b1) == Land(Lor(b0, Lsl(b1, 8)), 4095)
OcamlD2(b1, b2) == Lsr(Lor(b1, Lsl(b2, 8)), 4)
ASSUME \A b0, b1 \in 0 .. 255 : OcamlD1(b0, b1) = b0 + 256 * (b1 % 16)
ASSUME \A b1, b2 \in 0 .. 255 : OcamlD2(b1, b2) = (b1 \div 16) + 16 * b2

VARIABLES stream, len, off, count, out, pc, draws, steps, fault

vars == <<stream, len, off, count, out, pc, draws, steps, fault>>

Init ==
  /\ stream = <<>>
  /\ len \in InitLens            \* draw 840
  /\ off = 0 /\ count = 0 /\ out = Zeros
  /\ pc = "loop" /\ draws = 1 /\ steps = 0 /\ fault = "none"

(* One iteration of the while loop, or its exit (end of draw)              *)
Loop ==
  /\ pc = "loop"
  /\ IF count < N /\ off + 2 < len
     THEN \E ext \in Ext(off + 3 - Len(stream)) :
          LET s  == stream \o ext
              b0 == s[off + 1]
              b1 == s[off + 2]
              b2 == s[off + 3]
              \* let d1 = (get_u8 stream !off lor (get_u8 stream (!off + 1) lsl 8)) land 0xfff
              d1 == OcamlD1(b0, b1)
              \* let d2 = (get_u8 stream (!off + 1) lor (get_u8 stream (!off + 2) lsl 8)) lsr 4
              d2 == OcamlD2(b1, b2)
              w1 == d1 < Q /\ count < N
              out1 == IF w1 THEN [out EXCEPT ![count] = d1] ELSE out
              c1 == IF w1 THEN count + 1 ELSE count
              w2 == d2 < Q /\ c1 < N
              out2 == IF w2 THEN [out1 EXCEPT ![c1] = d2] ELSE out1
              c2 == IF w2 THEN c1 + 1 ELSE c1
          IN /\ stream' = s
             /\ off' = off + 3
             /\ out' = out2
             /\ count' = c2
             /\ fault' = IF off + 2 >= len THEN "read past output_length"
                         ELSE IF (w1 /\ count \notin 0 .. N - 1) \/ (w2 /\ c1 \notin 0 .. N - 1)
                              THEN "write past n" ELSE fault
             /\ UNCHANGED <<len, pc, draws>>
     ELSE IF count = N
          THEN /\ pc' = "done"
               /\ UNCHANGED <<stream, len, off, count, out, draws, fault>>
          ELSE IF 2 * len > MaxLen
          THEN /\ pc' = "gaveup"
               /\ UNCHANGED <<stream, len, off, count, out, draws, fault>>
          ELSE \* draw (output_length * 2): fresh out/count/off, same XOF stream
               /\ len' = 2 * len /\ off' = 0 /\ count' = 0 /\ out' = Zeros
               /\ draws' = draws + 1
               /\ UNCHANGED <<stream, pc, fault>>
  /\ steps' = steps + 1

Terminated == pc \in {"done", "gaveup"} /\ UNCHANGED vars
Next == Loop \/ Terminated
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
NoFault == fault = "none"

TypeOK ==
  /\ stream \in Seq(Alphabet) /\ Len(stream) <= MaxLen
  /\ count \in 0 .. N /\ off <= len + 2 /\ out \in [0 .. N - 1 -> 0 .. Q - 1]

\* during a draw, the OCaml state is FIPS run on the bytes read so far
CountInv ==
  pc = "loop" =>
    LET f == SampleNTTLoop(SubSeq(stream, 1, off), 0, 0, Zeros)
    IN /\ f.j = count
       /\ \A i \in 0 .. count - 1 : out[i] = f.a[i]

DoneOK ==
  pc = "done" =>
    LET f == SampleNTT(stream)
    IN f.ok /\ f.a = out /\ f.used = off /\ off <= len

GaveUpOK ==
  pc = "gaveup" => (~SampleNTT(stream).ok /\ Len(stream) + 3 > len)

StepBound == steps <= 2 * MaxLen + 2 * draws
=============================================================================
