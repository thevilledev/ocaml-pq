-------------------------- MODULE MldsaRejBoundedPoly --------------------------
(***************************************************************************)
(* ML-DSA RejBoundedPoly (eta_polynomial) with the "prefix of length L,    *)
(* retry with 2L" restart.                                                 *)
(*                                                                         *)
(* OCaml modelled (mldsa/mldsa_engine.ml, eta_polynomial, lines 350-375):  *)
(* the recursion on output_length, the for loop over *every* byte of the   *)
(* prefix, `accept (byte land 0x0f); accept (byte lsr 4)`, and `accept`    *)
(* with its `!count < n` guard, the eta = 2 reduction                      *)
(* value - ((205 * value) lsr 10) * 5 and the eta = 4 branch.              *)
(*                                                                         *)
(* Checked against FIPS 204 Algorithm 31 (RejBoundedPoly) with Algorithm   *)
(* 15 (CoeffFromHalfByte), written below as a recursive function that      *)
(* squeezes one byte at a time and stops as soon as j = 256.               *)
(*                                                                         *)
(* The XOF stream grows lazily (TLC branches over Alphabet whenever the    *)
(* OCaml loop reads a position not chosen yet), is shared by all retries,  *)
(* and a retry beyond MaxLen ends in state "gaveup".  The OCaml loop keeps *)
(* reading after count = n (accept ignores the values), so the stream is   *)
(* extended over the whole prefix.                                         *)
(*                                                                         *)
(* Why a small alphabet suffices: both loops use a nibble only via         *)
(* CoeffFromHalfByte (accept? and value).  The ASSUMEs check, for every    *)
(* byte and nibble and both eta, that the OCaml nibble split and `accept`  *)
(* arithmetic give exactly FIPS's values.  The stream alphabet then only   *)
(* needs every accept/reject combination of the two nibbles for both eta:  *)
(* 0x31 (both accepted), 0x9E (eta 2: both accepted, lo = 14; eta 4: both  *)
(* rejected), 0xF8 (lo 8 accepted by both eta, hi 15 rejected), 0xFF       *)
(* (both rejected), 0x70 (lo 0, hi 7 accepted).                            *)
(*                                                                         *)
(* Constants: N coefficients (256 real), Etas (subset of {2, 4}), InitLens *)
(* (real 272 bytes), MaxLen, Alphabet.                                     *)
(*                                                                         *)
(* Properties: NoFault (reads below the prefix length, writes below n),    *)
(* CountInv (the OCaml state is FIPS on the bytes read so far, and after   *)
(* count reaches n nothing changes), DoneOK, GaveUpOK, StepBound.          *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, TLC, BitOps

CONSTANTS N, Etas, InitLens, MaxLen, Alphabet

ASSUME N >= 1 /\ Etas \subseteq {2, 4} /\ InitLens \subseteq 1 .. MaxLen
       /\ Alphabet \subseteq 0 .. 255

Zeros == [i \in 0 .. N - 1 |-> 0]
Ext(k) == IF k <= 0 THEN {<<>>} ELSE [1 .. k -> Alphabet]

(* FIPS 204 Algorithm 15 CoeffFromHalfByte(b, eta):                        *)
(*   if eta = 2 and b < 15 then return 2 - (b mod 5)                       *)
(*   else if eta = 4 and b < 9 then return 4 - b                           *)
(*   else return bottom                                                    *)
CoeffFromHalfByte(b, eta) ==
  IF eta = 2 /\ b < 15 THEN [ok |-> TRUE, v |-> 2 - (b % 5)]
  ELSE IF eta = 4 /\ b < 9 THEN [ok |-> TRUE, v |-> 4 - b]
  ELSE [ok |-> FALSE, v |-> 0]

(* FIPS 204 Algorithm 31 RejBoundedPoly on a finite stream S:              *)
(*   j <- 0                                                                *)
(*   while j < 256:                                                        *)
(*     z <- H.Squeeze(ctx, 1)                                              *)
(*     z0 <- CoeffFromHalfByte(z mod 16, eta)                              *)
(*     z1 <- CoeffFromHalfByte(floor(z / 16), eta)                         *)
(*     if z0 != bottom: a_j <- z0; j <- j + 1                              *)
(*     if z1 != bottom and j < 256: a_j <- z1; j <- j + 1                  *)
RECURSIVE BoundedLoop(_, _, _, _, _)
BoundedLoop(S, eta, pos, j, a) ==
  IF j >= N THEN [ok |-> TRUE, a |-> a, used |-> pos, j |-> j]
  ELSE IF pos + 1 > Len(S) THEN [ok |-> FALSE, a |-> a, used |-> pos, j |-> j]
  ELSE LET z == S[pos + 1]
           z0 == CoeffFromHalfByte(z % 16, eta)
           z1 == CoeffFromHalfByte(z \div 16, eta)
           a1 == IF z0.ok THEN [a EXCEPT ![j] = z0.v] ELSE a
           j1 == IF z0.ok THEN j + 1 ELSE j
           a2 == IF z1.ok /\ j1 < N THEN [a1 EXCEPT ![j1] = z1.v] ELSE a1
           j2 == IF z1.ok /\ j1 < N THEN j1 + 1 ELSE j1
       IN BoundedLoop(S, eta, pos + 1, j2, a2)

RejBoundedPoly(S, eta) == BoundedLoop(S, eta, 0, 0, Zeros)

(* OCaml `accept value` as a function of (count, coefficients)             *)
Accept(eta, value, cnt, coeffs) ==
  IF cnt < N
  THEN IF eta = 2
       THEN IF value < 15
            THEN LET reduced == value - Lsr(205 * value, 10) * 5
                 IN [cnt |-> cnt + 1, coeffs |-> [coeffs EXCEPT ![cnt] = 2 - reduced]]
            ELSE [cnt |-> cnt, coeffs |-> coeffs]
       ELSE IF value < 9
            THEN [cnt |-> cnt + 1, coeffs |-> [coeffs EXCEPT ![cnt] = 4 - value]]
            ELSE [cnt |-> cnt, coeffs |-> coeffs]
  ELSE [cnt |-> cnt, coeffs |-> coeffs]

\* nibble split and per-nibble arithmetic for every byte / nibble value
ASSUME \A z \in 0 .. 255 : Land(z, 15) = z % 16 /\ Lsr(z, 4) = z \div 16
ASSUME \A b \in 0 .. 15, eta \in {2, 4} :
         LET o == Accept(eta, b, 0, [i \in 0 .. 0 |-> 99])
             f == CoeffFromHalfByte(b, eta)
         IN /\ (o.cnt = 1) = f.ok
            /\ f.ok => o.coeffs[0] = f.v

VARIABLES eta, stream, len, position, count, out, pc, draws, steps, fault

vars == <<eta, stream, len, position, count, out, pc, draws, steps, fault>>

Init ==
  /\ eta \in Etas
  /\ stream = <<>>
  /\ len \in InitLens             \* eta_polynomial seed index 272
  /\ position = 0 /\ count = 0 /\ out = Zeros
  /\ pc = "loop" /\ draws = 1 /\ steps = 0 /\ fault = "none"

(* One iteration of `for position = 0 to String.length stream - 1`         *)
Loop ==
  /\ pc = "loop"
  /\ IF position <= len - 1
     THEN \E ext \in Ext(position + 1 - Len(stream)) :
          LET s == stream \o ext
              byte == s[position + 1]
              r0 == Accept(eta, Land(byte, 15), count, out)
              r1 == Accept(eta, Lsr(byte, 4), r0.cnt, r0.coeffs)
          IN /\ stream' = s
             /\ position' = position + 1
             /\ count' = r1.cnt
             /\ out' = r1.coeffs
             /\ fault' = IF r1.cnt > N THEN "write past n" ELSE fault
             /\ UNCHANGED <<len, pc, draws>>
     ELSE IF count = N
          THEN /\ pc' = "done"
               /\ UNCHANGED <<stream, len, position, count, out, draws, fault>>
          ELSE IF 2 * len > MaxLen
          THEN /\ pc' = "gaveup"
               /\ UNCHANGED <<stream, len, position, count, out, draws, fault>>
          ELSE \* eta_polynomial seed nonce (2 * output_length)
               /\ len' = 2 * len /\ position' = 0 /\ count' = 0 /\ out' = Zeros
               /\ draws' = draws + 1
               /\ UNCHANGED <<stream, pc, fault>>
  /\ steps' = steps + 1
  /\ UNCHANGED eta

Terminated == pc \in {"done", "gaveup"} /\ UNCHANGED vars
Next == Loop \/ Terminated
Spec == Init /\ [][Next]_vars

NoFault == fault = "none"

TypeOK ==
  /\ stream \in Seq(Alphabet) /\ Len(stream) <= MaxLen
  /\ count \in 0 .. N /\ out \in [0 .. N - 1 -> -eta .. eta]

\* After reading `position` bytes, OCaml holds FIPS's (j, a) on those bytes
\* (FIPS stops squeezing once j = n; OCaml keeps reading but changes nothing).
CountInv ==
  pc = "loop" =>
    LET f == BoundedLoop(SubSeq(stream, 1, position), eta, 0, 0, Zeros)
    IN f.j = count /\ f.a = out

DoneOK ==
  pc = "done" =>
    LET f == RejBoundedPoly(SubSeq(stream, 1, len), eta)
    IN f.ok /\ f.a = out /\ f.used <= len /\ position = len

GaveUpOK ==
  pc = "gaveup" => (~RejBoundedPoly(stream, eta).ok /\ Len(stream) = len)

StepBound == steps <= 2 * MaxLen + 2 * draws
=============================================================================
