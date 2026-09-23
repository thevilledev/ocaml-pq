--------------------------- MODULE MldsaSampleInBall ---------------------------
(***************************************************************************)
(* ML-DSA SampleInBall (challenge_polynomial) with the "prefix of length   *)
(* L, retry with 2L" restart.                                              *)
(*                                                                         *)
(* OCaml modelled (mldsa/mldsa_engine.ml, challenge_polynomial, lines      *)
(* 383-414): the Int64 `signs` register built from the first 8 bytes       *)
(* (logor / shift_left), `position` starting at 8, the for loop over       *)
(* index = n - tau .. n - 1 guarded by `complete`, the inner while loop    *)
(* that sets complete := false when the prefix is exhausted, the swap      *)
(* coefficients.(index) <- coefficients.(selected); coefficients.(selected)*)
(* <- +-1 from `signs land 1`, `signs lsr 1` (logical), and the retry with *)
(* 2 * output_length.                                                      *)
(*                                                                         *)
(* Checked against FIPS 204 Algorithm 29 (SampleInBall): s <- 8 squeezed   *)
(* bytes, h <- BytesToBits(s); for i from 256 - tau to 255: squeeze j      *)
(* until j <= i; c_i <- c_j; c_j <- (-1)^h[i + tau - 256].                 *)
(*                                                                         *)
(* Abstraction: the 8 sign bytes are symbolic (bit b of byte k is the atom *)
(* <<k, b>>; Int64 bits are sets of atoms, {} = 0), so all 2^64 sign       *)
(* prefixes are covered at once and a coefficient +-1 is represented by    *)
(* the sign bit it was taken from.  Candidate bytes (stream positions >= 8)*)
(* are concrete and chosen lazily from Alphabet whenever the OCaml loop    *)
(* reads a position not chosen yet; the stream is shared by all retries.   *)
(* A candidate byte is only compared with the current index, so Alphabet   *)
(* holds the values 0 .. n-1 and one value >= n (255).  A retry beyond     *)
(* MaxLen ends in state "gaveup".                                          *)
(*                                                                         *)
(* Constants: N (ring degree analog, 256 real), Taus (tau values, real 39, *)
(* 49, 60), InitLens (real 136 = 8 + 128), MaxLen, Alphabet.               *)
(*                                                                         *)
(* Properties:                                                             *)
(*   NoFault    - sign bytes and candidates read below output_length, the  *)
\* sign register never ORs overlapping bits, writes are in
(*                0 .. n-1;                                                *)
(*   SignsInv   - after m coefficients, signs = h >> m (bits of the 8 sign *)
(*                bytes in BytesToBits order);                             *)
(*   DoneOK     - result = FIPS SampleInBall on the stream, consuming      *)
(*                exactly the bytes the final draw read;                   *)
(*   Weight     - exactly tau nonzero (+-1) coefficients;                  *)
(*   GaveUpOK   - if OCaml needs a prefix longer than MaxLen, FIPS has not *)
(*                finished within the bytes read either;                   *)
(*   StepBound  - termination bound.                                       *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS N, Taus, InitLens, MaxLen, Alphabet

ASSUME /\ N >= 1 /\ Taus \subseteq 1 .. N /\ \A t \in Taus : t <= 64
       /\ InitLens \subseteq 8 .. MaxLen /\ Alphabet \subseteq 0 .. 255

W == 64
ZeroC == [pm |-> FALSE, bit |-> {}]
PM(b) == [pm |-> TRUE, bit |-> b]      \* +1 if the bit is 0, -1 if it is 1
Zeros == [i \in 0 .. N - 1 |-> ZeroC]
Ext(k) == IF k <= 0 THEN {<<>>} ELSE [1 .. k -> Alphabet]

\* FIPS: h = BytesToBits(s), h[k] = bit (k mod 8) of s[k div 8]
Hbit(k) == IF k < 64 THEN {<<k \div 8, k % 8>>} ELSE {}

(***************************************************************************)
(* FIPS 204 Algorithm 29 SampleInBall on the candidate bytes C (stream     *)
(* positions 8, 9, ...).                                                   *)
(***************************************************************************)
RECURSIVE FindJ(_, _, _)
FindJ(i, pos, C) ==             \* first p >= pos with C[p] <= i, 0 if none
  IF pos > Len(C) THEN 0 ELSE IF C[pos] <= i THEN pos ELSE FindJ(i, pos + 1, C)

RECURSIVE SIBLoop(_, _, _, _, _)
SIBLoop(tau, i, pos, c, C) ==
  IF i = N THEN [ok |-> TRUE, c |-> c, used |-> pos - 1]
  ELSE LET p == FindJ(i, pos, C)
       IN IF p = 0 THEN [ok |-> FALSE, c |-> c, used |-> Len(C)]
          ELSE LET j == C[p]
               IN SIBLoop(tau, i + 1, p + 1,
                          [c EXCEPT ![i] = c[j], ![j] = PM(Hbit(i + tau - N))], C)

SampleInBall(tau, C) == SIBLoop(tau, N - tau, 1, Zeros, C)

\* Int64 on sets-of-atoms bit vectors
I64Zero == [p \in 0 .. W - 1 |-> {}]
I64OfByteShifted(k) == [p \in 0 .. W - 1 |-> IF p >= 8 * k /\ p < 8 * k + 8
                                                THEN {<<k, p - 8 * k>>} ELSE {}]
I64LogOr(v, u) == [p \in 0 .. W - 1 |-> v[p] \cup u[p]]
I64Lsr1(v) == [p \in 0 .. W - 1 |-> IF p + 1 < W THEN v[p + 1] ELSE {}]

VARIABLES tau, len, cands, signs, prepIdx, position, index, selected, complete,
          coeffs, placed, phase, draws, steps, fault

vars == <<tau, len, cands, signs, prepIdx, position, index, selected, complete,
          coeffs, placed, phase, draws, steps, fault>>

Init ==
  /\ tau \in Taus
  /\ len \in InitLens            \* challenge_polynomial c_tilde 136
  /\ cands = <<>>
  /\ signs = I64Zero /\ prepIdx = 0
  /\ position = 8 /\ index = N - tau /\ selected = -1 /\ complete = TRUE
  /\ coeffs = Zeros /\ placed = 0
  /\ phase = "prep" /\ draws = 1 /\ steps = 0 /\ fault = "none"

(* for index = 0 to 7: signs := signs lor (of_int byte lsl (8 * index))    *)
Prep ==
  /\ phase = "prep"
  /\ IF prepIdx < 8
     THEN /\ signs' = I64LogOr(signs, I64OfByteShifted(prepIdx))
          /\ prepIdx' = prepIdx + 1
          /\ fault' = IF prepIdx >= len THEN "sign byte read past output_length"
                      ELSE IF \E p \in 0 .. W - 1 : signs[p] /= {} /\ I64OfByteShifted(prepIdx)[p] /= {}
                      THEN "overlapping logor" ELSE fault
          /\ UNCHANGED <<phase, position, index, selected, complete, coeffs, placed>>
     ELSE /\ phase' = "for"
          /\ position' = 8 /\ index' = N - tau /\ complete' = TRUE
          /\ coeffs' = Zeros /\ placed' = 0
          /\ UNCHANGED <<signs, prepIdx, selected, fault>>
  /\ UNCHANGED <<cands, len, draws>>

(* for index = n - tau to n - 1 do if !complete then ...                   *)
For ==
  /\ phase = "for"
  /\ IF index <= N - 1
     THEN IF complete
          THEN /\ selected' = -1 /\ phase' = "while" /\ UNCHANGED index
          ELSE /\ index' = index + 1 /\ UNCHANGED <<selected, phase>>
     ELSE /\ phase' = "end" /\ UNCHANGED <<index, selected>>
  /\ UNCHANGED <<cands, len, signs, prepIdx, position, complete, coeffs, placed, draws, fault>>

(* while !selected < 0 && !complete do ...                                 *)
While ==
  /\ phase = "while"
  /\ IF selected < 0 /\ complete
     THEN /\ UNCHANGED phase
          /\ IF position >= len
             THEN /\ complete' = FALSE
                  /\ UNCHANGED <<cands, position, selected, fault>>
             ELSE \E ext \in Ext(position - 8 + 1 - Len(cands)) :
                  LET c == cands \o ext
                      candidate == c[position - 8 + 1]
                  IN /\ cands' = c
                     /\ position' = position + 1
                     /\ selected' = IF candidate <= index THEN candidate ELSE selected
                     /\ UNCHANGED <<complete, fault>>
     ELSE /\ phase' = "place"
          /\ UNCHANGED <<cands, position, selected, complete, fault>>
  /\ UNCHANGED <<len, signs, prepIdx, index, coeffs, placed, draws>>

(* if !complete then swap, set the sign, signs := signs lsr 1; next index  *)
Place ==
  /\ phase = "place"
  /\ IF complete
     THEN /\ coeffs' = [coeffs EXCEPT ![index] = coeffs[selected],
                                      ![selected] = PM(signs[0])]
          /\ signs' = I64Lsr1(signs)
          /\ placed' = placed + 1
          /\ fault' = IF selected \notin 0 .. N - 1 \/ index \notin 0 .. N - 1
                      THEN "coefficient index out of bounds" ELSE fault
     ELSE UNCHANGED <<coeffs, signs, placed, fault>>
  /\ index' = index + 1
  /\ phase' = "for"
  /\ UNCHANGED <<cands, len, prepIdx, position, selected, complete, draws>>

\* if !complete then coefficients else challenge_polynomial seed (2 * output_length)
End ==
  /\ phase = "end"
  /\ IF complete
     THEN /\ phase' = "done"
          /\ UNCHANGED <<len, signs, prepIdx, draws>>
     ELSE IF 2 * len > MaxLen
     THEN /\ phase' = "gaveup"
          /\ UNCHANGED <<len, signs, prepIdx, draws>>
     ELSE /\ len' = 2 * len /\ phase' = "prep" /\ signs' = I64Zero /\ prepIdx' = 0
          /\ draws' = draws + 1
  /\ UNCHANGED <<cands, position, index, selected, complete, coeffs, placed, fault>>

Step == (Prep \/ For \/ While \/ Place \/ End) /\ steps' = steps + 1 /\ UNCHANGED tau

Terminated == phase \in {"done", "gaveup"} /\ UNCHANGED vars
Next == Step \/ Terminated
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
NoFault == fault = "none"

TypeOK ==
  /\ cands \in Seq(Alphabet) /\ Len(cands) + 8 <= MaxLen
  /\ selected \in {-1} \cup 0 .. N - 1
  /\ index \in N - tau .. N
  /\ complete \in BOOLEAN

SignsInv ==
  phase \in {"for", "while", "place", "end", "done"} =>
    \A p \in 0 .. W - 1 : signs[p] = Hbit(p + placed)

DoneOK ==
  phase = "done" =>
    LET f == SampleInBall(tau, cands)
    IN f.ok /\ f.c = coeffs /\ 8 + f.used = position /\ position <= len

Weight ==
  phase = "done" =>
    Cardinality({i \in 0 .. N - 1 : coeffs[i].pm}) = tau

GaveUpOK ==
  phase = "gaveup" => (~SampleInBall(tau, cands).ok /\ Len(cands) + 8 = len)

StepBound == steps <= 6 * MaxLen + 4 * N * draws + 12 * draws
=============================================================================
