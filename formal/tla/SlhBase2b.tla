------------------------------- MODULE SlhBase2b -------------------------------
(***************************************************************************)
(* SLH-DSA base_2b conversions: FORS indices with a wrapping OCaml int     *)
(* accumulator, and the WOTS+ message digits with checksum.                *)
(*                                                                         *)
(* OCaml modelled (slhdsa/slhdsa_engine.ml):                               *)
(*   message_to_fors_indices, lines 394-408: the `input`, `bits`, `total`  *)
(*     refs; total := (total lsl 8) + byte grows without masking, so it    *)
(*     wraps modulo 2^63 (OCaml int), and each index is                    *)
(*     (total lsr bits) land ((1 lsl a) - 1);                              *)
(*   base_w_nibbles and chain_lengths, lines 282-299 (ASSUMEs).            *)
(*                                                                         *)
(* Checked against FIPS 205 Algorithm 4 (base_2b) with an unbounded        *)
(* integer `total`, as used by fors_sign / fors_pkFromSig (Algorithms 16,  *)
(* 17: indices <- base_2b(md, a, k)) and by wots_sign / wots_pkFromSig     *)
(* (Algorithms 7, 8: base_2b(M, lg_w, len1), csum << ((8 - (len2 lg_w mod  *)
(* 8)) mod 8), base_2b(toByte(csum, ceil(len2 lg_w / 8)), lg_w, len2)).    *)
(*                                                                         *)
(* Abstraction: the message is symbolic (bit t of byte i is the atom       *)
(* <<i, t>>), `total` is a W-position vector of sets of atoms ({} = 0).    *)
(* (total lsl 8) + byte is modelled as a shift that drops bits past W - 1  *)
(* (the wrap-around) followed by lor, which equals + because the low 8     *)
(* bits of total lsl 8 are 0 (checked: NoOverlap).  lsr is logical on the  *)
(* W-bit pattern.  All operations are exact at the bit level, so one run   *)
(* per (W, a, k) covers every message; W = 63 is the real OCaml int.       *)
(*                                                                         *)
(* Constants: Params = set of [w, a, k]; the cfg uses the six FIPS 205     *)
(* (a, k) pairs with W = 63 and analogues W in {10, 12, 16, 20, 31, 32}    *)
(* with every a in 1 .. W - 7 and k in 1 .. 5.                             *)
(*                                                                         *)
(* Properties:                                                             *)
(*   NoOverlap    - the + never adds overlapping bits;                     *)
(*   InputBound   - bytes read = ceil(k a / 8), never past the message;    *)
(*   BitsRange    - 0 <= bits < a + 8 (so 0 .. 7 after each index);        *)
(*   IndicesFIPS  - every index equals FIPS base_2b's (after wrapping);    *)
(*   StepBound    - termination bound.                                     *)
(*   ASSUMEs      - base_w_nibbles = base_2b(M, 4, 2n) for n = 16, 24, 32, *)
(*                  and chain_lengths' three checksum digits = FIPS for    *)
(*                  every possible checksum 0 .. 15 * len1.                *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT Params

MsgLen(P) == (P.k * P.a + 7) \div 8          \* fors_message_bytes
FW(P) == 8 * MsgLen(P) + 8                    \* enough positions for FIPS' total

ByteVec(i, w) == [p \in 0 .. w - 1 |-> IF p < 8 THEN {<<i, p>>} ELSE {}]
Shl(v, s, w) == [p \in 0 .. w - 1 |-> IF p >= s THEN v[p - s] ELSE {}]
Shr(v, s, w) == [p \in 0 .. w - 1 |-> IF p + s < w THEN v[p + s] ELSE {}]
Or(v, u, w) == [p \in 0 .. w - 1 |-> v[p] \cup u[p]]
Overlap(v, u, w) == \E p \in 0 .. w - 1 : v[p] # {} /\ u[p] # {}
LowBits(v, k) == [p \in 0 .. k - 1 |-> v[p]]

(***************************************************************************)
(* FIPS 205 Algorithm 4 base_2b(X, b, out_len), unbounded total:           *)
(*   in <- 0; bits <- 0; total <- 0                                        *)
(*   for out from 0 to out_len - 1:                                        *)
(*     while bits < b:                                                     *)
(*       total <- (total << 8) + X[in]; in <- in + 1; bits <- bits + 8     *)
(*     bits <- bits - b                                                    *)
(*     baseb[out] <- (total >> bits) mod 2^b                               *)
(* The message is symbolic, so total is a vector of FW positions (never    *)
(* overflowing: at most 8 * MsgLen bits are ever shifted in).              *)
(***************************************************************************)
RECURSIVE Base2bLoop(_, _, _, _, _, _, _, _)
Base2bLoop(fw, b, outLen, out, in, bits, total, acc) ==
  IF out = outLen THEN acc
  ELSE IF bits < b
       THEN Base2bLoop(fw, b, outLen, out, in + 1, bits + 8,
                       Or(Shl(total, 8, fw), ByteVec(in, fw), fw), acc)
       ELSE Base2bLoop(fw, b, outLen, out + 1, in, bits - b, total,
                       Append(acc, LowBits(Shr(total, bits - b, fw), b)))

Base2b(fw, b, outLen) == Base2bLoop(fw, b, outLen, 0, 0, 0, [p \in 0 .. fw - 1 |-> {}], <<>>)

VARIABLES P, input, bits, total, indices, phase, steps

vars == <<P, input, bits, total, indices, phase, steps>>

Init ==
  /\ P \in Params
  /\ input = 0 /\ bits = 0 /\ total = [p \in 0 .. P.w - 1 |-> {}]
  /\ indices = <<>>
  /\ phase = "while"
  /\ steps = 0

\* Array.init k (fun _ -> while bits < a do ... done; bits := bits - a; ...)
Step ==
  /\ phase = "while"
  /\ IF Len(indices) = P.k
     THEN /\ phase' = "done" /\ UNCHANGED <<input, bits, total, indices>>
     ELSE IF bits < P.a
          THEN \* total := (total lsl 8) + Char.code message.[input]; incr input
               /\ total' = Or(Shl(total, 8, P.w), ByteVec(input, P.w), P.w)
               /\ input' = input + 1
               /\ bits' = bits + 8
               /\ UNCHANGED <<indices, phase>>
          ELSE \* bits := bits - a; (total lsr bits) land mask
               /\ bits' = bits - P.a
               /\ indices' = Append(indices, LowBits(Shr(total, bits - P.a, P.w), P.a))
               /\ UNCHANGED <<input, total, phase>>
  /\ steps' = steps + 1
  /\ UNCHANGED P

Terminated == phase = "done" /\ UNCHANGED vars
Next == Step \/ Terminated
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
\* the + in (total lsl 8) + byte never adds overlapping bits
NoOverlap == Overlap(Shl(total, 8, P.w), ByteVec(input, P.w), P.w) = FALSE

InputBound == input <= MsgLen(P) /\ (phase = "done" => input = MsgLen(P))

\* bits < a + 8, so after `bits := bits - a` it is in 0 .. 7 and an index
\* needs positions bits .. bits + a - 1 <= a + 6 of total
BitsRange == bits \in 0 .. P.a + 7

\* indices is append-only and checked in every state, so checking the newest
\* entry checks them all
IndicesFIPS ==
  Len(indices) > 0 =>
    indices[Len(indices)] = Base2b(FW(P), P.a, Len(indices))[Len(indices)]

StepBound == steps <= P.k + MsgLen(P) + 1

(***************************************************************************)
(* chain_lengths (lines 282-299) against FIPS 205 Algorithms 7/8.          *)
(***************************************************************************)
\* base_w_nibbles: index even -> byte lsr 4, odd -> byte land 0x0f
OcamlNibble(index) ==
  LET byte == ByteVec(index \div 2, 8)
  IN IF index % 2 = 0 THEN LowBits(Shr(byte, 4, 8), 4) ELSE LowBits(byte, 4)
ASSUME \A n \in {16, 24, 32} :
         LET f == Base2b(8 * n + 8, 4, 2 * n)
         IN \A index \in 0 .. 2 * n - 1 : OcamlNibble(index) = f[index + 1]

\* checksum digits for every checksum value (len1 = 2n <= 64, w = 16)
Bit(x, i) == (x \div 2 ^ i) % 2
OcamlCsumDigits(csum) ==
  LET c == csum * 2 ^ 4                                  \* checksum lsl 4
  IN <<(c \div 2 ^ 12) % 16, (c \div 2 ^ 8) % 16, (c \div 2 ^ 4) % 16>>
\* FIPS: csum << ((8 - ((len2 * lg_w) mod 8)) mod 8) with len2 = 3, lg_w = 4,
\* then base_2b(toByte(csum, ceil(12 / 8) = 2), 4, 3) with concrete bytes
FipsCsumDigits(csum) ==
  LET shift == (8 - ((3 * 4) % 8)) % 8
      c == csum * 2 ^ shift
      bytes == <<(c \div 256) % 256, c % 256>>            \* toByte(c, 2), big-endian
      tot == bytes[1] * 256 + bytes[2]
  IN <<(tot \div 2 ^ 12) % 16, (tot \div 2 ^ 8) % 16, (tot \div 2 ^ 4) % 16>>
ASSUME \A n \in {16, 24, 32} : \A csum \in 0 .. 15 * (2 * n) :
         /\ OcamlCsumDigits(csum) = FipsCsumDigits(csum)
         /\ csum * 2 ^ 4 < 2 ^ 16          \* toByte(csum, 2) loses nothing

(***************************************************************************)
(* Parameter sets                                                          *)
(***************************************************************************)
FipsParams ==
  { [w |-> 63, a |-> x[1], k |-> x[2]] : x \in {<<12, 14>>, <<6, 33>>, <<14, 17>>,
                                                <<8, 33>>, <<14, 22>>, <<9, 35>>} }
AnalogueParams ==
  { [w |-> x[1], a |-> x[2], k |-> x[3]] :
      x \in { y \in {10, 12, 16, 20, 31, 32} \X (1 .. 25) \X (1 .. 5) : y[2] <= y[1] - 7 } }
AllParams == FipsParams \cup AnalogueParams
=============================================================================
