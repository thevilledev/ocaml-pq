------------------------------ MODULE MlkemDecaps ------------------------------
(***************************************************************************)
(* ML-KEM decapsulation: implicit rejection, constant-time comparison and  *)
(* constant-time selection.                                                *)
(*                                                                         *)
(* OCaml modelled (lib/mlkem_engine.ml):                                   *)
(*   ct_equal, lines 411-417: diff := diff lor (a[i] lxor b[i]) over the   *)
(*     bytes, then Int32 ((d lor (neg d)) lsr 31) land 1, lxor 1;          *)
(*   select_secret, lines 508-516: nz = choose_left lxor 1, mask = -nz,    *)
(*     out[i] = (l land (lnot mask)) lor (r land mask), set_u8 land 0xff;  *)
(*   decapsulate, lines 518-524: candidate K' from G(m' || h), rejection   *)
(*     key J(z || c), re-encryption c' and                                 *)
(*     select_secret ~choose_left:(ct_equal c c') K' Kbar.                 *)
(*                                                                         *)
(* Checked against FIPS 203 Algorithm 18 (ML-KEM.Decaps_internal):         *)
(*   Kbar <- J(z || c); c' <- K-PKE.Encrypt(ek, m', r');                   *)
(*   if c != c' then K' <- Kbar; return K'.                                *)
(*                                                                         *)
(* Abstraction: K-PKE and the hashes are opaque; what matters is the pair  *)
(* (c, c') of equal-length byte strings and the two secrets.  Every pair   *)
(* (c, c') over Alphabet^CtLen is explored with the byte loops as state    *)
(* machines; K' and Kbar are two fixed byte strings that differ in every   *)
(* bit.  The byte-level arithmetic is checked for every value by ASSUMEs:  *)
(* the Int32 zero test for every diff in 0 .. 255 (Int32 as 32-bit         *)
(* vectors), and select_secret for choose_left in {0, 1} and all byte      *)
(* pairs (OCaml ints represented modulo 2^16, which is exact here: land,   *)
(* lor, lnot and negation act on the low 16 bits independently of the      *)
(* upper bits, and set_u8 keeps only the low 8).                           *)
(*                                                                         *)
(* Constants: CtLen (ciphertext length analog; real 768/1088/1568),        *)
(* SsLen (shared-secret length analog; real 32), Alphabet.                 *)
(*                                                                         *)
(* Properties:                                                             *)
(*   DiffInv     - diff = OR of (c[j] xor c'[j]) for j < i, diff < 256;    *)
(*   CtEqualOK   - ct_equal returns 1 iff c = c', and only 0 or 1;         *)
(*   DecapsOK    - the output is K' if c = c' and Kbar otherwise (FIPS 203 *)
(*                 Algorithm 18);                                          *)
(*   StepBound   - CtLen + SsLen + 3 steps.                                *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, TLC, BitOps

CONSTANTS CtLen, SsLen, Alphabet

ASSUME CtLen >= 1 /\ SsLen >= 1 /\ Alphabet \subseteq 0 .. 255

(***************************************************************************)
(* Int32 as 32-bit vectors (bit 31 = sign).                                *)
(***************************************************************************)
\* Int32.of_int x for 0 <= x < 2^31 (TLC integers cannot hold 2^31)
I32OfInt(x) == [b \in 0 .. 31 |-> IF b = 31 THEN 0 ELSE (x \div 2 ^ b) % 2]
I32Lognot(v) == [b \in 0 .. 31 |-> 1 - v[b]]
I32Inc(v) == [b \in 0 .. 31 |-> IF \A c \in 0 .. b - 1 : v[c] = 1 THEN 1 - v[b] ELSE v[b]]
I32Neg(v) == I32Inc(I32Lognot(v))                               \* two's complement
I32Logor(v, u) == [b \in 0 .. 31 |-> IF v[b] = 1 \/ u[b] = 1 THEN 1 ELSE 0]
I32ShrLogical(v, s) == [b \in 0 .. 31 |-> IF b + s <= 31 THEN v[b + s] ELSE 0]
I32ToInt(v) == LET R[b \in 0 .. 31] == IF b = 0 THEN 0 ELSE R[b - 1] + v[b - 1] * 2 ^ (b - 1)
               IN R[31]                                         \* requires v[31] = 0

\* let d = Int32.of_int diff in
\* Int32.to_int (Int32.logand (Int32.shift_right_logical (Int32.logor d (Int32.neg d)) 31) 1l) lxor 1
CtEqualFinal(diff) ==
  LET d == I32OfInt(diff)
      s == I32ShrLogical(I32Logor(d, I32Neg(d)), 31)
      masked == [b \in 0 .. 31 |-> IF b = 0 THEN s[0] ELSE 0]  \* logand 1l
  IN Lxor(I32ToInt(masked), 1)

ASSUME \A diff \in 0 .. 255 : CtEqualFinal(diff) = IF diff = 0 THEN 1 ELSE 0

(***************************************************************************)
(* select_secret on OCaml ints modulo 2^16.                                *)
(***************************************************************************)
M16 == 2 ^ 16
Neg16(x) == (M16 - x) % M16
Lnot16(x) == M16 - 1 - x
Select(chooseLeft, l, r) ==
  LET nz == Lxor(chooseLeft, 1)
      mask == Neg16(nz)
  IN Land(Lor(Land(l, Lnot16(mask)), Land(r, mask)), 255)       \* set_u8 ... land 0xff

ASSUME \A cl \in {0, 1} : \A l, r \in 0 .. 255 :
         Select(cl, l, r) = IF cl = 1 THEN l ELSE r

(***************************************************************************)
(* Decapsulation state machine                                             *)
(***************************************************************************)
Kprime == [i \in 1 .. SsLen |-> IF i % 2 = 1 THEN 165 ELSE 60]   \* 0xA5, 0x3C
Kbar   == [i \in 1 .. SsLen |-> 255 - Kprime[i]]                  \* 0x5A, 0xC3

VARIABLES c, cPrime, i, diff, chooseLeft, j, out, pc, steps

vars == <<c, cPrime, i, diff, chooseLeft, j, out, pc, steps>>

Init ==
  /\ c \in [1 .. CtLen -> Alphabet]          \* received ciphertext
  /\ cPrime \in [1 .. CtLen -> Alphabet]     \* re-encryption pke_encrypt ek m' coins
  /\ i = 0 /\ diff = 0
  /\ chooseLeft = -1 /\ j = 0 /\ out = [k \in 1 .. SsLen |-> 0]
  /\ pc = "cmp" /\ steps = 0

(* for i = 0 to String.length a - 1 do diff := !diff lor (a[i] lxor b[i])  *)
Cmp ==
  /\ pc = "cmp"
  /\ IF i < CtLen
     THEN /\ diff' = Lor(diff, Lxor(c[i + 1], cPrime[i + 1]))
          /\ i' = i + 1
          /\ UNCHANGED <<chooseLeft, pc>>
     ELSE /\ chooseLeft' = CtEqualFinal(diff)
          /\ pc' = "select"
          /\ UNCHANGED <<i, diff>>
  /\ UNCHANGED <<c, cPrime, j, out>>

(* for i = 0 to shared_secret_size - 1 do set_u8 out i (select ...)        *)
Sel ==
  /\ pc = "select"
  /\ IF j < SsLen
     THEN /\ out' = [out EXCEPT ![j + 1] = Select(chooseLeft, Kprime[j + 1], Kbar[j + 1])]
          /\ j' = j + 1
          /\ UNCHANGED pc
     ELSE /\ pc' = "done" /\ UNCHANGED <<j, out>>
  /\ UNCHANGED <<c, cPrime, i, diff, chooseLeft>>

Step == (Cmp \/ Sel) /\ steps' = steps + 1
Terminated == pc = "done" /\ UNCHANGED vars
Next == Step \/ Terminated
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
RECURSIVE OrXor(_, _, _)
OrXor(a, b, n) == IF n = 0 THEN 0 ELSE Lor(OrXor(a, b, n - 1), Lxor(a[n], b[n]))

DiffInv == pc = "cmp" => (diff = OrXor(c, cPrime, i) /\ diff \in 0 .. 255)

CtEqualOK ==
  pc # "cmp" => (chooseLeft \in {0, 1} /\ (chooseLeft = 1 <=> c = cPrime))

\* FIPS 203 Algorithm 18: if c != c' then K' <- Kbar; return K'
DecapsOK == pc = "done" => out = IF c # cPrime THEN Kbar ELSE Kprime

StepBound == steps <= CtLen + SsLen + 3
=============================================================================
