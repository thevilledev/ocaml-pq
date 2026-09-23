---------------------------- MODULE MldsaHintCodec ----------------------------
(***************************************************************************)
(* ML-DSA hint codec: the hint part of encode_signature / decode_signature *)
(*                                                                         *)
(* OCaml modelled (mldsa/mldsa_engine.ml):                                 *)
(*   decode_signature, lines 652-676: the `previous`/`valid` loop over the *)
(*     k endpoint bytes, the inner strictly-increasing check, and the      *)
(*     trailing-zero loop;                                                 *)
(*   encode_signature, lines 694-704: the `count` loop writing hint        *)
(*     positions and the cumulative endpoint bytes.                        *)
(* Both loops are modelled as small-step state machines whose variables    *)
(* are the OCaml refs (previous, valid, count, row, index) and the array   *)
(* contents (hint matrix, output bytes).  `hint_offset` is 0 here: the     *)
(* model's byte string is exactly the omega + k byte hint area.            *)
(*                                                                         *)
(* Checked against FIPS 204 Algorithm 20 (HintBitPack) and Algorithm 21    *)
(* (HintBitUnpack), written below as separate recursive functions that     *)
(* transliterate the FIPS pseudo-code.                                     *)
(*                                                                         *)
(* Constants: N = ring degree = size of the byte alphabet (the real code   *)
(* has n = 256 = number of byte values, so every byte is a valid           *)
(* coefficient index; the model keeps that relationship), K = rows,        *)
(* Omega = maximum number of hints.  N >= Omega + 2 so that endpoint bytes *)
(* > Omega are part of the alphabet.                                       *)
(*                                                                         *)
(* Behaviours (all explored exhaustively):                                 *)
(*   "fromS": every byte string s of length Omega + K: run the OCaml       *)
(*            decoder; if it accepts, run the OCaml encoder on the result. *)
(*   "fromH": every hint matrix h with <= Omega ones: run the OCaml        *)
(*            encoder, then the OCaml decoder on its output.               *)
(*                                                                         *)
(* Properties:                                                             *)
(*   TypeOK, NoFault     - all reads/writes in bounds; the encoder never   *)
(*                         writes a position into the endpoint area.       *)
(*   DecodeMatchesFIPS   - OCaml decode accepts exactly when HintBitUnpack *)
(*                         does, with the same hint matrix.                *)
(*   Canonical           - decode(s) = h  =>  encode(h) = s.               *)
(*   EncodeMatchesFIPS   - OCaml encode = HintBitPack.                     *)
(*   RoundTrip           - decode(encode(h)) = h for weight(h) <= Omega.   *)
(*   StepBound           - each loop terminates within its static bound.   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, K, Omega

ASSUME N \in Nat /\ K \in Nat \ {0} /\ Omega \in Nat \ {0} /\ N >= Omega + 2

Bytes    == 0 .. N - 1
SigLen   == Omega + K
Pos      == 0 .. SigLen - 1
Rows     == 0 .. K - 1
Cols     == 0 .. N - 1
ZeroHint == [r \in Rows |-> [c \in Cols |-> 0]]
ZeroSig  == [p \in Pos |-> 0]

HintOf(S) == [r \in Rows |-> [c \in Cols |-> IF <<r, c>> \in S THEN 1 ELSE 0]]
Weight(h) == Cardinality({rc \in Rows \X Cols : h[rc[1]][rc[2]] = 1})
ValidHints == { HintOf(S) : S \in { S \in SUBSET (Rows \X Cols) : Cardinality(S) <= Omega } }

(***************************************************************************)
(* FIPS 204 Algorithm 20: HintBitPack(h)                                   *)
(*   y <- 0^(omega+k); Index <- 0                                          *)
(*   for i from 0 to k-1: for j from 0 to 255:                             *)
(*       if h[i]_j != 0 then y[Index] <- j; Index <- Index + 1             *)
(*     y[omega + i] <- Index                                               *)
(***************************************************************************)
RECURSIVE PackLoop(_, _, _, _, _)
PackLoop(h, i, j, y, index) ==
  IF i = K THEN y
  ELSE IF j = N THEN PackLoop(h, i + 1, 0, [y EXCEPT ![Omega + i] = index], index)
  ELSE IF h[i][j] # 0 THEN PackLoop(h, i, j + 1, [y EXCEPT ![index] = j], index + 1)
  ELSE PackLoop(h, i, j + 1, y, index)

HintBitPack(h) == PackLoop(h, 0, 0, ZeroSig, 0)

(***************************************************************************)
(* FIPS 204 Algorithm 21: HintBitUnpack(y)                                 *)
(*   h <- 0; Index <- 0                                                    *)
(*   for i from 0 to k-1:                                                  *)
(*     if y[omega+i] < Index or y[omega+i] > omega then return bottom      *)
(*     First <- Index                                                      *)
(*     while Index < y[omega+i]:                                           *)
(*       if Index > First and y[Index-1] >= y[Index] then return bottom    *)
(*       h[i]_{y[Index]} <- 1; Index <- Index + 1                          *)
(*   for i from Index to omega-1: if y[i] != 0 then return bottom          *)
(*   return h                                                              *)
(***************************************************************************)
RECURSIVE UnpackWhile(_, _, _, _, _, _)
UnpackWhile(y, i, first, index, end, h) ==
  IF index < end
  THEN IF index > first /\ y[index - 1] >= y[index]
       THEN [ok |-> FALSE]
       ELSE UnpackWhile(y, i, first, index + 1, end, [h EXCEPT ![i][y[index]] = 1])
  ELSE [ok |-> TRUE, h |-> h, index |-> index]

RECURSIVE UnpackFor(_, _, _, _)
UnpackFor(y, i, index, h) ==
  IF i = K THEN [ok |-> TRUE, h |-> h, index |-> index]
  ELSE IF y[Omega + i] < index \/ y[Omega + i] > Omega THEN [ok |-> FALSE]
  ELSE LET r == UnpackWhile(y, i, index, index, y[Omega + i], h)
       IN IF ~r.ok THEN r ELSE UnpackFor(y, i + 1, r.index, r.h)

HintBitUnpack(y) ==
  LET r == UnpackFor(y, 0, 0, ZeroHint)
  IN IF ~r.ok THEN [ok |-> FALSE]
     ELSE IF \E p \in r.index .. Omega - 1 : y[p] # 0 THEN [ok |-> FALSE]
     ELSE [ok |-> TRUE, h |-> r.h]

(***************************************************************************)
(* State machine for the OCaml code.                                       *)
(***************************************************************************)
VARIABLES
  origin,   \* "fromS" or "fromH"
  s0, h0,   \* the original input of the pipeline
  pc,       \* "dec", "enc", "done"
  \* decode_signature refs
  dy, dphase, drow, didx, dend, dprev, dvalid, dhint, dsteps,
  \* encode_signature refs
  eh, eout, erow, ecoef, ecount, esteps,
  fault     \* "none" or a description of a safety violation

vars == <<origin, s0, h0, pc, dy, dphase, drow, didx, dend, dprev, dvalid, dhint,
          dsteps, eh, eout, erow, ecoef, ecount, esteps, fault>>

DecInit(y) ==
  /\ dy = y /\ dphase = "row" /\ drow = 0 /\ didx = 0 /\ dend = 0
  /\ dprev = 0 /\ dvalid = TRUE /\ dhint = ZeroHint /\ dsteps = 0

EncInit(h) ==
  /\ eh = h /\ eout = ZeroSig /\ erow = 0 /\ ecoef = 0 /\ ecount = 0 /\ esteps = 0

DecStart(y) ==
  /\ dy' = y /\ dphase' = "row" /\ drow' = 0 /\ didx' = 0 /\ dend' = 0
  /\ dprev' = 0 /\ dvalid' = TRUE /\ dhint' = ZeroHint /\ dsteps' = 0

EncStart(h) ==
  /\ eh' = h /\ eout' = ZeroSig /\ erow' = 0 /\ ecoef' = 0 /\ ecount' = 0 /\ esteps' = 0

Init ==
  /\ fault = "none"
  /\ \/ /\ origin = "fromS"
        /\ s0 \in [Pos -> Bytes]
        /\ h0 = ZeroHint
        /\ pc = "dec"
        /\ DecInit(s0)
        /\ EncInit(ZeroHint)
     \/ /\ origin = "fromH"
        /\ h0 \in ValidHints
        /\ s0 = ZeroSig
        /\ pc = "enc"
        /\ EncInit(h0)
        /\ DecInit(ZeroSig)

decVars == <<dy, dphase, drow, didx, dend, dprev, dvalid, dhint>>
encVars == <<eh, eout, erow, ecoef, ecount>>

(* for row = 0 to k-1: endpoint check, then enter the inner loop if valid  *)
DecRow ==
  /\ pc = "dec" /\ dphase = "row"
  /\ IF drow = K
     THEN /\ dphase' = "trail" /\ didx' = dprev
          /\ UNCHANGED <<dy, drow, dend, dprev, dvalid, dhint>>
     ELSE LET endpoint == dy[Omega + drow]
              v == dvalid /\ ~(endpoint < dprev \/ endpoint > Omega)
          IN /\ dvalid' = v
             /\ IF v
                THEN /\ dphase' = "inner" /\ didx' = dprev /\ dend' = endpoint
                     /\ UNCHANGED <<dy, drow, dprev, dhint>>
                ELSE /\ drow' = drow + 1
                     /\ UNCHANGED <<dy, dphase, didx, dend, dprev, dhint>>
  /\ fault' = IF drow < K /\ ~(Omega + drow \in Pos) THEN "dec: endpoint read out of bounds" ELSE fault

(* for index = !previous to endpoint - 1                                   *)
DecInner ==
  /\ pc = "dec" /\ dphase = "inner"
  /\ IF didx < dend
     THEN LET c == dy[didx]
          IN /\ IF didx > dprev /\ c <= dy[didx - 1]
                THEN /\ dvalid' = FALSE /\ UNCHANGED dhint
                ELSE /\ dhint' = [dhint EXCEPT ![drow][c] = 1] /\ UNCHANGED dvalid
             /\ didx' = didx + 1
             /\ UNCHANGED <<dy, dphase, drow, dend, dprev>>
             /\ fault' = IF ~(didx \in Pos) \/ (didx > dprev /\ ~(didx - 1 \in Pos)) \/ ~(c \in Cols)
                         THEN "dec: inner access out of bounds" ELSE fault
     ELSE /\ dprev' = dend /\ drow' = drow + 1 /\ dphase' = "row"
          /\ UNCHANGED <<dy, didx, dend, dvalid, dhint, fault>>

(* for index = !previous to omega - 1: trailing bytes must be zero         *)
DecTrail ==
  /\ pc = "dec" /\ dphase = "trail"
  /\ IF didx < Omega
     THEN /\ dvalid' = (dvalid /\ dy[didx] = 0)
          /\ didx' = didx + 1
          /\ UNCHANGED <<dy, dphase, drow, dend, dprev, dhint>>
          /\ fault' = IF ~(didx \in Pos) THEN "dec: trailing read out of bounds" ELSE fault
     ELSE /\ dphase' = "done"
          /\ UNCHANGED <<dy, drow, didx, dend, dprev, dvalid, dhint, fault>>

DecStep ==
  /\ (DecRow \/ DecInner \/ DecTrail)
  /\ dsteps' = dsteps + 1
  /\ UNCHANGED <<origin, s0, h0, pc, eh, eout, erow, ecoef, ecount, esteps>>

(* decoder finished: fromS continues with the encoder if accepted          *)
DecFinish ==
  /\ pc = "dec" /\ dphase = "done"
  /\ IF origin = "fromS" /\ dvalid
     THEN /\ pc' = "enc" /\ EncStart(dhint)
     ELSE /\ pc' = "done" /\ UNCHANGED <<eh, eout, erow, ecoef, ecount, esteps>>
  /\ UNCHANGED <<origin, s0, h0, dy, dphase, drow, didx, dend, dprev, dvalid, dhint, dsteps, fault>>

(* for row: for coefficient: if hint <> 0 then write; then endpoint        *)
EncStep ==
  /\ pc = "enc" /\ erow < K
  /\ IF ecoef < N
     THEN IF eh[erow][ecoef] # 0
          THEN /\ eout' = [eout EXCEPT ![ecount] = ecoef]
               /\ ecount' = ecount + 1
               /\ fault' = IF ecount >= Omega THEN "enc: hint write outside hint-position area"
                           ELSE fault
               /\ ecoef' = ecoef + 1 /\ UNCHANGED erow
          ELSE /\ ecoef' = ecoef + 1 /\ UNCHANGED <<eout, ecount, erow, fault>>
     ELSE /\ eout' = [eout EXCEPT ![Omega + erow] = ecount]
          /\ erow' = erow + 1 /\ ecoef' = 0
          /\ UNCHANGED <<ecount, fault>>
  /\ esteps' = esteps + 1
  /\ UNCHANGED <<origin, s0, h0, pc, eh, dy, dphase, drow, didx, dend, dprev, dvalid, dhint, dsteps>>

(* encoder finished: fromH continues with the decoder on the produced bytes*)
EncFinish ==
  /\ pc = "enc" /\ erow = K
  /\ IF origin = "fromH"
     THEN /\ pc' = "dec" /\ DecStart(eout)
     ELSE /\ pc' = "done" /\ UNCHANGED <<dy, dphase, drow, didx, dend, dprev, dvalid, dhint, dsteps>>
  /\ UNCHANGED <<origin, s0, h0, eh, eout, erow, ecoef, ecount, esteps, fault>>

Terminated == pc = "done" /\ UNCHANGED vars

Next == DecStep \/ DecFinish \/ EncStep \/ EncFinish \/ Terminated

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
  /\ origin \in {"fromS", "fromH"}
  /\ pc \in {"dec", "enc", "done"}
  /\ dy \in [Pos -> Bytes]
  /\ dphase \in {"row", "inner", "trail", "done"}
  /\ drow \in 0 .. K /\ dprev \in 0 .. Omega /\ dend \in 0 .. Omega
  /\ didx \in 0 .. Omega
  /\ dvalid \in BOOLEAN
  /\ dhint \in [Rows -> [Cols -> {0, 1}]]
  /\ eout \in [Pos -> Bytes]
  /\ erow \in 0 .. K /\ ecoef \in 0 .. N /\ ecount \in 0 .. Omega

NoFault == fault = "none"

DecodeMatchesFIPS ==
  (origin = "fromS" /\ pc # "dec") =>
     LET f == HintBitUnpack(s0)
     IN /\ dvalid = f.ok
        /\ dvalid => dhint = f.h

Canonical ==
  (origin = "fromS" /\ pc = "done" /\ dvalid) => eout = s0

EncodeMatchesFIPS ==
  (origin = "fromH" /\ pc # "enc") => eout = HintBitPack(h0)

RoundTrip ==
  (origin = "fromH" /\ pc = "done") => (dvalid /\ dhint = h0)

StepBound ==
  /\ dsteps <= 2 * K + 2 * Omega + 2
  /\ esteps <= K * (N + 1)

\* Sanity: the FIPS functions themselves are mutually inverse on valid hints.
FIPSRoundTrip ==
  (origin = "fromH" /\ pc = "enc" /\ esteps = 0) =>
     LET f == HintBitUnpack(HintBitPack(h0)) IN f.ok /\ f.h = h0
=============================================================================
