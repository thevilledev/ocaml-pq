----------------------------- MODULE SlhHypertree -----------------------------
(***************************************************************************)
(* SLH-DSA digest split and hypertree layer traversal.                     *)
(*                                                                         *)
(* OCaml modelled (slhdsa/slhdsa_engine.ml):                               *)
(*   bytes_to_u64 / low_mask / split_message_digest, lines 487-513         *)
(*     (Int64 arithmetic, including the tree_bits = 64 special case);      *)
(*   sign_formatted_with_randomness, lines 598-636: the FORS address       *)
(*     {tree = idx_tree; keypair = idx_leaf} and the layer loop            *)
(*     (base_address, merkle_sign leaf, leaf := tree land low_mask h',     *)
(*     tree := tree lsr h');                                               *)
(*   verify_formatted, lines 673-722: the same split, FORS address and     *)
(*     layer loop, ending in the comparison with pk_root;                  *)
(*   merkle_root, lines 477-485 (pk_root = root of layer d-1, tree 0);     *)
(*   set_u64_be, lines 168-176 (encoding of the tree address).             *)
(*                                                                         *)
(* Checked against FIPS 205 Algorithm 19 (slh_sign_internal: idx_tree =    *)
(* toInt(tmp_idx_tree, ceil(tree_bits/8)) mod 2^tree_bits, idx_leaf =      *)
(* toInt(tmp_idx_leaf, ceil(h'/8)) mod 2^h'), Algorithm 20                 *)
(* (slh_verify_internal), Algorithm 12 (ht_sign) and Algorithm 13          *)
(* (ht_verify), plus Algorithm 1 (toInt) and 3 (toByte) with unbounded     *)
(* integers.                                                               *)
(*                                                                         *)
(* Abstraction: the digest bytes are symbolic.  Digest byte i, bit j is    *)
(* the atom <<i, j>>; an integer is a vector of bits, each bit a set of    *)
(* atoms (their OR; {} is 0; two atoms would mean an overlapping logor).   *)
(* All OCaml operations involved (Int64 shift_left, logor, logand with a   *)
(* concrete mask, shift_right_logical, sub 1L, to_int) are bitwise, and    *)
(* the FIPS operations (toInt, mod 2^k, >> k) are bit slicing, so one      *)
(* symbolic run per parameter set covers every digest exactly.  Int64 is   *)
(* a 64-position vector (bits shifted past 63 are lost; an OCaml shift by  *)
(* >= 64 is unspecified and flagged); FIPS integers use 96 positions.      *)
(* XMSS roots are symbols: sign's root after layer j is ("xmss", j,        *)
(* tree_j) (by SlhTreehash, treehash's root is xmss_node(0, h') of that    *)
(* tree); verify obtains the same symbol when it recomputes layer j at the *)
(* same (layer, tree, leaf) from the same message, which is what WOTS+ and *)
(* XMSS correctness guarantee.                                             *)
(*                                                                         *)
(* Constants: Params = set of parameter records [n, h, d, a, k, m]; the    *)
(* cfg uses AllParams = the 12 FIPS 205 parameter sets plus synthetic      *)
(* (h', d) combinations with tree_bits in 0..64 (including d = 1).         *)
(*                                                                         *)
(* Properties:                                                             *)
(*   NoFault          - no overlapping logor, no unspecified shift, to_int *)
(*                      of the leaf loses no bits;                         *)
(*   ForsAddressOK    - FORS tree address = idx_tree, keypair = idx_leaf   *)
(*                      (sign and verify);                                 *)
(*   SignLayersOK     - per-layer (layer, tree, leaf) = FIPS ht_sign's;    *)
(*   VerifyLayersOK   - verify visits the same (layer, tree, leaf) and     *)
(*                      signs/checks the same messages as ht_verify;       *)
(*   TopTreeZero      - the top layer's tree index is 0, so verify's final *)
(*                      root is merkle_root's pk_root;                     *)
(*   VerifyAccepts    - verify of an honest signature returns true;        *)
(*   TreeAddressBytes - set_u64_be(tree) = bytes 4..15 of toByte(tree, 12) *)
(*                      minus the 4 leading zero bytes;                    *)
(*   StepBound        - both loops take exactly d steps.                   *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT Params

W  == 64          \* Int64
FW == 96          \* "unbounded" FIPS integers (all values here are < 2^72)

\* ---------------------------------------------------------------------------
\* Symbolic bit vectors.  A symbolic bit is a set of atoms (their OR); {} is 0.
\* Atom <<i, j>> = bit j of digest byte i.  Concrete constants (masks) are
\* 0/1 vectors.  A symbolic bit with two or more atoms would be the result
\* of an overlapping logor, which the model flags.
\* ---------------------------------------------------------------------------
Zero(w) == [p \in 0 .. w - 1 |-> {}]

\* Int64 operations (positions 0..63); z is the fill value ({} or 0).
\* OCaml leaves shifts by >= 64 unspecified; ShiftOK flags them.
ShiftOK(s) == s < W
I64ShiftLeft(v, s, z) == [p \in 0 .. W - 1 |-> IF p >= s THEN v[p - s] ELSE z]
I64ShiftRightLogical(v, s) == [p \in 0 .. W - 1 |-> IF p + s < W THEN v[p + s] ELSE {}]
I64LogOr(v, u) == [p \in 0 .. W - 1 |-> v[p] \cup u[p]]
\* logand with a concrete (0/1) mask
I64LogAndConst(v, m) == [p \in 0 .. W - 1 |-> IF m[p] = 1 THEN v[p] ELSE {}]
\* concrete constants and concrete subtraction of 1 (two's complement, mod 2^64)
I64Const1 == [p \in 0 .. W - 1 |-> IF p = 0 THEN 1 ELSE 0]
I64MinusOne == [p \in 0 .. W - 1 |-> 1]
I64Sub1(v) == [p \in 0 .. W - 1 |-> IF \A q \in 0 .. p - 1 : v[q] = 0 THEN 1 - v[p] ELSE v[p]]
\* Int64.of_int of digest byte i (8 symbolic bits)
I64OfByte(i) == [p \in 0 .. W - 1 |-> IF p < 8 THEN {<<i, p>>} ELSE {}]

\* let low_mask bits = if bits = 64 then Int64.minus_one
\*                     else Int64.sub (Int64.shift_left 1L bits) 1L
LowMask(bits) ==
  IF bits = 64 THEN I64MinusOne ELSE I64Sub1(I64ShiftLeft(I64Const1, bits, 0))
LowMaskOK(bits) == bits = 64 \/ ShiftOK(bits)

\* bytes_to_u64 string offset length: loop result := (result lsl 8) lor byte
RECURSIVE BytesToU64Loop(_, _, _, _)
BytesToU64Loop(offset, length, i, result) ==
  IF i = length THEN result
  ELSE BytesToU64Loop(offset, length, i + 1,
                      I64LogOr(I64ShiftLeft(result, 8, {}), I64OfByte(offset + i)))
BytesToU64(offset, length) == BytesToU64Loop(offset, length, 0, Zero(W))

\* Int64.to_int: OCaml int has 63 bits; ToIntOK requires bits 62, 63 to be 0
I64ToInt(v) == [p \in 0 .. W - 2 |-> v[p]]
ToIntOK(v) == v[62] = {} /\ v[63] = {}

\* no bit is the OR of two different atoms (overlapping logor)
NoOverlap(v) == \A p \in DOMAIN v : Cardinality(v[p]) <= 1

\* ---------------------------------------------------------------------------
\* FIPS 205 integer helpers on FW-position vectors
\* ---------------------------------------------------------------------------
\* Algorithm 1 toInt(X[offset .. offset+n-1], n), big-endian
FipsToInt(offset, n) ==
  [p \in 0 .. FW - 1 |-> IF p < 8 * n THEN {<<offset + n - 1 - p \div 8, p % 8>>} ELSE {}]
FipsMod2(v, k) == [p \in 0 .. FW - 1 |-> IF p < k THEN v[p] ELSE {}]
FipsShr(v, k) == [p \in 0 .. FW - 1 |-> IF p + k < FW THEN v[p + k] ELSE {}]
\* compare a 64- or 63-position OCaml value with a FIPS integer
SameInt(o, f) ==
  /\ \A p \in DOMAIN o : o[p] = f[p]
  /\ \A p \in 0 .. FW - 1 : p \notin DOMAIN o => f[p] = {}

\* Algorithm 3 toByte(x, 12) (big-endian): byte i as a bit-vector of 8
FipsToByte12(x, i) == [b \in 0 .. 7 |-> x[8 * (11 - i) + b]]
\* OCaml set_u64_be result 8 value: byte i = (value lsr (8*(7-i))) land 0xff
SetU64Be(v, i) == [b \in 0 .. 7 |-> v[8 * (7 - i) + b]]

\* ---------------------------------------------------------------------------
\* Derived parameters (as in the OCaml functor)
\* ---------------------------------------------------------------------------
TreeHeight(Q) == Q.h \div Q.d
ForsBytes(Q)  == (Q.k * Q.a + 7) \div 8
TreeBits(Q)   == TreeHeight(Q) * (Q.d - 1)
TreeBytes(Q)  == (TreeBits(Q) + 7) \div 8
LeafBytes(Q)  == (TreeHeight(Q) + 7) \div 8

\* FIPS 205 Algorithm 19 lines 7-10
FipsIdxTree(Q) == FipsMod2(FipsToInt(ForsBytes(Q), TreeBytes(Q)), TreeBits(Q))
FipsIdxLeaf(Q) == FipsMod2(FipsToInt(ForsBytes(Q) + TreeBytes(Q), LeafBytes(Q)), TreeHeight(Q))

\* FIPS 205 Algorithm 12 / 13: the (layer, tree, leaf) of iteration j
RECURSIVE FipsLayer(_, _)
FipsLayer(Q, j) ==
  IF j = 0 THEN [layer |-> 0, tree |-> FipsIdxTree(Q), leaf |-> FipsIdxLeaf(Q)]
  ELSE LET prev == FipsLayer(Q, j - 1)
       IN [layer |-> j,
           leaf  |-> FipsMod2(prev.tree, TreeHeight(Q)),
           tree  |-> FipsShr(prev.tree, TreeHeight(Q))]

\* ---------------------------------------------------------------------------
\* The OCaml state machine
\* ---------------------------------------------------------------------------
VARIABLES P, pc, tree, leaf, layer, root, fors, signLog, verifyLog,
          verifyResult, steps, fault

vars == <<P, pc, tree, leaf, layer, root, fors, signLog, verifyLog,
          verifyResult, steps, fault>>

RootRec(kind, j, tr, lf) == [kind |-> kind, layer |-> j, tree |-> tr, leaf |-> lf]

\* split_message_digest: (tree, leaf) and the checks on the Int64 operations
SplitTree(Q) == I64LogAndConst(BytesToU64(ForsBytes(Q), TreeBytes(Q)), LowMask(TreeBits(Q)))
SplitLeaf64(Q) == I64LogAndConst(BytesToU64(ForsBytes(Q) + TreeBytes(Q), LeafBytes(Q)),
                                 LowMask(TreeHeight(Q)))
SplitFault(Q) ==
  IF ~LowMaskOK(TreeBits(Q)) \/ ~LowMaskOK(TreeHeight(Q)) THEN "split: unspecified shift"
  ELSE IF ~ToIntOK(SplitLeaf64(Q)) THEN "split: to_int loses bits"
  ELSE IF ~NoOverlap(SplitTree(Q)) \/ ~NoOverlap(SplitLeaf64(Q)) THEN "split: overlapping logor"
  ELSE "none"

Init ==
  /\ P \in Params
  /\ pc = "sign"
  /\ tree = SplitTree(P)
  /\ leaf = I64ToInt(SplitLeaf64(P))
  /\ fault = SplitFault(P)
  \* fors_address = { tree = initial_tree; keypair = initial_leaf } (sign)
  /\ fors = [signTree |-> tree, signLeaf |-> leaf, verifyDone |-> FALSE,
             verifyTree |-> tree, verifyLeaf |-> leaf]
  /\ layer = 0
  /\ root = RootRec("fors", -1, tree, leaf)       \* fors_sign's public key
  /\ signLog = <<>>
  /\ verifyLog = <<>>
  /\ verifyResult = FALSE
  /\ steps = 0

\* One iteration of the layer loop (identical code in sign and verify).
\* sign: merkle_sign returns the treehash root of (layer, tree);
\* verify: compute_root over the WOTS public key recomputed from the
\* signature segment that sign produced for this layer; it is that
\* tree's root iff the address and the message are the ones sign used.
LayerStep ==
  /\ pc \in {"sign", "verify"}
  /\ layer < P.d
  /\ LET mask == LowMask(TreeHeight(P))
         entry == [layer |-> layer, tree |-> tree, leaf |-> leaf, msg |-> root]
         masked == I64LogAndConst(tree, mask)
         honest == pc = "sign" \/ (layer < Len(signLog) /\ signLog[layer + 1] = entry)
     IN /\ IF pc = "sign"
           THEN /\ signLog' = Append(signLog, entry) /\ UNCHANGED verifyLog
           ELSE /\ verifyLog' = Append(verifyLog, entry) /\ UNCHANGED signLog
        /\ root' = IF honest THEN RootRec("xmss", layer, tree, Zero(W - 1))
                   ELSE RootRec("garbage", layer, tree, Zero(W - 1))
        /\ leaf' = I64ToInt(masked)
        /\ tree' = I64ShiftRightLogical(tree, TreeHeight(P))
        /\ fault' = IF ~LowMaskOK(TreeHeight(P)) \/ ~ShiftOK(TreeHeight(P))
                    THEN "layer: unspecified shift"
                    ELSE IF ~ToIntOK(masked) THEN "layer: to_int loses bits"
                    ELSE fault
        /\ layer' = layer + 1
        /\ UNCHANGED <<P, pc, fors, verifyResult>>

\* End of sign: verify re-splits the same digest; fors_public_key_from_signature
\* returns fors_sign's key iff it runs at the same FORS address.
StartVerify ==
  /\ pc = "sign" /\ layer = P.d
  /\ tree' = SplitTree(P)
  /\ leaf' = I64ToInt(SplitLeaf64(P))
  /\ fors' = [fors EXCEPT !.verifyDone = TRUE, !.verifyTree = tree', !.verifyLeaf = leaf']
  /\ root' = IF tree' = fors.signTree /\ leaf' = fors.signLeaf
             THEN RootRec("fors", -1, tree', leaf')
             ELSE RootRec("garbage", -1, tree', leaf')
  /\ layer' = 0
  /\ pc' = "verify"
  /\ UNCHANGED <<P, signLog, verifyLog, verifyResult, fault>>

\* constant_time_equal !root verification_key.pk_root, where pk_root is
\* merkle_root: the root of layer d - 1, tree 0L.
FinishVerify ==
  /\ pc = "verify" /\ layer = P.d
  /\ verifyResult' = (root = RootRec("xmss", P.d - 1, Zero(W), Zero(W - 1)))
  /\ pc' = "done"
  /\ UNCHANGED <<P, tree, leaf, layer, root, fors, signLog, verifyLog, fault>>

Step == (LayerStep \/ StartVerify \/ FinishVerify) /\ steps' = steps + 1

Terminated == pc = "done" /\ UNCHANGED vars
Next == Step \/ Terminated
Spec == Init /\ [][Next]_vars

\* ---------------------------------------------------------------------------
\* Properties
\* ---------------------------------------------------------------------------
NoFault == fault = "none"

ForsAddressOK ==
  /\ SameInt(fors.signTree, FipsIdxTree(P)) /\ SameInt(fors.signLeaf, FipsIdxLeaf(P))
  /\ fors.verifyDone =>
       SameInt(fors.verifyTree, FipsIdxTree(P)) /\ SameInt(fors.verifyLeaf, FipsIdxLeaf(P))

LayerOK(e, j) ==
  LET f == FipsLayer(P, j)
  IN e.layer = f.layer /\ SameInt(e.tree, f.tree) /\ SameInt(e.leaf, f.leaf)

\* The logs are append-only and invariants are checked in every state, so
\* checking the newest entry checks every entry.
SignLayersOK ==
  Len(signLog) > 0 => LayerOK(signLog[Len(signLog)], Len(signLog) - 1)

VerifyLayersOK ==
  LET j == Len(verifyLog)
  IN j > 0 =>
       /\ LayerOK(verifyLog[j], j - 1)
       /\ j <= Len(signLog) /\ verifyLog[j] = signLog[j]

TopTreeZero ==
  (Len(signLog) = P.d) => SameInt(signLog[P.d].tree, Zero(FW))

VerifyAccepts == pc = "done" => verifyResult = TRUE

TreeAddressBytes ==
  LET j == Len(signLog)
  IN j > 0 =>
       LET ft == FipsLayer(P, j - 1).tree
       IN /\ \A i \in 0 .. 7 : SetU64Be(signLog[j].tree, i) = FipsToByte12(ft, i + 4)
          /\ \A i \in 0 .. 3 : FipsToByte12(ft, i) = [b \in 0 .. 7 |-> {}]

StepBound == steps <= 2 * P.d + 2

\* ---------------------------------------------------------------------------
\* Parameter sets
\* ---------------------------------------------------------------------------
FipsParams == {
  [name |-> "SHA2/SHAKE-128s", n |-> 16, h |-> 63, d |-> 7,  a |-> 12, k |-> 14, m |-> 30],
  [name |-> "SHA2/SHAKE-128f", n |-> 16, h |-> 66, d |-> 22, a |-> 6,  k |-> 33, m |-> 34],
  [name |-> "SHA2/SHAKE-192s", n |-> 24, h |-> 63, d |-> 7,  a |-> 14, k |-> 17, m |-> 39],
  [name |-> "SHA2/SHAKE-192f", n |-> 24, h |-> 66, d |-> 22, a |-> 8,  k |-> 33, m |-> 42],
  [name |-> "SHA2/SHAKE-256s", n |-> 32, h |-> 64, d |-> 8,  a |-> 14, k |-> 22, m |-> 47],
  [name |-> "SHA2/SHAKE-256f", n |-> 32, h |-> 68, d |-> 17, a |-> 9,  k |-> 35, m |-> 49] }

\* synthetic (h', d) with tree_bits <= 64 (the functor rejects > 64); a = 3, k = 3
SyntheticParams ==
  { [name |-> "synthetic", n |-> 16, h |-> x[1] * x[2], d |-> x[2], a |-> 3, k |-> 3, m |-> 0] :
      x \in { y \in (1 .. 17) \X (1 .. 65) : y[1] * (y[2] - 1) <= 64 } }

AllParams == FipsParams \cup SyntheticParams

\* the functor's digest-length consistency check holds for the FIPS sets
ASSUME \A Q \in FipsParams : ForsBytes(Q) + TreeBytes(Q) + LeafBytes(Q) = Q.m
=============================================================================
