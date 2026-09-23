------------------------------ MODULE SlhTreehash ------------------------------
(***************************************************************************)
(* SLH-DSA stack treehash with authentication-path capture, and the        *)
(* matching root recomputation.                                            *)
(*                                                                         *)
(* OCaml modelled (slhdsa/slhdsa_engine.ml):                               *)
(*   treehash, lines 337-370: the `stack`/`heights` arrays, the `offset`   *)
(*     ref, the leaf loop over index = 0 .. 2^height - 1, the merge while  *)
(*     loop, the address fields (field1 = tree height, field2 = tree index *)
(*     + index_offset >> height) and both authentication-path blits;       *)
(*   compute_root, lines 372-392.                                          *)
(* Callers: fors_sign / fors_public_key_from_signature (index_offset =     *)
(* tree << a, leaf_index = indices.(tree)), merkle_sign (index_offset = 0, *)
(* leaf_index = idx_leaf, the WOTS signature captured when gen_leaf is     *)
(* called with index = leaf_index), merkle_root (leaf_index = -1).         *)
(*                                                                         *)
(* Checked against FIPS 205 Algorithms 9 (xmss_node), 10 (xmss_sign),      *)
(* 11 (xmss_pkFromSig), 15 (fors_node), 16 (fors_sign) and 17              *)
(* (fors_pkFromSig), as recursive TLA+ definitions over a symbolic hash:   *)
(* a node value is the term <<"H", height, index, left, right>> and a leaf *)
(* is <<"leaf", global index>> (an injective, free-term hash), so term     *)
(* equality means "the same hash computation with the same address".       *)
(* The remaining address words (layer, tree, type, keypair) are copied     *)
(* unchanged from tree_address by the OCaml record update and are not      *)
(* modelled.                                                               *)
(*                                                                         *)
(* Constants: Heights = tree heights to check (h' for XMSS, a for FORS);   *)
(* NumTrees = number of FORS trees, giving index_offset = t * 2^height for *)
(* t in 0 .. NumTrees-1 (t = 0 is also the XMSS case).  Every leaf_index   *)
(* in {-1} \cup 0 .. 2^height - 1 is explored.                             *)
(*                                                                         *)
(* Properties:                                                             *)
(*   NoFault        - stack/heights writes within the height+1 arrays, and *)
(*                    no authentication write at level >= height (the blit *)
(*                    would be out of the height*n byte buffer);           *)
(*   StackInv       - heights strictly decreasing below the top pair, and  *)
(*                    every stack entry is the FIPS node for its position; *)
(*   RootOK         - stack.(0) = fors_node / xmss_node(t, height);        *)
(*   AuthOK         - auth[j] = node(t*2^(h-j) + ((leaf >> j) xor 1), j),  *)
(*                    each level written exactly once (none for -1);       *)
(*   CaptureOnce    - gen_leaf is called exactly once with leaf_index;     *)
(*   ComputeRootOK  - OCaml compute_root(leaf, auth) = root, and FIPS      *)
(*                    pkFromSig(leaf, auth) = root;                        *)
(*   StepBound      - termination within 3 * 2^h + h + 2 steps.            *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS Heights, NumTrees

ASSUME Heights \subseteq Nat \ {0} /\ NumTrees \in Nat \ {0}

Leaf(i) == <<"leaf", i>>
H(z, i, l, r) == <<"H", z, i, l, r>>

\* x xor 1 and x lsr k for non-negative x
Xor1(x) == IF x % 2 = 0 THEN x + 1 ELSE x - 1
Lsr(x, k) == x \div (2 ^ k)

(***************************************************************************)
(* FIPS 205 Algorithms 9 / 15: node(i, z) (symbolic).                      *)
(***************************************************************************)
RECURSIVE Node(_, _)
Node(i, z) == IF z = 0 THEN Leaf(i) ELSE H(z, i, Node(2 * i, z - 1), Node(2 * i + 1, z - 1))

(* FIPS 205 Algorithm 16 (fors_sign) / 10 (xmss_sign), AUTH[j]:            *)
(*   s <- floor(idx / 2^j) xor 1;  AUTH[j] <- node(t * 2^(h-j) + s, j)     *)
FipsAuth(t, h, idx, j) == Node(t * 2 ^ (h - j) + Xor1(idx \div 2 ^ j), j)

(* FIPS 205 Algorithm 17 (fors_pkFromSig) / 11 (xmss_pkFromSig) loop:      *)
(*   treeIndex <- t*2^a + idx; node0 <- leaf                               *)
(*   for j: setTreeHeight(j+1); if floor(idx/2^j) even:                    *)
(*       treeIndex <- treeIndex/2; node1 <- H(node0 || auth[j])            *)
(*     else treeIndex <- (treeIndex-1)/2; node1 <- H(auth[j] || node0)     *)
RECURSIVE PkLoop(_, _, _, _, _, _)
PkLoop(h, idx, auth, j, treeIndex, node0) ==
  IF j = h THEN node0
  ELSE IF (idx \div 2 ^ j) % 2 = 0
       THEN PkLoop(h, idx, auth, j + 1, treeIndex \div 2,
                   H(j + 1, treeIndex \div 2, node0, auth[j]))
       ELSE PkLoop(h, idx, auth, j + 1, (treeIndex - 1) \div 2,
                   H(j + 1, (treeIndex - 1) \div 2, auth[j], node0))

FipsPkFromSig(t, h, idx, auth) ==
  PkLoop(h, idx, auth, 0, t * 2 ^ h + idx, Leaf(t * 2 ^ h + idx))

MaxH == CHOOSE m \in Heights : \A x \in Heights : x <= m

VARIABLES
  height, t, offset0, leafIdx,   \* treehash arguments (index_offset = offset0)
  stack, heights, off,           \* OCaml arrays and the `offset` ref
  auth, authWrites,              \* authentication bytes (per level) and write counts
  index,                         \* the for-loop index
  phase,                         \* "push", "merge", "croot", "done"
  captured,                      \* gen_leaf calls with argument = leaf_index + index_offset
  root,                          \* stack.(0) returned by treehash
  clevel, cnode,                 \* compute_root loop
  steps, fault

vars == <<height, t, offset0, leafIdx, stack, heights, off, auth, authWrites, index,
          phase, captured, root, clevel, cnode, steps, fault>>

Init ==
  /\ height \in Heights
  /\ t \in 0 .. NumTrees - 1
  /\ offset0 = t * 2 ^ height
  /\ leafIdx \in {-1} \cup 0 .. 2 ^ height - 1
  /\ stack = [p \in 0 .. height |-> ""]
  /\ heights = [p \in 0 .. height |-> 0]
  /\ off = 0
  /\ auth = [j \in 0 .. height - 1 |-> "zero"]
  /\ authWrites = [j \in 0 .. height - 1 |-> 0]
  /\ index = 0
  /\ phase = "push"
  /\ captured = 0
  /\ root = "none" /\ clevel = 0 /\ cnode = "none"
  /\ steps = 0
  /\ fault = "none"

(* One iteration of the for loop head: push gen_leaf (index + index_offset)*)
Push ==
  /\ phase = "push"
  /\ IF index < 2 ^ height
     THEN LET leaf == Leaf(index + offset0)
              newOff == off + 1
          IN /\ IF off \in DOMAIN stack
                THEN /\ stack' = [stack EXCEPT ![off] = leaf]
                     /\ heights' = [heights EXCEPT ![off] = 0]
                     /\ UNCHANGED fault
                ELSE /\ fault' = "push: stack overflow"
                     /\ UNCHANGED <<stack, heights>>
             /\ off' = newOff
             /\ captured' = IF index + offset0 = leafIdx + offset0 THEN captured + 1 ELSE captured
             /\ IF leafIdx >= 0 /\ Xor1(leafIdx) = index
                THEN /\ auth' = [auth EXCEPT ![0] = leaf]
                     /\ authWrites' = [authWrites EXCEPT ![0] = @ + 1]
                ELSE UNCHANGED <<auth, authWrites>>
             /\ phase' = "merge"
             /\ UNCHANGED <<index, root, clevel, cnode>>
     ELSE /\ root' = stack[0]
          /\ phase' = IF leafIdx >= 0 THEN "croot" ELSE "done"
          /\ clevel' = 0
          /\ cnode' = Leaf(leafIdx + offset0)   \* F(sk) recomputed by the verifier
          /\ UNCHANGED <<stack, heights, off, auth, authWrites, index, captured, fault>>

(* One iteration of the merge while loop, or its exit                      *)
Merge ==
  /\ phase = "merge"
  /\ IF off >= 2 /\ heights[off - 1] = heights[off - 2]
     THEN LET nodeHeight == heights[off - 1]
              treeIndex == Lsr(index, nodeHeight + 1)
              addrIndex == treeIndex + Lsr(offset0, nodeHeight + 1)
              merged == H(nodeHeight + 1, addrIndex, stack[off - 2], stack[off - 1])
              newOff == off - 1
              lvl == nodeHeight + 1          \* heights.(!offset - 1) after the update
          IN /\ stack' = [stack EXCEPT ![off - 2] = merged]
             /\ heights' = [heights EXCEPT ![newOff - 1] = lvl]
             /\ off' = newOff
             /\ IF leafIdx >= 0 /\ Xor1(Lsr(leafIdx, lvl)) = treeIndex
                THEN IF lvl < height
                     THEN /\ auth' = [auth EXCEPT ![lvl] = merged]
                          /\ authWrites' = [authWrites EXCEPT ![lvl] = @ + 1]
                          /\ UNCHANGED fault
                     ELSE /\ fault' = "merge: authentication write at level >= height"
                          /\ UNCHANGED <<auth, authWrites>>
                ELSE UNCHANGED <<auth, authWrites, fault>>
             /\ UNCHANGED <<index, phase>>
     ELSE /\ index' = index + 1
          /\ phase' = "push"
          /\ UNCHANGED <<stack, heights, off, auth, authWrites, fault>>
  /\ UNCHANGED <<captured, root, clevel, cnode>>

(* compute_root loop body                                                  *)
ComputeRoot ==
  /\ phase = "croot"
  /\ IF clevel < height
     THEN LET sibling == auth[clevel]
              addr == Lsr(leafIdx, clevel + 1) + Lsr(offset0, clevel + 1)
          IN /\ cnode' = IF Lsr(leafIdx, clevel) % 2 = 0
                         THEN H(clevel + 1, addr, cnode, sibling)
                         ELSE H(clevel + 1, addr, sibling, cnode)
             /\ clevel' = clevel + 1
             /\ UNCHANGED phase
     ELSE /\ phase' = "done" /\ UNCHANGED <<clevel, cnode>>
  /\ UNCHANGED <<stack, heights, off, auth, authWrites, index, captured, root, fault>>

Step ==
  /\ (Push \/ Merge \/ ComputeRoot)
  /\ steps' = steps + 1
  /\ UNCHANGED <<height, t, offset0, leafIdx>>

Terminated == phase = "done" /\ UNCHANGED vars

Next == Step \/ Terminated
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
NoFault == fault = "none"

TypeOK ==
  /\ off \in 0 .. height + 1
  /\ phase \in {"push", "merge", "croot", "done"}
  /\ index \in 0 .. 2 ^ height
  /\ \A p \in 0 .. height : heights[p] \in 0 .. height

\* first leaf (local index) covered by stack entry p
RECURSIVE Start(_)
Start(p) == IF p = 0 THEN 0 ELSE Start(p - 1) + 2 ^ heights[p - 1]

StackInv ==
  phase \in {"push", "merge"} =>
    /\ \A p \in 0 .. off - 3 : heights[p] > heights[p + 1]
    /\ off >= 2 => heights[off - 2] >= heights[off - 1]
    /\ \A p \in 0 .. off - 1 :
         stack[p] = Node(Lsr(offset0, heights[p]) + Start(p) \div 2 ^ heights[p], heights[p])

RootOK == phase \in {"croot", "done"} => root = Node(t, height)

AuthOK ==
  phase \in {"croot", "done"} =>
    IF leafIdx >= 0
    THEN \A j \in 0 .. height - 1 : auth[j] = FipsAuth(t, height, leafIdx, j) /\ authWrites[j] = 1
    ELSE \A j \in 0 .. height - 1 : authWrites[j] = 0

CaptureOnce == phase \in {"croot", "done"} => captured = IF leafIdx >= 0 THEN 1 ELSE 0

ComputeRootOK ==
  (phase = "done" /\ leafIdx >= 0) =>
    /\ cnode = root
    /\ FipsPkFromSig(t, height, leafIdx, auth) = root

StepBound == steps <= 3 * 2 ^ height + height + 2
=============================================================================
