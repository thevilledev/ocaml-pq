----------------------------- MODULE KeccakSponge -----------------------------
(***************************************************************************)
(* Keccak sponge driver: absorb loop, tail padding and squeeze loop, with  *)
(* an abstract permutation.                                                *)
(*                                                                         *)
(* OCaml modelled: lib/keccak.ml `sponge`, lines 87-115, with load64_le,   *)
(* store64_le and xor_block (lines 68-85).  mldsa/mldsa_keccak.ml and the  *)
(* Keccak part of slhdsa/slhdsa_hash.ml contain the identical function.    *)
(*                                                                         *)
(* Checked against FIPS 202 Algorithm 8 (SPONGE[f, pad, r]) with           *)
(* Algorithm 9 (pad10*1), SHA3-x(M) = KECCAK[c](M || 01, d) and            *)
(* SHAKEx(M, d) = KECCAK[c](M || 1111, d) (Sections 6.1, 6.2), at the bit  *)
(* level, with the byte/bit conventions of Appendix B.1 (bit 8k + t of a   *)
(* string is bit t of byte k) and the state layout of Section 3.1.2 (lane  *)
(* x + 5y holds state bits 64(5y + x) .. 64(5y + x) + 63).                 *)
(*                                                                         *)
(* Abstraction: message bytes are symbolic (bit t of input byte i is the   *)
(* atom <<"m", i, t>>, a constant 1 bit is <<"one", 0, 0>>, a bit is the   *)
(* set of atoms XOR/OR-ed into it, {} = 0).  The permutation is opaque:    *)
(* absorption is checked by comparing the sequence of rate-bit strings     *)
(* XORed into the state before each permutation, and squeezing starts from *)
(* an arbitrary state whose bit z after the m-th squeeze permutation is    *)
(* the atom <<"s", m, z>>.  Absorb and squeeze are independent (squeeze    *)
(* only sees the state), so they are separate behaviours.                  *)
(*                                                                         *)
(* Constants: Configs = set of [rate (bytes), kind ("SHA3" / "SHAKE")];    *)
(* the cfg uses the four real instances (SHA3-256 136, SHA3-512 72,        *)
(* SHAKE128 168, SHAKE256 136) and abstract rates 8 and 16 with both       *)
(* suffixes.  All input lengths 0 .. 2 * rate (every tail length rem in    *)
(* 0 .. rate - 1, including rem = rate - 1 where suffix and 0x80 share a   *)
(* byte) and all output lengths 0 .. 3 * rate are explored.                *)
(*                                                                         *)
(* Properties:                                                             *)
(*   AbsorbOK      - the blocks XORed into the state, lane by lane via     *)
(*                   load64_le, are exactly FIPS's P_i || 0^c, and the     *)
(*                   number of absorb permutations is len(P) / r;          *)
(*   TailBytesOK   - the tail block is the byte-level pad10*1 with suffix  *)
(*                   (message, suffix byte, zeros, last byte | 0x80);      *)
(*   SqueezeOK     - output = Trunc_d(Z) of FIPS's squeeze loop and the    *)
(*                   number of squeeze permutations is max(0, ceil(d/r)-1);*)
(*   PrefixOK      - output byte i depends only on i (so a shorter output  *)
(*                   is a prefix of a longer one, as the samplers assume); *)
(*   StepBound     - termination bound.                                    *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT Configs

One == {<<"one", 0, 0>>}
MsgByte(i) == [t \in 0 .. 7 |-> {<<"m", i, t>>}]
ConstByte(v) == [t \in 0 .. 7 |-> IF (v \div 2 ^ t) % 2 = 1 THEN One ELSE {}]
ByteOr(a, b) == [t \in 0 .. 7 |-> a[t] \cup b[t]]
SuffixByte(kind) == IF kind = "SHAKE" THEN 31 ELSE 6        \* 0x1f / 0x06

(***************************************************************************)
(* OCaml lane helpers                                                      *)
(***************************************************************************)
\* load64_le s off: r := r lor (byte (off + i) lsl (8 * i)), i = 0 .. 7
Load64Le(block, off) == [z \in 0 .. 63 |-> block[off + z \div 8][z % 8]]
\* xor_block state block: lanes i = 0 .. len/8 - 1; returns the bits XORed
\* into state bits 0 .. 8 * rate - 1 (lane i covers bits 64 i .. 64 i + 63)
XorBlockBits(block, rate) ==
  [k \in 0 .. 8 * rate - 1 |->
     IF k \div 64 < rate \div 8 THEN Load64Le(block, 8 * (k \div 64))[k % 64] ELSE {}]

(***************************************************************************)
(* FIPS 202: N = M || suffix bits; P = N || pad10*1(r, len(N)).            *)
(***************************************************************************)
SuffixBits(kind) == IF kind = "SHAKE" THEN <<1, 1, 1, 1>> ELSE <<0, 1>>
\* Algorithm 9 pad10*1(x, m): j = (-m - 2) mod x; return 1 || 0^j || 1
ASSUME (-3) % 8 = 5 /\ (-10) % 8 = 6      \* TLA+ mod is non-negative
PadBits(x, m) == LET j == (-m - 2) % x IN [i \in 1 .. j + 2 |-> IF i = 1 \/ i = j + 2 THEN 1 ELSE 0]
FipsP(c, L) ==
  LET mbits == 8 * L
      sfx == SuffixBits(c.kind)
      nlen == mbits + Len(sfx)
      pad == PadBits(8 * c.rate, nlen)
  IN [k \in 0 .. nlen + Len(pad) - 1 |->
        IF k < mbits THEN {<<"m", k \div 8, k % 8>>}
        ELSE IF k < nlen THEN (IF sfx[k - mbits + 1] = 1 THEN One ELSE {})
        ELSE (IF pad[k - nlen + 1] = 1 THEN One ELSE {})]
FipsNumBlocks(c, L) == Cardinality(DOMAIN FipsP(c, L)) \div (8 * c.rate)
\* P_i || 0^c restricted to the rate part (the capacity part is 0^c)
FipsBlock(c, L, i) == [k \in 0 .. 8 * c.rate - 1 |-> FipsP(c, L)[i * 8 * c.rate + k]]

\* FIPS squeeze: Z = Trunc_r(S_0) || Trunc_r(S_1) || ...; byte q of Z
FipsStreamByte(c, q) == [t \in 0 .. 7 |-> {<<"s", q \div c.rate, 8 * (q % c.rate) + t>>}]
FipsSqueezePerms(c, d) == IF d = 0 THEN 0 ELSE (d + c.rate - 1) \div c.rate - 1

VARIABLES
  cfg, mode, L, d,
  blk, aphase, absorbed, tail,       \* absorb
  produced, sqPerms, out,            \* squeeze
  steps

vars == <<cfg, mode, L, d, blk, aphase, absorbed, tail, produced, sqPerms, out, steps>>

Init ==
  /\ cfg \in Configs
  /\ mode \in {"absorb", "squeeze"}
  /\ IF mode = "absorb" THEN L \in 0 .. 2 * cfg.rate /\ d = 0
                        ELSE L = 0 /\ d \in 0 .. 3 * cfg.rate
  /\ blk = 0 /\ aphase = IF mode = "absorb" THEN "full" ELSE "done"
  /\ absorbed = <<>> /\ tail = <<>>
  /\ produced = 0 /\ sqPerms = 0 /\ out = <<>>
  /\ steps = 0

FullBlocks == L \div cfg.rate

\* for block = 0 to full_blocks - 1 do xor_block state (String.sub input (block * rate) rate); permute state
AbsorbFull ==
  /\ mode = "absorb" /\ aphase = "full"
  /\ IF blk < FullBlocks
     THEN LET sub == [p \in 0 .. cfg.rate - 1 |-> MsgByte(blk * cfg.rate + p)]
          IN /\ absorbed' = Append(absorbed, XorBlockBits(sub, cfg.rate))
             /\ blk' = blk + 1
             /\ UNCHANGED aphase
     ELSE /\ aphase' = "tail" /\ UNCHANGED <<absorbed, blk>>
  /\ UNCHANGED <<tail, produced, sqPerms, out>>

\* rem = len mod rate; tail = Bytes.make rate 0; blit; tail.[rem] <- suffix;
(* tail.[rate-1] <- tail.[rate-1] lor 0x80; xor_block state tail; permute  *)
AbsorbTail ==
  /\ mode = "absorb" /\ aphase = "tail"
  /\ LET rem == L % cfg.rate
         t0 == [p \in 0 .. cfg.rate - 1 |->
                  IF p < rem THEN MsgByte(FullBlocks * cfg.rate + p) ELSE ConstByte(0)]
         t1 == [t0 EXCEPT ![rem] = ConstByte(SuffixByte(cfg.kind))]
         t2 == [t1 EXCEPT ![cfg.rate - 1] = ByteOr(t1[cfg.rate - 1], ConstByte(128))]
     IN /\ tail' = t2
        /\ absorbed' = Append(absorbed, XorBlockBits(t2, cfg.rate))
  /\ aphase' = "done"
  /\ UNCHANGED <<blk, produced, sqPerms, out>>

(* while !produced < output_length do                                      *)
(*   take = min rate (output_length - produced); block = store64_le lanes; *)
(*   blit block 0 out produced take; produced += take;                     *)
(*   if produced < output_length then permute state done                   *)
Squeeze ==
  /\ mode = "squeeze" /\ produced < d
  /\ LET take == IF cfg.rate < d - produced THEN cfg.rate ELSE d - produced
         \* store64_le block (8 i) state.(i): byte 8i + j = bits 8j .. 8j+7 of lane i
         block == [p \in 0 .. cfg.rate - 1 |->
                     [t \in 0 .. 7 |-> {<<"s", sqPerms, 64 * (p \div 8) + 8 * (p % 8) + t>>}]]
     IN /\ out' = out \o [q \in 1 .. take |-> block[q - 1]]
        /\ produced' = produced + take
        /\ sqPerms' = IF produced + take < d THEN sqPerms + 1 ELSE sqPerms
  /\ UNCHANGED <<blk, aphase, absorbed, tail>>

Step == (AbsorbFull \/ AbsorbTail \/ Squeeze) /\ steps' = steps + 1 /\ UNCHANGED <<cfg, mode, L, d>>

Finished == (mode = "absorb" /\ aphase = "done") \/ (mode = "squeeze" /\ produced >= d)
Terminated == Finished /\ UNCHANGED vars
Next == Step \/ Terminated
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
AbsorbOK ==
  (mode = "absorb" /\ aphase = "done") =>
    /\ Len(absorbed) = FipsNumBlocks(cfg, L)          \* one permute per block
    /\ \A i \in 1 .. Len(absorbed) : absorbed[i] = FipsBlock(cfg, L, i - 1)

TailBytesOK ==
  (mode = "absorb" /\ aphase = "done") =>
    LET rem == L % cfg.rate
        s == SuffixByte(cfg.kind)
    IN \A p \in 0 .. cfg.rate - 1 :
         tail[p] = IF p < rem THEN MsgByte(FullBlocks * cfg.rate + p)
                   ELSE IF p = cfg.rate - 1 /\ p = rem THEN ConstByte(s + 128)
                   ELSE IF p = rem THEN ConstByte(s)
                   ELSE IF p = cfg.rate - 1 THEN ConstByte(128)
                   ELSE ConstByte(0)

SqueezeOK ==
  (mode = "squeeze" /\ produced >= d) =>
    /\ Len(out) = d
    /\ sqPerms = FipsSqueezePerms(cfg, d)

PrefixOK == \A q \in 1 .. Len(out) : out[q] = FipsStreamByte(cfg, q - 1)

StepBound == steps <= 3 * 3 + 3

(***************************************************************************)
(* Configurations                                                          *)
(***************************************************************************)
RealConfigs == { [rate |-> 136, kind |-> "SHA3"], [rate |-> 72, kind |-> "SHA3"],
                 [rate |-> 168, kind |-> "SHAKE"], [rate |-> 136, kind |-> "SHAKE"] }
AbstractConfigs == { [rate |-> r, kind |-> k] : r \in {8, 16}, k \in {"SHA3", "SHAKE"} }
AllConfigs == RealConfigs \cup AbstractConfigs
=============================================================================
