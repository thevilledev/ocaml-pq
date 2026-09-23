------------------------------ MODULE SlhSha2Pad ------------------------------
(***************************************************************************)
(* SHA-256 / SHA-512 message padding, MGF1 and the HMAC key block used by  *)
(* the SLH-DSA SHA2 parameter sets.                                        *)
(*                                                                         *)
(* OCaml modelled (slhdsa/slhdsa_hash.ml):                                 *)
(*   sha256, lines 162-173 and the block loop header of line 182:          *)
(*     padded_length = ((len + 9 + 63) / 64) * 64, 0x80 after the message, *)
(*     the loop writing the 8 bytes of len * 8 (Int64) big-endian at the   *)
(*     end, and padded_length / 64 compression calls;                      *)
(*   sha512, lines 269-276, 284: padded_length = ((len + 17 + 127) / 128)  *)
(*     * 128, 0x80, set_u64_be of len * 8 at padded_length - 8 (the upper  *)
(*     64 bits of the 128-bit length stay 0 from Bytes.make);              *)
(*   mgf1, lines 329-337: blocks = ceil(m / digest), hash(seed ||          *)
(*     set_u32_be counter), String.sub 0 m (set_u32_be, lines 126-137);    *)
(*   hmac, lines 321-324: key block K0 (ASSUME).                           *)
(*                                                                         *)
(* Checked against FIPS 180-4 Section 5.1.1 / 5.1.2 (append bit 1, the     *)
(* least k >= 0 zero bits with l + 1 + k = 448 mod 512 (resp. 896 mod      *)
(* 1024), then the 64-bit (resp. 128-bit) big-endian l) and 5.2 (number of *)
(* blocks), RFC 8017 Appendix B.2.1 (MGF1, as referenced by FIPS 205       *)
(* Section 11.2) and FIPS 198-1 Section 4 steps 1-3 (K0).                  *)
(*                                                                         *)
(* Abstraction: message bytes are symbolic atoms <<"m", i>> (the padding   *)
(* code only moves them), pad bytes are concrete; compression functions    *)
(* and hashes are opaque, so MGF1's i-th hash output byte j is the atom    *)
(* <<"h", i, j>> and its input is recorded.  Bit-level FIPS padding is     *)
(* converted to bytes big-endian within bytes (FIPS 180-4 convention).     *)
(*                                                                         *)
(* Constants: MaxBlocks (message lengths 0 .. MaxBlocks * block size - 1   *)
(* for both hashes, covering every length mod the block size), MgfMax      *)
(* (MGF1 output lengths 0 .. MgfMax for digest sizes 32 and 64; the real   *)
(* m is 30 .. 49).                                                         *)
(*                                                                         *)
(* Properties: PadOK (padded buffer and block count = FIPS 180-4), NoFault *)
(* (writes inside the buffer, 0x80 does not overwrite the length),         *)
(* MgfOK (output = leading m bytes of H(seed||C(0)) || H(seed||C(1)) ...), *)
(* StepBound; ASSUME for the HMAC key block.                               *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, TLC

CONSTANTS MaxBlocks, MgfMax

\* bytes are either symbolic message bytes <<"m", i>> or constants <<"c", v>>
C(v) == <<"c", v>>
M(i) == <<"m", i>>

(***************************************************************************)
(* FIPS 180-4 5.1.1 / 5.1.2 at the bit level, then grouped into bytes.     *)
(*   blockBits = 512 / 1024, lenBits = 64 / 128                            *)
(***************************************************************************)
FipsPadded(L, blockBits, lenBits) ==
  LET l == 8 * L
      k == (blockBits - lenBits - ((l + 1) % blockBits) + blockBits) % blockBits
      total == l + 1 + k + lenBits
      \* bit p of the padded message, big-endian within bytes
      Bit(p) == IF p = l THEN 1
                ELSE IF p < l + 1 + k THEN 0
                ELSE LET q == p - (l + 1 + k)          \* index in the length field
                         e == lenBits - 1 - q          \* weight 2^e
                     IN IF e > 30 THEN 0 ELSE (l \div 2 ^ e) % 2
      ByteVal(b) == LET R[t \in 0 .. 8] == IF t = 0 THEN 0 ELSE 2 * R[t - 1] + Bit(8 * b + t - 1)
                    IN R[8]
  IN [b \in 0 .. total \div 8 - 1 |-> IF b < L THEN M(b) ELSE C(ByteVal(b))]

VARIABLES alg, L, padded, lenIdx, blocks, pc, steps, fault,
          mgfDigest, mgfLen, mgfCounter, mgfOut, mgfInputs

vars == <<alg, L, padded, lenIdx, blocks, pc, steps, fault,
          mgfDigest, mgfLen, mgfCounter, mgfOut, mgfInputs>>

BlockSize(a) == IF a = "sha256" THEN 64 ELSE 128
PaddedLength(a, len) ==
  IF a = "sha256" THEN ((len + 9 + 63) \div 64) * 64 ELSE ((len + 17 + 127) \div 128) * 128

Init ==
  /\ steps = 0 /\ fault = "none"
  /\ \/ /\ alg \in {"sha256", "sha512"}
        /\ L \in 0 .. MaxBlocks * BlockSize(alg) - 1
        \* Bytes.make padded_length '\000'; blit input; set padded.[len] 0x80
        /\ padded = [b \in 0 .. PaddedLength(alg, L) - 1 |->
                       IF b < L THEN M(b) ELSE IF b = L THEN C(128) ELSE C(0)]
        /\ lenIdx = 0 /\ blocks = 0 /\ pc = "len"
        /\ mgfDigest = 0 /\ mgfLen = 0 /\ mgfCounter = 0 /\ mgfOut = <<>> /\ mgfInputs = <<>>
     \/ /\ alg = "mgf1" /\ L = 0 /\ padded = <<>> /\ lenIdx = 0 /\ blocks = 0
        /\ mgfDigest \in {32, 64} /\ mgfLen \in 0 .. MgfMax
        /\ mgfCounter = 0 /\ mgfOut = <<>> /\ mgfInputs = <<>> /\ pc = "mgf"

\* sha256: for i = 0 to 7: padded.[padded_length - 1 - i] <- (bit_length lsr (8 i)) land 0xff
\* sha512: set_u64_be padded (padded_length - 8) bit_length: byte i = bit_length lsr (8 (7 - i))
LenStep ==
  /\ pc = "len"
  /\ IF lenIdx < 8
     THEN LET pl == PaddedLength(alg, L)
              bitLength == L * 8
              pos == IF alg = "sha256" THEN pl - 1 - lenIdx ELSE pl - 8 + lenIdx
              shift == IF alg = "sha256" THEN 8 * lenIdx ELSE 8 * (7 - lenIdx)
              v == IF shift > 30 THEN 0 ELSE (bitLength \div 2 ^ shift) % 256
          IN /\ padded' = [padded EXCEPT ![pos] = C(v)]
             /\ lenIdx' = lenIdx + 1
             /\ fault' = IF pos \notin DOMAIN padded THEN "length write outside buffer"
                         ELSE IF pos <= L THEN "length overwrites message or 0x80"
                         ELSE fault
             /\ UNCHANGED <<blocks, pc>>
     ELSE /\ pc' = "blocks" /\ UNCHANGED <<padded, lenIdx, blocks, fault>>
  /\ UNCHANGED <<alg, L, mgfDigest, mgfLen, mgfCounter, mgfOut, mgfInputs>>

(* for block = 0 to (padded_length / block_size) - 1 do compress ... done  *)
BlockStep ==
  /\ pc = "blocks"
  /\ IF blocks < PaddedLength(alg, L) \div BlockSize(alg)
     THEN blocks' = blocks + 1 /\ UNCHANGED pc
     ELSE pc' = "done" /\ UNCHANGED blocks
  /\ UNCHANGED <<alg, L, padded, lenIdx, fault, mgfDigest, mgfLen, mgfCounter, mgfOut, mgfInputs>>

(* mgf1: for counter = 0 to blocks - 1 do                                  *)
\* encoded = set_u32_be (Int32.of_int counter); add (hash (seed ^ encoded))
(* done; String.sub (Buffer.contents result) 0 output_length               *)
MgfStep ==
  /\ pc = "mgf"
  /\ LET nblocks == (mgfLen + mgfDigest - 1) \div mgfDigest
     IN IF mgfCounter < nblocks
        THEN LET encoded == <<(mgfCounter \div 2 ^ 24) % 256, (mgfCounter \div 2 ^ 16) % 256,
                              (mgfCounter \div 2 ^ 8) % 256, mgfCounter % 256>>
                 digest == [j \in 1 .. mgfDigest |-> <<"h", mgfCounter, j - 1>>]
             IN /\ mgfInputs' = Append(mgfInputs, encoded)
                /\ mgfOut' = mgfOut \o digest
                /\ mgfCounter' = mgfCounter + 1
                /\ UNCHANGED <<pc, fault>>
        ELSE /\ IF mgfLen <= Len(mgfOut)
                THEN /\ mgfOut' = SubSeq(mgfOut, 1, mgfLen) /\ UNCHANGED fault
                ELSE /\ fault' = "String.sub past the MGF1 buffer" /\ UNCHANGED mgfOut
             /\ pc' = "done"
             /\ UNCHANGED <<mgfCounter, mgfInputs>>
  /\ UNCHANGED <<alg, L, padded, lenIdx, blocks, mgfDigest, mgfLen>>

Step == (LenStep \/ BlockStep \/ MgfStep) /\ steps' = steps + 1
Terminated == pc = "done" /\ UNCHANGED vars
Next == Step \/ Terminated
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
NoFault == fault = "none"

PadOK ==
  (pc = "done" /\ alg \in {"sha256", "sha512"}) =>
    LET f == IF alg = "sha256" THEN FipsPadded(L, 512, 64) ELSE FipsPadded(L, 1024, 128)
    IN /\ padded = f
       /\ blocks * BlockSize(alg) = PaddedLength(alg, L)

\* RFC 8017 B.2.1: T = T || Hash(mgfSeed || C) with C = I2OSP(counter, 4) for
\* counter = 0 .. ceil(maskLen / hLen) - 1; output the leading maskLen octets
I2OSP4(x) == <<(x \div 16777216) % 256, (x \div 65536) % 256, (x \div 256) % 256, x % 256>>
MgfOK ==
  (pc = "done" /\ alg = "mgf1") =>
    /\ Len(mgfOut) = mgfLen
    /\ \A q \in 1 .. mgfLen : mgfOut[q] = <<"h", (q - 1) \div mgfDigest, (q - 1) % mgfDigest>>
    /\ Len(mgfInputs) = (mgfLen + mgfDigest - 1) \div mgfDigest
    /\ \A c \in 1 .. Len(mgfInputs) : mgfInputs[c] = I2OSP4(c - 1)

StepBound == steps <= 8 + 2 * MaxBlocks + 3 + MgfMax

(***************************************************************************)
(* HMAC key block (FIPS 198-1 steps 1-3) vs hmac, lines 321-323, for every *)
(* key length 0 .. 2B + 1 (B = 64, 128); H(K) is the opaque <<"H", len>>.  *)
(***************************************************************************)
OcamlK0(len, B, hlen) ==
  LET key == IF len > B THEN [i \in 0 .. hlen - 1 |-> <<"H", len, i>>]
             ELSE [i \in 0 .. len - 1 |-> <<"k", len, i>>]
      klen == IF len > B THEN hlen ELSE len
  IN [i \in 0 .. B - 1 |-> IF i < klen THEN key[i] ELSE <<"z", 0, 0>>]   \* key ^ String.make (B - |key|) '\000'
FipsK0(len, B, hlen) ==
  IF len = B THEN [i \in 0 .. B - 1 |-> <<"k", len, i>>]                             \* step 1
  ELSE IF len > B THEN [i \in 0 .. B - 1 |-> IF i < hlen THEN <<"H", len, i>> ELSE <<"z", 0, 0>>] \* step 2
  ELSE [i \in 0 .. B - 1 |-> IF i < len THEN <<"k", len, i>> ELSE <<"z", 0, 0>>]     \* step 3
ASSUME \A x \in {<<64, 32>>, <<128, 64>>} : \A len \in 0 .. 2 * x[1] + 1 :
         OcamlK0(len, x[1], x[2]) = FipsK0(len, x[1], x[2])
=============================================================================
