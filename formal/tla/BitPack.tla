-------------------------------- MODULE BitPack --------------------------------
(***************************************************************************)
(* Accumulator bit packers of ML-DSA and ML-KEM, and ML-KEM's              *)
(* compress/decompress arithmetic.                                         *)
(*                                                                         *)
(* OCaml modelled:                                                         *)
(*   mldsa/mldsa_engine.ml pack_codes / unpack_codes, lines 265-300        *)
(*     (kind "dsa": accumulator is an OCaml int, 63 bits);                 *)
(*   lib/mlkem_engine.ml encode_compressed / decode_compressed, lines      *)
(*     255-287 (kind "kem": Int64 accumulator, set_u8 masks with 0xff,     *)
(*     decode masks Int64.to_int acc with (1 lsl d) - 1);                  *)
(*   lib/mlkem_engine.ml compress / decompress, lines 125-137 (ASSUMEs,    *)
(*     all inputs, d in {1, 4, 5, 10, 11});                                *)
(*   lib/mlkem_engine.ml encode_12 / decode_12, lines 230-253 (ASSUME,     *)
(*     n = 256, symbolic).                                                 *)
(*                                                                         *)
(* Checked against FIPS 204 Algorithms 16 and 18 (SimpleBitPack,           *)
(* SimpleBitUnpack, via IntegerToBits / BitsToBytes / BytesToBits,         *)
(* Algorithms 9, 12, 13) and FIPS 203 Algorithms 5 and 6 (ByteEncode_d,    *)
(* ByteDecode_d) and Section 4.2.1 (Compress_d, Decompress_d).             *)
(*                                                                         *)
(* Abstraction: symbolic bits.  Bit j of code i is the atom <<"c", i, j>>, *)
(* bit t of input byte k is the atom <<"b", k, t>>; an integer is a vector *)
(* of positions (63 for an OCaml int, 64 for Int64) each holding the set   *)
(* of atoms OR-ed into it ({} = 0).  lor = union, lsl/lsr = shifts that    *)
(* drop bits leaving the word (flagged), land with a constant mask =       *)
(* restriction.  These operations are exact bit-level semantics, so one    *)
(* symbolic run per (kind, width, count) covers every input: every code    *)
(* value < 2^b (the callers' precondition: they pack gamma1 - z, eta - s,  *)
(* 2^12 - t0, t1, w1, compress(x, d)) and every byte string.               *)
(*                                                                         *)
(* Behaviours: "fromCodes" packs count symbolic codes then unpacks the     *)
(* result; "fromBytes" unpacks ceil(count*b/8) symbolic bytes then packs   *)
(* the result.                                                             *)
(*                                                                         *)
(* Constants: Configs = set of [kind, bits, count]; the cfg uses the real  *)
(* widths with count = 256 (ML-DSA 3, 4, 6, 10, 13, 18, 20; ML-KEM 1, 4,   *)
(* 5, 10, 11) and a sweep of all widths 1..20 (dsa) / 1..12 (kem) with     *)
(* counts 1..9 (every residue of count * b mod 8).                         *)
(*                                                                         *)
(* Properties:                                                             *)
(*   NoFault      - no byte written/read outside the buffer, no bit        *)
(*                  shifted out of the accumulator word, no overlapping    *)
(*                  lor;                                                   *)
(*   AccRange     - the accumulator only holds bits below `available`,     *)
(*                  and available < b + 8, i.e. accumulator < 2^(b+7);     *)
(*   BytesWritten - pack writes exactly count * b / 8 bytes;               *)
(*   PackIsFIPS   - pack output = BitsToBytes(IntegerToBits(w_0, b) || ...)*)
(*   UnpackIsFIPS - unpack output = SimpleBitUnpack / ByteDecode_d;        *)
(*   RoundTrips   - unpack(pack(x)) = x and pack(unpack(s)) = s whenever   *)
(*                  count * b is a multiple of 8;                          *)
(*   StepBound    - termination bound.                                     *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANT Configs

AccW(c) == IF c.kind = "dsa" THEN 63 ELSE 64
OutLen(c) == (c.count * c.bits) \div 8             \* Bytes.make (n * bits / 8)
InLen(c) == (c.count * c.bits + 7) \div 8        \* bytes fed to unpack (fromBytes)
UnpackCount(c, m) == (m * 8) \div c.bits           \* dsa: String.length input * 8 / bits

CodeAtoms(c, i) == [p \in 0 .. AccW(c) - 1 |-> IF p < c.bits THEN {<<"c", i, p>>} ELSE {}]
ByteAtoms(k) == [t \in 0 .. 7 |-> {<<"b", k, t>>}]

\* word operations on a w-position vector; ShlLost/lsr drop bits
Shl(v, s, w) == [p \in 0 .. w - 1 |-> IF p >= s THEN v[p - s] ELSE {}]
ShlLost(v, s, w) == \E p \in 0 .. w - 1 : p + s >= w /\ v[p] # {}
Shr(v, s, w) == [p \in 0 .. w - 1 |-> IF p + s < w THEN v[p + s] ELSE {}]
Or(v, u, w) == [p \in 0 .. w - 1 |-> v[p] \cup u[p]]
Overlap(v, u, w) == \E p \in 0 .. w - 1 : v[p] # {} /\ u[p] # {}
LowBits(v, k) == [p \in 0 .. k - 1 |-> v[p]]                 \* land (2^k - 1)
Widen(byte, w) == [p \in 0 .. w - 1 |-> IF p < 8 THEN byte[p] ELSE {}]
WidenCode(code, w) == [p \in 0 .. w - 1 |-> IF p \in DOMAIN code THEN code[p] ELSE {}]

(***************************************************************************)
(* FIPS: bit k of the concatenated bit string of codes; byte B bit t of    *)
(* BitsToBytes is bit 8B + t; code i bit j of BytesToBits is bit ib + j.   *)
(***************************************************************************)
FipsPackBit(c, B, t) == {<<"c", (8 * B + t) \div c.bits, (8 * B + t) % c.bits>>}
FipsUnpackBit(c, i, j) == {<<"b", (i * c.bits + j) \div 8, (i * c.bits + j) % 8>>}

VARIABLES
  cfg, pipeline, phase,
  codesIn,          \* codes given to pack (function i -> AccW vector)
  bytesIn,          \* bytes given to unpack (function k -> 8-bit vector)
  pIdx, pAcc, pAvail, pPos, pOut, pInner,
  uIdx, uAcc, uAvail, uPos, uOut, uInner, uCount,
  steps, fault

vars == <<cfg, pipeline, phase, codesIn, bytesIn, pIdx, pAcc, pAvail, pPos, pOut,
          pInner, uIdx, uAcc, uAvail, uPos, uOut, uInner, uCount, steps, fault>>

ZeroW(w) == [p \in 0 .. w - 1 |-> {}]
ZeroByte == [t \in 0 .. 7 |-> {}]

PackReset(c, codes) ==
  /\ codesIn' = codes
  /\ pIdx' = 0 /\ pAcc' = ZeroW(AccW(c)) /\ pAvail' = 0 /\ pPos' = 0
  \* Bytes.make (Array.length codes * bits / 8)
  /\ pOut' = [k \in 0 .. (Cardinality(DOMAIN codes) * c.bits) \div 8 - 1 |-> ZeroByte]
  /\ pInner' = FALSE

UnpackReset(c, bytes) ==
  /\ bytesIn' = bytes
  /\ uIdx' = 0 /\ uAcc' = ZeroW(AccW(c)) /\ uAvail' = 0 /\ uPos' = 0
  /\ uCount' = UnpackCount(c, Cardinality(DOMAIN bytes))
  /\ uOut' = [i \in 0 .. UnpackCount(c, Cardinality(DOMAIN bytes)) - 1 |-> [j \in 0 .. c.bits - 1 |-> {}]]
  /\ uInner' = FALSE

Init ==
  /\ cfg \in Configs
  /\ pipeline \in {"fromCodes", "fromBytes"}
  /\ steps = 0 /\ fault = "none"
  /\ IF pipeline = "fromCodes"
     THEN /\ phase = "pack"
          /\ codesIn = [i \in 0 .. cfg.count - 1 |-> CodeAtoms(cfg, i)]
          /\ bytesIn = [k \in {} |-> ZeroByte]
     ELSE /\ phase = "unpack"
          /\ codesIn = [i \in {} |-> ZeroW(AccW(cfg))]
          /\ bytesIn = [k \in 0 .. InLen(cfg) - 1 |-> ByteAtoms(k)]
  /\ pIdx = 0 /\ pAcc = ZeroW(AccW(cfg)) /\ pAvail = 0 /\ pPos = 0
  /\ pOut = [k \in 0 .. OutLen(cfg) - 1 |-> ZeroByte] /\ pInner = FALSE
  /\ uIdx = 0 /\ uAcc = ZeroW(AccW(cfg)) /\ uAvail = 0 /\ uPos = 0
  /\ uCount = UnpackCount(cfg, Cardinality(DOMAIN bytesIn))
  /\ uOut = [i \in 0 .. uCount - 1 |-> [j \in 0 .. cfg.bits - 1 |-> {}]]
  /\ uInner = FALSE

(***************************************************************************)
(* pack_codes / encode_compressed                                          *)
(*   accumulator := accumulator lor (value lsl available)                  *)
(*   available := available + bits                                         *)
(*   while available >= 8 do                                               *)
(*     set_u8 output position (accumulator land 0xff)                      *)
(*     incr position; accumulator := accumulator lsr 8;                    *)
(*     available := available - 8 done                                     *)
(***************************************************************************)
uVars == <<bytesIn, uIdx, uAcc, uAvail, uPos, uOut, uInner, uCount>>
pVars == <<codesIn, pIdx, pAcc, pAvail, pPos, pOut, pInner>>

PackStep ==
  /\ phase = "pack"
  /\ UNCHANGED <<cfg, pipeline, codesIn>>
  /\ LET w == AccW(cfg) IN
     IF ~pInner
     THEN IF pIdx < Cardinality(DOMAIN codesIn)
          THEN LET v == Shl(codesIn[pIdx], pAvail, w)
               IN /\ pAcc' = Or(pAcc, v, w)
                  /\ pAvail' = pAvail + cfg.bits
                  /\ pIdx' = pIdx + 1
                  /\ pInner' = TRUE
                  /\ fault' = IF ShlLost(codesIn[pIdx], pAvail, w) THEN "pack: bits shifted out"
                              ELSE IF Overlap(pAcc, v, w) THEN "pack: overlapping lor"
                              ELSE fault
                  /\ UNCHANGED <<pPos, pOut, phase>>
                  /\ UNCHANGED uVars
          ELSE \* pack finished
               /\ UNCHANGED <<pIdx, pAcc, pAvail, pPos, pOut, pInner, fault>>
               /\ IF pipeline = "fromCodes"
                  THEN /\ phase' = "unpack"
                       /\ UnpackReset(cfg, pOut)
                  ELSE /\ phase' = "done"
                       /\ UNCHANGED uVars
     ELSE IF pAvail >= 8
          THEN /\ pOut' = [pOut EXCEPT ![pPos] = LowBits(pAcc, 8)]
               /\ pPos' = pPos + 1
               /\ pAcc' = Shr(pAcc, 8, w)
               /\ pAvail' = pAvail - 8
               /\ fault' = IF pPos \notin DOMAIN pOut THEN "pack: write past output" ELSE fault
               /\ UNCHANGED <<pIdx, pInner, phase>>
               /\ UNCHANGED uVars
          ELSE /\ pInner' = FALSE
               /\ UNCHANGED <<pIdx, pAcc, pAvail, pPos, pOut, phase, fault>>
               /\ UNCHANGED uVars

(***************************************************************************)
(* unpack_codes / decode_compressed                                        *)
(*   for index = 0 to count - 1 do                                         *)
(*     while available < bits do                                           *)
(*       accumulator := accumulator lor                                    *)
(*                      (get_u8 input position lsl available);             *)
(*       incr position; available := available + 8 done;                   *)
(*     output.(index) <- accumulator land mask;                            *)
(*     accumulator := accumulator lsr bits; available := available - bits  *)
(***************************************************************************)
UnpackStep ==
  /\ phase = "unpack"
  /\ UNCHANGED <<cfg, pipeline, bytesIn, uInner, uCount>>
  /\ LET w == AccW(cfg) IN
     IF uIdx < uCount
     THEN /\ UNCHANGED <<phase, codesIn, pIdx, pAcc, pAvail, pPos, pOut, pInner>>
          /\ IF uAvail < cfg.bits
             THEN LET v == Shl(Widen(bytesIn[uPos], w), uAvail, w)
                  IN /\ uAcc' = Or(uAcc, v, w)
                     /\ uPos' = uPos + 1
                     /\ uAvail' = uAvail + 8
                     /\ fault' = IF uPos \notin DOMAIN bytesIn THEN "unpack: read past input"
                                 ELSE IF ShlLost(Widen(bytesIn[uPos], w), uAvail, w)
                                      THEN "unpack: bits shifted out"
                                 ELSE IF Overlap(uAcc, v, w) THEN "unpack: overlapping lor"
                                 ELSE fault
                     /\ UNCHANGED <<uIdx, uOut>>
             ELSE \* kem: (Int64.to_int acc) land mask; dsa: acc land mask
                  /\ uOut' = [uOut EXCEPT ![uIdx] = LowBits(uAcc, cfg.bits)]
                  /\ uAcc' = Shr(uAcc, cfg.bits, w)
                  /\ uAvail' = uAvail - cfg.bits
                  /\ uIdx' = uIdx + 1
                  /\ UNCHANGED <<uPos, fault>>
     ELSE \* unpack finished
          /\ UNCHANGED <<uIdx, uAcc, uAvail, uPos, uOut, fault>>
          /\ IF pipeline = "fromBytes"
             THEN /\ phase' = "pack"
                  /\ PackReset(cfg, [i \in 0 .. uCount - 1 |-> WidenCode(uOut[i], w)])
             ELSE /\ phase' = "done"
                  /\ UNCHANGED <<codesIn, pIdx, pAcc, pAvail, pPos, pOut, pInner>>

Terminated == phase = "done" /\ UNCHANGED vars
Next == ((PackStep \/ UnpackStep) /\ steps' = steps + 1) \/ Terminated
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
NoFault == fault = "none"

AccRange ==
  /\ \A p \in 0 .. AccW(cfg) - 1 : p >= pAvail => pAcc[p] = {}
  /\ \A p \in 0 .. AccW(cfg) - 1 : p >= uAvail => uAcc[p] = {}
  /\ pAvail < cfg.bits + 8 /\ uAvail < cfg.bits + 8

PackedBytesOK(c, out, ncodes) ==
  /\ Cardinality(DOMAIN out) = (ncodes * c.bits) \div 8
  /\ \A B \in DOMAIN out : \A t \in 0 .. 7 : out[B][t] = FipsPackBit(c, B, t)

BytesWritten ==
  (phase = "done" /\ pipeline = "fromCodes") => pPos = OutLen(cfg)

PackIsFIPS ==
  (pipeline = "fromCodes" /\ phase # "pack") => PackedBytesOK(cfg, pOut, cfg.count)

UnpackIsFIPS ==
  (pipeline = "fromBytes" /\ phase # "unpack") =>
    /\ uCount = (InLen(cfg) * 8) \div cfg.bits
    /\ \A i \in 0 .. uCount - 1 : \A j \in 0 .. cfg.bits - 1 : uOut[i][j] = FipsUnpackBit(cfg, i, j)

RoundTrips ==
  phase = "done" =>
    IF pipeline = "fromCodes"
    THEN /\ uCount = (OutLen(cfg) * 8) \div cfg.bits
         /\ \A i \in 0 .. uCount - 1 : WidenCode(uOut[i], AccW(cfg)) = CodeAtoms(cfg, i)
         /\ (cfg.count * cfg.bits) % 8 = 0 => uCount = cfg.count
    ELSE /\ pPos = (uCount * cfg.bits) \div 8
         /\ \A k \in 0 .. pPos - 1 : pOut[k] = bytesIn[k]
         /\ (InLen(cfg) * 8) % cfg.bits = 0 => pPos = InLen(cfg)

StepBound == steps <= 3 * cfg.count + 2 * InLen(cfg) + 25

(***************************************************************************)
(* ML-KEM compress / decompress (lib/mlkem_engine.ml 125-137), all inputs. *)
(* TLC integers are 32-bit, so (x lsl d) * 5039 is evaluated as            *)
(* floor((hi * 5039 + floor(lo * 5039 / 2^12)) / 2^12) with                *)
(* dividend = hi * 2^12 + lo, which is exactly floor(dividend*5039/2^24).  *)
(* ((threshold - remainder) lsr 63) land 1 on Int64 is the sign bit, i.e.  *)
(* 1 iff threshold < remainder.                                            *)
(***************************************************************************)
KQ == 3329
KemDs == {1, 4, 5, 10, 11}
OcamlCompress(x, d) ==
  LET dividend == x * 2 ^ d
      hi == dividend \div 2 ^ 12
      lo == dividend % 2 ^ 12
      quotient == (hi * 5039 + (lo * 5039) \div 2 ^ 12) \div 2 ^ 12
      remainder == dividend - quotient * KQ
      inc(threshold) == IF threshold - remainder < 0 THEN 1 ELSE 0
  IN (quotient + inc(KQ \div 2) + inc(KQ + KQ \div 2)) % 2 ^ d
OcamlDecompress(y, d) ==
  LET dividend == y * KQ
  IN (dividend \div 2 ^ d) + ((dividend \div 2 ^ (d - 1)) % 2)
\* FIPS 203 (4.7) Compress_d(x) = round((2^d / q) x) mod 2^d, round half up
FipsCompress(x, d) == ((2 ^ (d + 1) * x + KQ) \div (2 * KQ)) % 2 ^ d
\* FIPS 203 (4.8) Decompress_d(y) = round((q / 2^d) y)
FipsDecompress(y, d) == (2 * KQ * y + 2 ^ d) \div 2 ^ (d + 1)

ASSUME \A d \in KemDs : \A x \in 0 .. KQ - 1 : OcamlCompress(x, d) = FipsCompress(x, d)
ASSUME \A d \in KemDs : \A y \in 0 .. 2 ^ d - 1 : OcamlDecompress(y, d) = FipsDecompress(y, d)
\* the remainder is in [0, 2q), so two conditional increments suffice
ASSUME \A d \in KemDs : \A x \in 0 .. KQ - 1 :
         LET dividend == x * 2 ^ d
             quotient == ((dividend \div 2 ^ 12) * 5039 + ((dividend % 2 ^ 12) * 5039) \div 2 ^ 12) \div 2 ^ 12
         IN dividend - quotient * KQ \in 0 .. 2 * KQ - 1

(***************************************************************************)
(* ML-KEM encode_12 / decode_12 (lines 230-253), n = 256, symbolic codes:  *)
(*   x = a lor (b lsl 12); out[3i] = x, out[3i+1] = x lsr 8,               *)
(*   out[3i+2] = x lsr 16 (set_u8 masks with 0xff);                        *)
(*   decode: x = s[p] lor (s[p+1] lsl 8) lor (s[p+2] lsl 16);              *)
(*   a = x land 0xfff; b = x lsr 12.                                       *)
(***************************************************************************)
E12Code(i) == [p \in 0 .. 63 |-> IF p < 12 THEN {<<"c", i, p>>} ELSE {}]
E12X(i) == Or(E12Code(2 * i), Shl(E12Code(2 * i + 1), 12, 63), 63)
E12Byte(i, k) == LowBits(Shr(E12X(i), 8 * k, 63), 8)
E12Cfg == [kind |-> "kem", bits |-> 12, count |-> 256]
ASSUME \A i \in 0 .. 127 : \A k \in 0 .. 2 : \A t \in 0 .. 7 :
         E12Byte(i, k)[t] = FipsPackBit(E12Cfg, 3 * i + k, t)
D12X(i) == Or(Or(Widen(ByteAtoms(3 * i), 63), Shl(Widen(ByteAtoms(3 * i + 1), 63), 8, 63), 63),
              Shl(Widen(ByteAtoms(3 * i + 2), 63), 16, 63), 63)
ASSUME \A i \in 0 .. 127 : \A j \in 0 .. 11 :
         /\ LowBits(D12X(i), 12)[j] = FipsUnpackBit(E12Cfg, 2 * i, j)
         /\ Shr(D12X(i), 12, 63)[j] = FipsUnpackBit(E12Cfg, 2 * i + 1, j)
ASSUME \A i \in 0 .. 127 : \A p \in 24 .. 62 : D12X(i)[p] = {}
\* decode_12's validity test (a < q) is FIPS 203's modulus check:
\* ByteEncode_12(ByteDecode_12(v)) = v (ByteDecode_12 reduces mod q)
ASSUME \A v \in 0 .. 2 ^ 12 - 1 : (v % KQ = v) = (v < KQ)

(***************************************************************************)
(* Parameter sets                                                          *)
(***************************************************************************)
RealConfigs ==
  { [kind |-> "dsa", bits |-> b, count |-> 256] : b \in {3, 4, 6, 10, 13, 18, 20} }
  \cup { [kind |-> "kem", bits |-> b, count |-> 256] : b \in {1, 4, 5, 10, 11} }
SweepConfigs ==
  { [kind |-> "dsa", bits |-> b, count |-> n] : b \in 1 .. 20, n \in 1 .. 9 }
  \cup { [kind |-> "kem", bits |-> b, count |-> n] : b \in 1 .. 12, n \in 1 .. 9 }
AllConfigs == RealConfigs \cup SweepConfigs
=============================================================================
