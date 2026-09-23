import OcamlPq.Hash.KeccakModel

/-!
# Model of `slhdsa/slhdsa_hash.ml` lines 120–340 (SHA-256, SHA-512, HMAC, MGF1)

Conventions as in `KeccakModel`: `Int32.t`/`Int64.t` are `BitVec 32`/`BitVec 64`
(`Int32.add` is `+`, wrapping), strings and bytes are `List UInt8`, arrays are
`Array`, `for` loops are folds over `List.range`/`List.range'`, and the
unspecified contents of `Bytes.create n` are a parameter. OCaml `int`s that
are lengths, offsets and counters are `ℕ` (they are never negative on the
paths modelled; `mgf1`'s `output_length` is discussed in `HmacMgf1`).
-/

namespace OcamlPq.Hash.Sha2

open Keccak (blitString int64OfByte byteOfInt64)

/-- `Int32.of_int (Char.code ch)`. -/
def int32OfByte (ch : UInt8) : BitVec 32 := BitVec.ofNat 32 ch.toNat

/-- `Char.unsafe_chr (Int32.to_int v)` for `0 ≤ v < 256`. -/
def byteOfInt32 (v : BitVec 32) : UInt8 := UInt8.ofNat v.toNat

/-- `get_u32_be`, lines 120–124. -/
def getU32Be (s : List UInt8) (off : ℕ) : BitVec 32 :=
  let byte := fun i => int32OfByte (s[off + i]!)
  (byte 0 <<< 24) ||| ((byte 1 <<< 16) ||| ((byte 2 <<< 8) ||| byte 3))

/-- `set_u32_be`, lines 126–137. -/
def setU32Be (b : List UInt8) (off : ℕ) (x : BitVec 32) : List UInt8 :=
  let b := b.set off (byteOfInt32 ((x >>> 24) &&& 0xff#32))
  let b := b.set (off + 1) (byteOfInt32 ((x >>> 16) &&& 0xff#32))
  let b := b.set (off + 2) (byteOfInt32 ((x >>> 8) &&& 0xff#32))
  b.set (off + 3) (byteOfInt32 (x &&& 0xff#32))

/-- `rotr32`, lines 139–140. -/
def rotr32 (x : BitVec 32) (n : ℕ) : BitVec 32 := (x >>> n) ||| (x <<< (32 - n))

/-- `sha256_constants`, lines 142–160. -/
def sha256Constants : Array (BitVec 32) := #[
  0x428a2f98#32, 0x71374491#32, 0xb5c0fbcf#32, 0xe9b5dba5#32,
  0x3956c25b#32, 0x59f111f1#32, 0x923f82a4#32, 0xab1c5ed5#32,
  0xd807aa98#32, 0x12835b01#32, 0x243185be#32, 0x550c7dc3#32,
  0x72be5d74#32, 0x80deb1fe#32, 0x9bdc06a7#32, 0xc19bf174#32,
  0xe49b69c1#32, 0xefbe4786#32, 0x0fc19dc6#32, 0x240ca1cc#32,
  0x2de92c6f#32, 0x4a7484aa#32, 0x5cb0a9dc#32, 0x76f988da#32,
  0x983e5152#32, 0xa831c66d#32, 0xb00327c8#32, 0xbf597fc7#32,
  0xc6e00bf3#32, 0xd5a79147#32, 0x06ca6351#32, 0x14292967#32,
  0x27b70a85#32, 0x2e1b2138#32, 0x4d2c6dfc#32, 0x53380d13#32,
  0x650a7354#32, 0x766a0abb#32, 0x81c2c92e#32, 0x92722c85#32,
  0xa2bfe8a1#32, 0xa81a664b#32, 0xc24b8b70#32, 0xc76c51a3#32,
  0xd192e819#32, 0xd6990624#32, 0xf40e3585#32, 0x106aa070#32,
  0x19a4c116#32, 0x1e376c08#32, 0x2748774c#32, 0x34b0bcb5#32,
  0x391c0cb3#32, 0x4ed8aa4a#32, 0x5b9cca4f#32, 0x682e6ff3#32,
  0x748f82ee#32, 0x78a5636f#32, 0x84c87814#32, 0x8cc70208#32,
  0x90befffa#32, 0xa4506ceb#32, 0xbef9a3f7#32, 0xc67178f2#32]

/-- The initial `h` array of `sha256`, lines 175–180. -/
def sha256H0 : Array (BitVec 32) := #[
  0x6a09e667#32, 0xbb67ae85#32, 0x3c6ef372#32, 0xa54ff53a#32,
  0x510e527f#32, 0x9b05688c#32, 0x1f83d9ab#32, 0x5be0cd19#32]

/-- The eight `ref`s `a b c d e f g hh` of the compression loops. -/
structure Vars (w : ℕ) where
  a : BitVec w
  b : BitVec w
  c : BitVec w
  d : BitVec w
  e : BitVec w
  f : BitVec w
  g : BitVec w
  hh : BitVec w

/-- Padding, lines 163–174: `padded_length = ((len + 9 + 63) / 64) · 64`,
`padded` zero-filled, input copied, `0x80` at `len`, and the eight bytes of
`bit_length = Int64.mul (Int64.of_int len) 8L` stored big-endian at the end. -/
def sha256Pad (input : List UInt8) : List UInt8 :=
  let inputLength := input.length
  let paddedLength := ((inputLength + 9 + 63) / 64) * 64
  let padded := List.replicate paddedLength (0 : UInt8)
  let padded := blitString input 0 padded 0 inputLength
  let padded := padded.set inputLength 0x80
  let bitLength : BitVec 64 := BitVec.ofNat 64 inputLength * 8#64
  (List.range 8).foldl (fun p i =>
    p.set (paddedLength - 1 - i) (byteOfInt64 ((bitLength >>> (8 * i)) &&& 0xff#64))) padded

/-- The message schedule, lines 184–197. -/
def sha256Schedule (padded : List UInt8) (base : ℕ) (w : Array (BitVec 32)) : Array (BitVec 32) :=
  let w := (List.range 16).foldl (fun w i => w.set! i (getU32Be padded (base + 4 * i))) w
  (List.range' 16 48).foldl (fun w i =>
    let x := w[i - 15]!
    let y := w[i - 2]!
    let s0 := rotr32 x 7 ^^^ (rotr32 x 18 ^^^ (x >>> 3))
    let s1 := rotr32 y 17 ^^^ (rotr32 y 19 ^^^ (y >>> 10))
    w.set! i ((w[i - 16]! + s0) + (w[i - 7]! + s1))) w

/-- One iteration of `for i = 0 to 63`, lines 200–215. -/
def sha256Round (w : Array (BitVec 32)) (v : Vars 32) (i : ℕ) : Vars 32 :=
  let s1 := rotr32 v.e 6 ^^^ (rotr32 v.e 11 ^^^ rotr32 v.e 25)
  let ch := (v.e &&& v.f) ^^^ ((~~~v.e) &&& v.g)
  let t1 := v.hh + (s1 + (ch + (sha256Constants[i]! + w[i]!)))
  let s0 := rotr32 v.a 2 ^^^ (rotr32 v.a 13 ^^^ rotr32 v.a 22)
  let maj := (v.a &&& v.b) ^^^ ((v.a &&& v.c) ^^^ (v.b &&& v.c))
  let t2 := s0 + maj
  { hh := v.g, g := v.f, f := v.e, e := v.d + t1, d := v.c, c := v.b, b := v.a, a := t1 + t2 }

/-- The final additions `h.(j) <- Int32.add h.(j) !x`, lines 216–219 (and 308–311). -/
def addVars {w : ℕ} (h : Array (BitVec w)) (v : Vars w) : Array (BitVec w) :=
  let h := h.set! 0 (h[0]! + v.a)
  let h := h.set! 1 (h[1]! + v.b)
  let h := h.set! 2 (h[2]! + v.c)
  let h := h.set! 3 (h[3]! + v.d)
  let h := h.set! 4 (h[4]! + v.e)
  let h := h.set! 5 (h[5]! + v.f)
  let h := h.set! 6 (h[6]! + v.g)
  h.set! 7 (h[7]! + v.hh)

/-- The `let a = ref h.(0) and …` initialisation. -/
def varsOf {w : ℕ} (h : Array (BitVec w)) : Vars w :=
  ⟨h[0]!, h[1]!, h[2]!, h[3]!, h[4]!, h[5]!, h[6]!, h[7]!⟩

/-- One iteration of `for block = 0 to padded_length / 64 - 1`, lines 182–220;
`w` is shared between blocks. -/
def sha256Block (padded : List UInt8) (hw : Array (BitVec 32) × Array (BitVec 32)) (block : ℕ) :
    Array (BitVec 32) × Array (BitVec 32) :=
  let (h, w) := hw
  let base := block * 64
  let w := sha256Schedule padded base w
  let v := (List.range 64).foldl (sha256Round w) (varsOf h)
  (addVars h v, w)

/-- `sha256`, lines 162–223, with the contents of `Bytes.create 32` as `junk`. -/
def sha256With (junk : List UInt8) (input : List UInt8) : List UInt8 :=
  let padded := sha256Pad input
  let paddedLength := padded.length
  let hw := (List.range (paddedLength / 64)).foldl (sha256Block padded)
    (sha256H0, Array.replicate 64 0)
  let h := hw.1
  -- `Array.iteri (fun i x -> set_u32_be result (4 * i) x) h`
  (List.range 8).foldl (fun r i => setU32Be r (4 * i) h[i]!) junk

def sha256 (input : List UInt8) : List UInt8 := sha256With (List.replicate 32 0) input

/-- `get_u64_be`, lines 225–232. -/
def getU64Be (s : List UInt8) (off : ℕ) : BitVec 64 :=
  (List.range 8).foldl (fun r i => (r <<< 8) ||| int64OfByte (s[off + i]!)) 0

/-- `set_u64_be`, lines 234–240. -/
def setU64Be (b : List UInt8) (off : ℕ) (x : BitVec 64) : List UInt8 :=
  (List.range 8).foldl (fun b i =>
    b.set (off + i) (byteOfInt64 ((x >>> (8 * (7 - i))) &&& 0xff#64))) b

/-- `rotr64`, lines 242–243. -/
def rotr64 (x : BitVec 64) (n : ℕ) : BitVec 64 := (x >>> n) ||| (x <<< (64 - n))

/-- `sha512_constants`, lines 245–267. -/
def sha512Constants : Array (BitVec 64) := #[
  0x428a2f98d728ae22#64, 0x7137449123ef65cd#64, 0xb5c0fbcfec4d3b2f#64, 0xe9b5dba58189dbbc#64,
  0x3956c25bf348b538#64, 0x59f111f1b605d019#64, 0x923f82a4af194f9b#64, 0xab1c5ed5da6d8118#64,
  0xd807aa98a3030242#64, 0x12835b0145706fbe#64, 0x243185be4ee4b28c#64, 0x550c7dc3d5ffb4e2#64,
  0x72be5d74f27b896f#64, 0x80deb1fe3b1696b1#64, 0x9bdc06a725c71235#64, 0xc19bf174cf692694#64,
  0xe49b69c19ef14ad2#64, 0xefbe4786384f25e3#64, 0x0fc19dc68b8cd5b5#64, 0x240ca1cc77ac9c65#64,
  0x2de92c6f592b0275#64, 0x4a7484aa6ea6e483#64, 0x5cb0a9dcbd41fbd4#64, 0x76f988da831153b5#64,
  0x983e5152ee66dfab#64, 0xa831c66d2db43210#64, 0xb00327c898fb213f#64, 0xbf597fc7beef0ee4#64,
  0xc6e00bf33da88fc2#64, 0xd5a79147930aa725#64, 0x06ca6351e003826f#64, 0x142929670a0e6e70#64,
  0x27b70a8546d22ffc#64, 0x2e1b21385c26c926#64, 0x4d2c6dfc5ac42aed#64, 0x53380d139d95b3df#64,
  0x650a73548baf63de#64, 0x766a0abb3c77b2a8#64, 0x81c2c92e47edaee6#64, 0x92722c851482353b#64,
  0xa2bfe8a14cf10364#64, 0xa81a664bbc423001#64, 0xc24b8b70d0f89791#64, 0xc76c51a30654be30#64,
  0xd192e819d6ef5218#64, 0xd69906245565a910#64, 0xf40e35855771202a#64, 0x106aa07032bbd1b8#64,
  0x19a4c116b8d2d0c8#64, 0x1e376c085141ab53#64, 0x2748774cdf8eeb99#64, 0x34b0bcb5e19b48a8#64,
  0x391c0cb3c5c95a63#64, 0x4ed8aa4ae3418acb#64, 0x5b9cca4f7763e373#64, 0x682e6ff3d6b2b8a3#64,
  0x748f82ee5defb2fc#64, 0x78a5636f43172f60#64, 0x84c87814a1f0ab72#64, 0x8cc702081a6439ec#64,
  0x90befffa23631e28#64, 0xa4506cebde82bde9#64, 0xbef9a3f7b2c67915#64, 0xc67178f2e372532b#64,
  0xca273eceea26619c#64, 0xd186b8c721c0c207#64, 0xeada7dd6cde0eb1e#64, 0xf57d4f7fee6ed178#64,
  0x06f067aa72176fba#64, 0x0a637dc5a2c898a6#64, 0x113f9804bef90dae#64, 0x1b710b35131c471b#64,
  0x28db77f523047d84#64, 0x32caab7b40c72493#64, 0x3c9ebe0a15c9bebc#64, 0x431d67c49c100d4c#64,
  0x4cc5d4becb3e42b6#64, 0x597f299cfc657e2a#64, 0x5fcb6fab3ad6faec#64, 0x6c44198c4a475817#64]

/-- The initial `h` array of `sha512`, lines 277–282. -/
def sha512H0 : Array (BitVec 64) := #[
  0x6a09e667f3bcc908#64, 0xbb67ae8584caa73b#64, 0x3c6ef372fe94f82b#64, 0xa54ff53a5f1d36f1#64,
  0x510e527fade682d1#64, 0x9b05688c2b3e6c1f#64, 0x1f83d9abfb41bd6b#64, 0x5be0cd19137e2179#64]

/-- Padding, lines 270–276: `padded_length = ((len + 17 + 127) / 128) · 128`;
only the low 64 bits of the 128-bit length field are written. -/
def sha512Pad (input : List UInt8) : List UInt8 :=
  let inputLength := input.length
  let paddedLength := ((inputLength + 17 + 127) / 128) * 128
  let padded := List.replicate paddedLength (0 : UInt8)
  let padded := blitString input 0 padded 0 inputLength
  let padded := padded.set inputLength 0x80
  let bitLength : BitVec 64 := BitVec.ofNat 64 inputLength * 8#64
  setU64Be padded (paddedLength - 8) bitLength

/-- The message schedule, lines 286–294. -/
def sha512Schedule (padded : List UInt8) (base : ℕ) (w : Array (BitVec 64)) : Array (BitVec 64) :=
  let w := (List.range 16).foldl (fun w i => w.set! i (getU64Be padded (base + 8 * i))) w
  (List.range' 16 64).foldl (fun w i =>
    let x := w[i - 15]!
    let y := w[i - 2]!
    let s0 := rotr64 x 1 ^^^ (rotr64 x 8 ^^^ (x >>> 7))
    let s1 := rotr64 y 19 ^^^ (rotr64 y 61 ^^^ (y >>> 6))
    w.set! i ((w[i - 16]! + s0) + (w[i - 7]! + s1))) w

/-- One iteration of `for i = 0 to 79`, lines 297–307. -/
def sha512Round (w : Array (BitVec 64)) (v : Vars 64) (i : ℕ) : Vars 64 :=
  let s1 := rotr64 v.e 14 ^^^ (rotr64 v.e 18 ^^^ rotr64 v.e 41)
  let ch := (v.e &&& v.f) ^^^ ((~~~v.e) &&& v.g)
  let t1 := v.hh + (s1 + (ch + (sha512Constants[i]! + w[i]!)))
  let s0 := rotr64 v.a 28 ^^^ (rotr64 v.a 34 ^^^ rotr64 v.a 39)
  let maj := (v.a &&& v.b) ^^^ ((v.a &&& v.c) ^^^ (v.b &&& v.c))
  let t2 := s0 + maj
  { hh := v.g, g := v.f, f := v.e, e := v.d + t1, d := v.c, c := v.b, b := v.a, a := t1 + t2 }

/-- One iteration of `for block = 0 to padded_length / 128 - 1`, lines 284–312. -/
def sha512Block (padded : List UInt8) (hw : Array (BitVec 64) × Array (BitVec 64)) (block : ℕ) :
    Array (BitVec 64) × Array (BitVec 64) :=
  let (h, w) := hw
  let base := block * 128
  let w := sha512Schedule padded base w
  let v := (List.range 80).foldl (sha512Round w) (varsOf h)
  (addVars h v, w)

/-- `sha512`, lines 269–315, with the contents of `Bytes.create 64` as `junk`. -/
def sha512With (junk : List UInt8) (input : List UInt8) : List UInt8 :=
  let padded := sha512Pad input
  let paddedLength := padded.length
  let hw := (List.range (paddedLength / 128)).foldl (sha512Block padded)
    (sha512H0, Array.replicate 80 0)
  let h := hw.1
  (List.range 8).foldl (fun r i => setU64Be r (8 * i) h[i]!) junk

def sha512 (input : List UInt8) : List UInt8 := sha512With (List.replicate 64 0) input

/-- `xor_with`, lines 317–319. -/
def xorWith (byte : UInt8) (s : List UInt8) : List UInt8 := s.map fun c => c ^^^ byte

/-- `hmac`, lines 321–324. -/
def hmac (blockSize : ℕ) (hash : List UInt8 → List UInt8) (key message : List UInt8) : List UInt8 :=
  let key := if key.length > blockSize then hash key else key
  let key := key ++ List.replicate (blockSize - key.length) 0
  hash (xorWith 0x5c key ++ hash (xorWith 0x36 key ++ message))

/-- `hmac_sha256`, line 326. -/
def hmacSha256 (key message : List UInt8) : List UInt8 := hmac 64 sha256 key message
/-- `hmac_sha512`, line 327. -/
def hmacSha512 (key message : List UInt8) : List UInt8 := hmac 128 sha512 key message

/-- `Int32.of_int counter` for a non-negative `int`: the low 32 bits. -/
def int32OfInt (n : ℕ) : BitVec 32 := BitVec.ofNat 32 n

/-- `mgf1`, lines 329–337 (`output_length ≥ 0`; `Buffer` is a growing byte list,
`Bytes.create 4` is fully overwritten by `set_u32_be`). -/
def mgf1 (hash : List UInt8 → List UInt8) (digestSize outputLength : ℕ) (seed : List UInt8) :
    List UInt8 :=
  let blocks := (outputLength + digestSize - 1) / digestSize
  let result := (List.range blocks).foldl (fun result counter =>
    let encoded := setU32Be (List.replicate 4 0) 0 (int32OfInt counter)
    result ++ hash (seed ++ encoded)) []
  (result.drop 0).take outputLength

/-- `mgf1_sha256`, line 339. -/
def mgf1Sha256 (outputLength : ℕ) (seed : List UInt8) : List UInt8 := mgf1 sha256 32 outputLength seed
/-- `mgf1_sha512`, line 340. -/
def mgf1Sha512 (outputLength : ℕ) (seed : List UInt8) : List UInt8 := mgf1 sha512 64 outputLength seed

end OcamlPq.Hash.Sha2
