import Mathlib

/-!
# Model of `lib/keccak.ml`

A literal Lean transcription of the OCaml Keccak-f[1600] permutation and
sponge in `lib/keccak.ml`.

Representation choices:

* `Int64.t` is `BitVec 64`. `Int64.logxor`/`logand`/`lognot`/`logor` are
  `^^^`/`&&&`/`~~~`/`|||`; `Int64.shift_left x n` and
  `Int64.shift_right_logical x n` are `x <<< n` and `x >>> n`. OCaml leaves
  those shifts unspecified outside `0 ≤ n < 64`; every call site is shown to
  stay in that range (`KeccakSafety`).
* An OCaml `int` used as a loop counter or array index is a `ℕ` (the loops
  only ever produce non-negative values); `KeccakSafety` bounds them.
* An OCaml `'a array` is a Lean `Array`; `a.(i)` is `a[i]!` and
  `a.(i) <- v` is `a.set! i v`. `KeccakSafety` shows every index is in
  bounds, so the OCaml bounds checks never fire and `[i]!` never falls back to
  its default.
* An OCaml `string`/`bytes` is a `List UInt8`. `Bytes.create n` returns
  unspecified contents; the model takes those contents as a parameter
  (`junk`), and the theorems hold for every choice.
* The OCaml array `c` is called `cc` in the model (Mathlib reserves
  `c[…]` for cycle notation).
* A `for i = 0 to n - 1 do … done` loop is a left fold over `List.range n`
  (`List.range' lo n` when it starts at `lo`);
  a `while` loop is a recursion with an explicit fuel bound that is shown to
  be sufficient.
-/

namespace OcamlPq.Hash.Keccak

/-- `round_constants`, `lib/keccak.ml` lines 1–15. -/
def roundConstants : Array (BitVec 64) := #[
  0x0000000000000001#64, 0x0000000000008082#64,
  0x800000000000808a#64, 0x8000000080008000#64,
  0x000000000000808b#64, 0x0000000080000001#64,
  0x8000000080008081#64, 0x8000000000008009#64,
  0x000000000000008a#64, 0x0000000000000088#64,
  0x0000000080008009#64, 0x000000008000000a#64,
  0x000000008000808b#64, 0x800000000000008b#64,
  0x8000000000008089#64, 0x8000000000008003#64,
  0x8000000000008002#64, 0x8000000000000080#64,
  0x000000000000800a#64, 0x800000008000000a#64,
  0x8000000080008081#64, 0x8000000000008080#64,
  0x0000000080000001#64, 0x8000000080008008#64]

/-- `rotation`, `lib/keccak.ml` lines 17–24. -/
def rotation : Array ℕ := #[
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14]

/-- `rotl`, `lib/keccak.ml` lines 26–28:
`if n = 0 then x else logor (shift_left x n) (shift_right_logical x (64 - n))`. -/
def rotl (x : BitVec 64) (n : ℕ) : BitVec 64 :=
  if n = 0 then x else (x <<< n) ||| (x >>> (64 - n))

/-- The three scratch arrays `c`, `d`, `b` of `permute` together with the
state `a`; `lib/keccak.ml` lines 31–33 allocate them once, outside the round
loop, so their contents carry over from one round to the next. -/
structure PermState where
  a : Array (BitVec 64)
  c : Array (BitVec 64)
  d : Array (BitVec 64)
  b : Array (BitVec 64)

/-- `lib/keccak.ml` lines 35–41: `c.(x) <- a.(x) ⊕ a.(x+5) ⊕ … ⊕ a.(x+20)`. -/
def thetaCLoop (a cc : Array (BitVec 64)) : Array (BitVec 64) :=
  (List.range 5).foldl (fun cc x =>
    cc.set! x (a[x]! ^^^ (a[x + 5]! ^^^ (a[x + 10]! ^^^ (a[x + 15]! ^^^ a[x + 20]!))))) cc

/-- `lib/keccak.ml` lines 42–44:
`d.(x) <- c.((x + 4) mod 5) ⊕ rotl c.((x + 1) mod 5) 1`. -/
def thetaDLoop (cc d : Array (BitVec 64)) : Array (BitVec 64) :=
  (List.range 5).foldl (fun d x => d.set! x (cc[(x + 4) % 5]! ^^^ rotl (cc[(x + 1) % 5]!) 1)) d

/-- `lib/keccak.ml` lines 45–49: `a.(x + 5y) <- a.(x + 5y) ⊕ d.(x)`. -/
def thetaALoop (a d : Array (BitVec 64)) : Array (BitVec 64) :=
  (List.range 5).foldl (fun a y => (List.range 5).foldl (fun a x =>
    a.set! (x + 5 * y) (a[x + 5 * y]! ^^^ d[x]!)) a) a

/-- `lib/keccak.ml` lines 50–56:
`b.(new_x + 5 new_y) <- rotl a.(x + 5y) rotation.(x + 5y)` with
`new_x = y`, `new_y = (2x + 3y) mod 5`. -/
def rhoPiLoop (a b : Array (BitVec 64)) : Array (BitVec 64) :=
  (List.range 5).foldl (fun b y => (List.range 5).foldl (fun b x =>
    let newX := y
    let newY := (2 * x + 3 * y) % 5
    b.set! (newX + 5 * newY) (rotl (a[x + 5 * y]!) (rotation[x + 5 * y]!))) b) b

/-- `lib/keccak.ml` lines 57–64:
`a.(x + 5y) <- b.(x + 5y) ⊕ (¬b.((x+1) mod 5 + 5y) ∧ b.((x+2) mod 5 + 5y))`. -/
def chiLoop (a b : Array (BitVec 64)) : Array (BitVec 64) :=
  (List.range 5).foldl (fun a y => (List.range 5).foldl (fun a x =>
    a.set! (x + 5 * y)
      (b[x + 5 * y]! ^^^ ((~~~(b[(x + 1) % 5 + 5 * y]!)) &&& b[(x + 2) % 5 + 5 * y]!))) a) a

/-- One iteration of the `for round = 0 to 23` loop, `lib/keccak.ml`
lines 35–65. -/
def permRound (s : PermState) (round : ℕ) : PermState :=
  let cc := thetaCLoop s.a s.c
  let d := thetaDLoop cc s.d
  let a := thetaALoop s.a d
  let b := rhoPiLoop a s.b
  let a := chiLoop a b
  let a := a.set! 0 (a[0]! ^^^ roundConstants[round]!)
  { a := a, c := cc, d := d, b := b }

/-- `permute`, `lib/keccak.ml` lines 30–66. The OCaml function mutates its
argument; the model returns the final contents of `a`. -/
def permute (a : Array (BitVec 64)) : Array (BitVec 64) :=
  let s : PermState :=
    { a := a, c := Array.replicate 5 0, d := Array.replicate 5 0, b := Array.replicate 25 0 }
  ((List.range 24).foldl permRound s).a

/-- `Int64.of_int (Char.code ch)`: a byte zero-extended to 64 bits. -/
def int64OfByte (ch : UInt8) : BitVec 64 := BitVec.ofNat 64 ch.toNat

/-- `Char.unsafe_chr (Int64.to_int v)` for `0 ≤ v < 256`: the low byte. -/
def byteOfInt64 (v : BitVec 64) : UInt8 := UInt8.ofNat v.toNat

/-- `load64_le`, `lib/keccak.ml` lines 68–74. -/
def load64Le (s : List UInt8) (off : ℕ) : BitVec 64 :=
  (List.range 8).foldl (fun r i => r ||| (int64OfByte (s[off + i]!) <<< (8 * i))) 0

/-- `store64_le`, `lib/keccak.ml` lines 76–80. -/
def store64Le (b : List UInt8) (off : ℕ) (x : BitVec 64) : List UInt8 :=
  (List.range 8).foldl (fun b i => b.set (off + i) (byteOfInt64 ((x >>> (8 * i)) &&& 0xff#64))) b

/-- `xor_block`, `lib/keccak.ml` lines 82–85. -/
def xorBlock (state : Array (BitVec 64)) (block : List UInt8) : Array (BitVec 64) :=
  (List.range (block.length / 8)).foldl (fun st i =>
    st.set! i (st[i]! ^^^ load64Le block (8 * i))) state

/-- `String.sub s pos len` (in bounds). -/
def stringSub (s : List UInt8) (pos len : ℕ) : List UInt8 := (s.drop pos).take len

/-- `Bytes.blit_string src srcoff dst dstoff len` (in bounds): the bytes
`dst[dstoff + i] := src[srcoff + i]` for `i < len`. -/
def blitString (src : List UInt8) (srcoff : ℕ) (dst : List UInt8) (dstoff len : ℕ) :
    List UInt8 :=
  (List.range len).foldl (fun d i => d.set (dstoff + i) (src[srcoff + i]!)) dst

/-- The squeeze `while` loop, `lib/keccak.ml` lines 103–113. Arguments:
the state, the output buffer, `!produced`, and the contents that each fresh
`Bytes.create rate` block holds before it is filled (`blockJunk p` in the
iteration that starts with `!produced = p`, so it may differ between
iterations). Returns
the final state, output buffer and `!produced`. `fuel` bounds the number of
iterations; `squeeze_fuel_enough` shows the bound used by `sponge` is never
reached. -/
def squeezeLoop (rate outputLength : ℕ) (blockJunk : ℕ → List UInt8) :
    ℕ → Array (BitVec 64) → List UInt8 → ℕ → Array (BitVec 64) × List UInt8 × ℕ
  | 0, state, out, produced => (state, out, produced)
  | fuel + 1, state, out, produced =>
    if produced < outputLength then
      let take := min rate (outputLength - produced)
      let block := (List.range (rate / 8)).foldl (fun blk i => store64Le blk (8 * i) (state[i]!))
        (blockJunk produced)
      let out := blitString block 0 out produced take
      let produced := produced + take
      let state := if produced < outputLength then permute state else state
      squeezeLoop rate outputLength blockJunk fuel state out produced
    else (state, out, produced)

/-- The absorbing phase of `sponge`, `lib/keccak.ml` lines 88–101: the state
after the final (padded) block has been absorbed and permuted. -/
def absorb (rate suffix : ℕ) (input : List UInt8) : Array (BitVec 64) :=
  let state : Array (BitVec 64) := Array.replicate 25 0
  let fullBlocks := input.length / rate
  let state := (List.range fullBlocks).foldl (fun st block =>
    permute (xorBlock st (stringSub input (block * rate) rate))) state
  let rem := input.length % rate
  let tail := List.replicate rate (0 : UInt8)
  let tail := blitString input (fullBlocks * rate) tail 0 rem
  let tail := tail.set rem (UInt8.ofNat suffix)
  let tail := tail.set (rate - 1) (UInt8.ofNat (tail[rate - 1]!.toNat ||| 0x80))
  permute (xorBlock state tail)

/-- `sponge`, `lib/keccak.ml` lines 87–115, with the unspecified contents of
`Bytes.create output_length` (`outJunk`) and of each `Bytes.create rate`
(`blockJunk`) as parameters. The final `Bytes.fill tail 0 rate '\000'`
(line 114) only scrubs a buffer that is no longer read and is omitted. -/
def spongeWith (rate suffix outputLength : ℕ) (outJunk : List UInt8)
    (blockJunk : ℕ → List UInt8) (input : List UInt8) : List UInt8 :=
  let state := absorb rate suffix input
  (squeezeLoop rate outputLength blockJunk (outputLength + 1) state outJunk 0).2.1

/-- `sponge` with zero-filled `Bytes.create` buffers (the theorems show the
result does not depend on this choice). -/
def sponge (rate suffix outputLength : ℕ) (input : List UInt8) : List UInt8 :=
  spongeWith rate suffix outputLength (List.replicate outputLength 0) (fun _ => List.replicate rate 0)
    input

/-- `sha3_256`, `lib/keccak.ml` line 117. -/
def sha3_256 (input : List UInt8) : List UInt8 := sponge 136 0x06 32 input
/-- `sha3_512`, `lib/keccak.ml` line 118. -/
def sha3_512 (input : List UInt8) : List UInt8 := sponge 72 0x06 64 input
/-- `shake128`, `lib/keccak.ml` line 119. -/
def shake128 (outputLength : ℕ) (input : List UInt8) : List UInt8 :=
  sponge 168 0x1f outputLength input
/-- `shake256`, `lib/keccak.ml` line 120. -/
def shake256 (outputLength : ℕ) (input : List UInt8) : List UInt8 :=
  sponge 136 0x1f outputLength input

end OcamlPq.Hash.Keccak
