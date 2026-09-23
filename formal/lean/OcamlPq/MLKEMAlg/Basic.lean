import Mathlib
import OcamlPq.Common.Int

/-!
# ML-KEM sampling and composition: shared vocabulary

Types and helpers shared by the models of `lib/mlkem_engine.ml` (sampling,
K-PKE and the KEM composition) and by the FIPS 203 specifications.

* OCaml `string` values holding bytes are `Bytes := List Byte`, `Byte := Fin 256`.
* A mutable OCaml `bytes` buffer is a function `ℕ → Byte`. `Bytes.create`
  returns uninitialised memory, so every model takes the initial contents as
  an arbitrary argument and the theorems hold for all of them: this proves that
  no uninitialised byte reaches an output.
* An OCaml `poly = int array` of length 256 is `IPoly := Fin 256 → ℤ`; a spec
  polynomial (or NTT representation) is `Poly := Fin 256 → ZMod q`.
* An OCaml array of length `k` is `Fin k → α`; a `for i = 0 to k - 1` loop is a
  left fold over `List.finRange k`.
-/

namespace OcamlPq.MLKEMAlg

/-- `n` (lib/mlkem_engine.ml:60). -/
abbrev n : ℕ := 256

/-- `q` (lib/mlkem_engine.ml:61). -/
abbrev q : ℕ := 3329

theorem n_eq : n = 256 := rfl
theorem q_eq : q = 3329 := rfl

abbrev Byte := Fin 256
abbrev Bytes := List Byte

/-- An implementation polynomial: OCaml `int array` of length 256. -/
abbrev IPoly := Fin 256 → ℤ

/-- A FIPS 203 polynomial in `R_q` or `T_q`, as its 256 coefficients. -/
abbrev Poly := Fin 256 → ZMod q

/-- The abstraction function from implementation to spec polynomials. -/
def toSpec (p : IPoly) : Poly := fun i => ((p i : ℤ) : ZMod q)

/-- The representation invariant stated in lib/mlkem_engine.ml:77: every
    coefficient is the canonical representative in `[0, q)`. -/
def Canonical (p : IPoly) : Prop := ∀ i, 0 ≤ p i ∧ p i < q

/-- `poly_zero ()` (lib/mlkem_engine.ml:138). -/
def polyZero : IPoly := fun _ => 0

theorem polyZero_canonical : Canonical polyZero := fun _ => by simp [polyZero]

@[simp] theorem toSpec_polyZero : toSpec polyZero = 0 := by
  funext i; simp [toSpec, polyZero]

/-! ## Strings -/

/-- `get_u8 s i = Char.code (String.unsafe_get s i)` (lib/mlkem_engine.ml:102).
    `unsafe_get` does no bounds check; the model returns 0 out of range, and
    each call site proves that its index is in range. -/
def getU8 (s : Bytes) (i : ℕ) : ℕ := (s.getD i 0).val

theorem getU8_lt (s : Bytes) (i : ℕ) : getU8 s i < 256 := (s.getD i 0).isLt

theorem getU8_of_lt {s : Bytes} {i : ℕ} (h : i < s.length) : getU8 s i = (s[i]'h).val := by
  simp [getU8, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- `Char.unsafe_chr x`. It is only meaningful for `0 ≤ x < 256`; every call
    site proves that range (see the portability theorems). -/
def unsafeChr (x : ℤ) : Byte := ⟨(x % 256).toNat, by omega⟩

theorem unsafeChr_val {x : ℤ} (h0 : 0 ≤ x) (h1 : x < 256) : ((unsafeChr x).val : ℤ) = x := by
  simp only [unsafeChr]
  rw [Int.emod_eq_of_lt h0 h1]; omega

theorem unsafeChr_val_nat {x : ℕ} (h : x < 256) : (unsafeChr x).val = x := by
  simp only [unsafeChr]; omega

/-- `String.sub s off len`, which raises `Invalid_argument` unless
    `off + len ≤ String.length s`; the call sites prove that bound. -/
def stringSub (s : Bytes) (off len : ℕ) : Bytes := (s.drop off).take len

theorem stringSub_length {s : Bytes} {off len : ℕ} (h : off + len ≤ s.length) :
    (stringSub s off len).length = len := by
  simp [stringSub]; omega

@[simp] theorem stringSub_zero_length (s : Bytes) : stringSub s 0 s.length = s := by
  simp [stringSub]

/-- `String.make 1 (Char.unsafe_chr x)`. -/
def byteString (x : ℤ) : Bytes := [unsafeChr x]

/-! ## Mutable byte buffers -/

/-- `Bytes.blit_string src srcOff dst dstOff len` on a buffer modelled as a
    function. It raises `Invalid_argument` unless `srcOff + len ≤ length src`
    and `dstOff + len ≤ length dst`; the call sites prove those bounds. -/
def blitString (src : Bytes) (srcOff : ℕ) (dst : ℕ → Byte) (dstOff len : ℕ) : ℕ → Byte :=
  fun p => if dstOff ≤ p ∧ p < dstOff + len then src.getD (srcOff + (p - dstOff)) 0 else dst p

/-- `Bytes.unsafe_set b i c`. -/
def bytesSet (dst : ℕ → Byte) (i : ℕ) (c : Byte) : ℕ → Byte := Function.update dst i c

/-- `set_u8 b i x = Bytes.unsafe_set b i (Char.unsafe_chr (x land 0xff))`
    (lib/mlkem_engine.ml:103). -/
def setU8 (dst : ℕ → Byte) (i : ℕ) (x : ℤ) : ℕ → Byte := bytesSet dst i (unsafeChr (Int.land x 0xff))

/-- The `len` bytes of a buffer starting at `lo`; `Bytes.unsafe_to_string b`
    for a buffer of length `len` is `bufToList b 0 len`. -/
def bufToList (buf : ℕ → Byte) (lo len : ℕ) : Bytes := List.ofFn (fun i : Fin len => buf (lo + i))

@[simp] theorem bufToList_length (buf : ℕ → Byte) (lo len : ℕ) : (bufToList buf lo len).length = len := by
  simp [bufToList]

theorem bufToList_add (buf : ℕ → Byte) (lo a b : ℕ) :
    bufToList buf lo (a + b) = bufToList buf lo a ++ bufToList buf (lo + a) b := by
  simp only [bufToList]
  rw [List.ofFn_add]
  congr 1
  apply congrArg List.ofFn; funext j; simp [Nat.add_assoc]

theorem bufToList_congr {buf buf' : ℕ → Byte} {lo len : ℕ}
    (h : ∀ p, lo ≤ p → p < lo + len → buf p = buf' p) : bufToList buf lo len = bufToList buf' lo len := by
  simp only [bufToList]
  apply congrArg List.ofFn; funext j; exact h _ (by omega) (by omega)

theorem blitString_outside {src : Bytes} {so : ℕ} {dst : ℕ → Byte} {off len p : ℕ}
    (h : p < off ∨ off + len ≤ p) : blitString src so dst off len p = dst p := by
  simp only [blitString]; split_ifs <;> first | rfl | omega

theorem bufToList_blitString {src : Bytes} {dst : ℕ → Byte} {off len : ℕ} (h : len ≤ src.length) :
    bufToList (blitString src 0 dst off len) off len = src.take len := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [bufToList, List.getElem_ofFn, blitString, List.getElem_take]
    simp at h1
    split_ifs with hc
    · simp only [List.getD_eq_getElem?_getD, zero_add, Nat.add_sub_cancel_left]
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    · omega

/-- A `for i = 0 to k - 1 do Bytes.blit_string (chunk i) 0 buf (off + i * c) c done` loop. -/
def blitChunks {k : ℕ} (c off : ℕ) (chunk : Fin k → Bytes) (buf : ℕ → Byte) : ℕ → Byte :=
  (List.finRange k).foldl (fun b i => blitString (chunk i) 0 b (off + i.val * c) c) buf

theorem blitChunks_outside {k : ℕ} (c off : ℕ) (chunk : Fin k → Bytes) (buf : ℕ → Byte) (p : ℕ)
    (hp : p < off ∨ off + k * c ≤ p) : blitChunks c off chunk buf p = buf p := by
  induction k generalizing buf with
  | zero => simp [blitChunks]
  | succ k ih =>
    simp only [blitChunks, List.finRange_succ_last, List.foldl_append, List.foldl_map,
      List.foldl_cons, List.foldl_nil]
    rw [blitString_outside (by simp [Fin.val_last]; rcases hp with hp | hp
                                <;> [left; right] <;> nlinarith)]
    exact ih (fun i => chunk i.castSucc) buf (by rcases hp with hp | hp <;> [left; right] <;> nlinarith)

theorem bufToList_blitChunks {k : ℕ} (c off : ℕ) (chunk : Fin k → Bytes) (buf : ℕ → Byte)
    (hc : ∀ i, (chunk i).length = c) :
    bufToList (blitChunks c off chunk buf) off (k * c) = (List.ofFn chunk).flatten := by
  induction k generalizing buf with
  | zero => simp [bufToList]
  | succ k ih =>
    rw [List.ofFn_succ_last, List.flatten_concat, Nat.succ_mul, bufToList_add]
    have hstep : blitChunks c off chunk buf =
        blitString (chunk (Fin.last k)) 0 (blitChunks c off (fun i => chunk i.castSucc) buf)
          (off + k * c) c := by
      simp only [blitChunks, List.finRange_succ_last, List.foldl_append, List.foldl_map,
        List.foldl_cons, List.foldl_nil, Fin.val_last, Fin.val_castSucc]
    rw [hstep, bufToList_blitString (by rw [hc]), List.take_of_length_le (by rw [hc]),
      ← ih (fun i => chunk i.castSucc) buf (fun i => hc _)]
    congr 1
    apply bufToList_congr
    intro p _ hp
    exact blitString_outside (Or.inl hp)

/-! ## Arrays -/

/-- `Array.init n f` where `f` reads and advances a mutable counter held in the
    state `σ`. OCaml's `Array.init` applies `f` to `0, …, n - 1` in order. -/
def arrayInitST {σ α : Type} : (n : ℕ) → (σ → α × σ) → σ → (Fin n → α) × σ
  | 0, _, s => (Fin.elim0, s)
  | n + 1, f, s =>
    let r := arrayInitST n f s
    let x := f r.2
    (Fin.snoc (α := fun _ => α) r.1 x.1, x.2)

theorem arrayInitST_counter {α : Type} (g : ℕ → α) (f : ℕ → α × ℕ) (hf : ∀ s, f s = (g s, s + 1))
    (m s : ℕ) : arrayInitST m f s = (fun i => g (s + i.val), s + m) := by
  induction m with
  | zero => simp [arrayInitST]; funext i; exact i.elim0
  | succ m ih =>
    simp only [arrayInitST, ih, hf, Prod.mk.injEq]
    refine ⟨?_, by omega⟩
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp

/-! ## Field arithmetic on the small values produced by sampling -/

/-- `field_reduce_once` (lib/mlkem_engine.ml:104-107). `Int32.of_int` is
    `BitVec.ofInt 32`, `Int32.shift_right` is the arithmetic shift and
    `Int32.to_int` is `BitVec.toInt`. -/
def fieldReduceOnce (a : ℤ) : ℤ :=
  let x := a - q
  let sign := (BitVec.sshiftRight (BitVec.ofInt 32 x) 31).toInt
  x + Int.land sign q

/-- `field_sub` (lib/mlkem_engine.ml:111). -/
def fieldSub (a b : ℤ) : ℤ := fieldReduceOnce (a - b + q)

theorem Int.land_neg_one_natCast (m : ℕ) : Int.land (-1) m = m := by
  show Int.land (Int.negSucc 0) (Int.ofNat m) = _
  simp only [Int.land, Nat.cast_inj]
  exact Nat.eq_of_testBit_eq fun i => by simp [Nat.testBit_ldiff]

theorem Int.land_zero_left (m : ℤ) : Int.land 0 m = 0 := by
  cases m with
  | ofNat m => simp [Int.land]
  | negSucc m =>
    simp only [Int.land, Nat.cast_eq_zero]
    exact Nat.eq_of_testBit_eq fun i => by simp [Nat.testBit_ldiff]

/-- On the values that `sample_cbd` passes it, `field_sub` returns the
    canonical representative of `a - b`. -/
theorem fieldSub_small (a b : ℕ) (ha : a ≤ 3) (hb : b ≤ 3) :
    fieldSub a b = ((a : ℤ) - b) % q ∧ 0 ≤ fieldSub a b ∧ fieldSub a b < q ∧
      Portable ((a : ℤ) - b + q) ∧ Portable ((a : ℤ) - b + q - q) := by
  have key : ∀ x : Fin 7, (BitVec.sshiftRight (BitVec.ofInt 32 ((x : ℤ) - 3)) 31).toInt =
      if (x : ℤ) - 3 < 0 then -1 else 0 := by decide
  have hx : ((a : ℤ) - b + q - q) = ((⟨a + 3 - b, by omega⟩ : Fin 7) : ℤ) - 3 := by
    simp; omega
  simp only [fieldSub, fieldReduceOnce]
  rw [hx, key]
  unfold Portable
  split_ifs with hneg
  · rw [Int.land_neg_one_natCast]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp at hneg ⊢ <;> omega
  · rw [Int.land_zero_left]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp at hneg ⊢ <;> omega

/-! ## Keccak

The hash functions are verified elsewhere; here they are abstract. An XOF is
an infinite byte stream per input, and `Keccak.shake128 ~output_length input`
returns its first `output_length` bytes. This builds in the prefix consistency
of SHAKE (a longer output extends a shorter one), which is what FIPS 203's
incremental `XOF.Squeeze` relies on. -/

/-- The Keccak functions of lib/keccak.ml:117-120, used as H, G, J, PRF and XOF
    (FIPS 203 §4.1). The only assumptions are the fixed output lengths of the
    SHA3 functions, which lib/keccak.ml:117-118 pass as `~output_length`. -/
structure Keccak where
  sha3_256 : Bytes → Bytes
  sha3_512 : Bytes → Bytes
  /-- The SHAKE128 output stream for an input. -/
  shake128 : Bytes → ℕ → Byte
  /-- The SHAKE256 output stream for an input. -/
  shake256 : Bytes → ℕ → Byte
  sha3_256_length : ∀ x, (sha3_256 x).length = 32
  sha3_512_length : ∀ x, (sha3_512 x).length = 64

/-- `Keccak.shake128 ~output_length input` (lib/keccak.ml:119). -/
def Keccak.shake128Out (K : Keccak) (outputLength : ℕ) (input : Bytes) : Bytes :=
  List.ofFn (fun i : Fin outputLength => K.shake128 input i)

/-- `Keccak.shake256 ~output_length input` (lib/keccak.ml:120). -/
def Keccak.shake256Out (K : Keccak) (outputLength : ℕ) (input : Bytes) : Bytes :=
  List.ofFn (fun i : Fin outputLength => K.shake256 input i)

@[simp] theorem Keccak.shake128Out_length (K : Keccak) (L : ℕ) (x : Bytes) :
    (K.shake128Out L x).length = L := by simp [Keccak.shake128Out]

@[simp] theorem Keccak.shake256Out_length (K : Keccak) (L : ℕ) (x : Bytes) :
    (K.shake256Out L x).length = L := by simp [Keccak.shake256Out]

/-! ## Folds -/

/-- A loop that writes `f i` to position `i` for each `i` of a list leaves
    position `i` equal to `f i` if `i` was visited and unchanged otherwise. -/
theorem foldl_update_eq {ι α : Type} [DecidableEq ι] (f : ι → α) (L : List ι) (init : ι → α) :
    L.foldl (fun out i => Function.update out i (f i)) init =
      fun i => if i ∈ L then f i else init i := by
  induction L generalizing init with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    funext i
    by_cases h1 : i ∈ L
    · simp [h1]
    · by_cases h2 : i = a
      · subst h2; simp
      · simp [h1, h2]

/-- `for i = 0 to 255 do out.(i) <- f i done` on a fresh array computes `f`. -/
theorem foldl_update_finRange {m : ℕ} {α : Type} (f : Fin m → α) (init : Fin m → α) :
    (List.finRange m).foldl (fun out i => Function.update out i (f i)) init = f := by
  rw [foldl_update_eq]; funext i; simp

end OcamlPq.MLKEMAlg
