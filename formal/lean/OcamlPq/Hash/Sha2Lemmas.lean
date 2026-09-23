import OcamlPq.Hash.Sha2Constants
import OcamlPq.Hash.SpongeLemmas

/-!
# Lemmas shared by the SHA-256 and SHA-512 proofs

* big-endian byte/bit conversion (`bytesToBitsBE_getElem`, `…_drop`, `…_take`);
* words read from bit strings (`getLsbD_wordOfBits`) and written as bit
  strings (`wordToBits_getElem`);
* the message-schedule loop (`sched_spec`) and the round loop (`rounds_spec`)
  of both OCaml functions, against FIPS 180-4 `schedule` and `step`;
* the final additions `h.(j) <- h.(j) + x` (`addVars_get`).
-/

namespace OcamlPq.Hash.Sha2

open FIPS180

/-! ## Big-endian bytes and bits -/

theorem bytesToBitsBE_cons (b : UInt8) (bs : List UInt8) :
    bytesToBitsBE (b :: bs) = ((List.range 8).map fun i => b.toNat.testBit (7 - i)) ++ bytesToBitsBE bs := by
  simp [bytesToBitsBE]

theorem bytesToBitsBE_append (bs cs : List UInt8) :
    bytesToBitsBE (bs ++ cs) = bytesToBitsBE bs ++ bytesToBitsBE cs := by
  simp [bytesToBitsBE]

@[simp] theorem bytesToBitsBE_length (bs : List UInt8) : (bytesToBitsBE bs).length = 8 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [bytesToBitsBE_cons]; simp [ih]; ring

theorem bytesToBitsBE_getElem (bs : List UInt8) (k : ℕ) (hk : k < (bytesToBitsBE bs).length) :
    (bytesToBitsBE bs)[k] =
      (bs[k / 8]'(by rw [bytesToBitsBE_length] at hk; omega)).toNat.testBit (7 - k % 8) := by
  induction bs generalizing k with
  | nil => simp at hk
  | cons b bs ih =>
    simp only [bytesToBitsBE_cons]
    by_cases h8 : k < 8
    · rw [List.getElem_append_left (by simpa using h8)]
      simp [Nat.div_eq_of_lt h8, Nat.mod_eq_of_lt h8]
    · rw [List.getElem_append_right (by simpa using h8)]
      simp only [List.length_map, List.length_range]
      rw [ih (k - 8) (by simp [bytesToBitsBE_length] at hk ⊢; omega)]
      have h1 : k / 8 = (k - 8) / 8 + 1 := by omega
      have h2 : (k - 8) % 8 = k % 8 := by omega
      simp only [h1, h2, List.getElem_cons_succ]

/-! ## Words -/

/-- Bit `j` (least significant first) of the word read from a `w`-bit string is
string position `w − 1 − j`. -/
theorem getLsbD_wordOfBits (w : ℕ) (L : Bits) (hL : L.length = w) (j : ℕ) (hj : j < w) :
    (wordOfBits w L).getLsbD j = L[w - 1 - j]'(by omega) := by
  subst hL
  simp [wordOfBits, hj]

@[simp] theorem wordToBits_length {w : ℕ} (x : BitVec w) : (wordToBits x).length = w := by
  simp [wordToBits]

theorem wordToBits_getElem {w : ℕ} (x : BitVec w) (i : ℕ) (hi : i < (wordToBits x).length) :
    (wordToBits x)[i] = x.getLsbD (w - 1 - i) := by
  simp only [wordToBits, List.getElem_map, List.getElem_range, BitVec.getMsbD]
  simp at hi
  simp [hi]

/-! ## Array loops -/

/-- A `for i = 0 to n - 1 do a.(i) <- v i done` loop on an array. -/
theorem foldl_set!_const {α : Type*} [Inhabited α] (n : ℕ) (v : ℕ → α) (st : Array α) :
    ((List.range n).foldl (fun st i => st.set! i (v i)) st).size = st.size ∧
    ∀ j, ((List.range n).foldl (fun st i => st.set! i (v i)) st)[j]! =
      if j < n ∧ j < st.size then v j else st[j]! :=
  foldl_set!_self n (fun i _ => v i) st

/-- One step of the schedule loop `for i = 16 to R - 1`. -/
def schedStep {w : ℕ} (σ0 σ1 : BitVec w → BitVec w) (W : Array (BitVec w)) (i : ℕ) :
    Array (BitVec w) :=
  let x := W[i - 15]!
  let y := W[i - 2]!
  W.set! i ((W[i - 16]! + σ0 x) + (W[i - 7]! + σ1 y))

theorem schedule_ge {w : ℕ} (p : Params w) (Mi : Fin 16 → BitVec w) (t : ℕ) (ht : 16 ≤ t) :
    schedule p Mi t = p.smallSigma1 (schedule p Mi (t - 2)) + schedule p Mi (t - 7) +
      p.smallSigma0 (schedule p Mi (t - 15)) + schedule p Mi (t - 16) := by
  rw [schedule]; simp [show ¬ t < 16 by omega]

theorem schedule_lt {w : ℕ} (p : Params w) (Mi : Fin 16 → BitVec w) (t : ℕ) (ht : t < 16) :
    schedule p Mi t = Mi ⟨t, ht⟩ := by
  rw [schedule]; simp [ht]

/-- **Message schedule.** Starting from an array whose first 16 entries are
the block's words, the OCaml loop `for i = 16 to R − 1` computes FIPS 180-4's
`W_t` for all `t < R`. -/
theorem sched_spec {w : ℕ} (p : Params w) (Mi : Fin 16 → BitVec w) (σ0 σ1 : BitVec w → BitVec w)
    (h0 : ∀ x, σ0 x = p.smallSigma0 x) (h1 : ∀ x, σ1 x = p.smallSigma1 x) (R : ℕ)
    (W : Array (BitVec w)) (hW : W.size = R) (h16 : ∀ t (ht : t < 16), W[t]! = Mi ⟨t, ht⟩) :
    ∀ n, 16 + n ≤ R →
      ((List.range' 16 n).foldl (schedStep σ0 σ1) W).size = R ∧
      ∀ t < 16 + n, ((List.range' 16 n).foldl (schedStep σ0 σ1) W)[t]! = schedule p Mi t := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨hW, fun t ht => ?_⟩
    simp only [List.range'_zero, List.foldl_nil]
    rw [h16 t (by omega), schedule_lt p Mi t (by omega)]
  | succ n ih =>
    intro hn
    obtain ⟨ihs, ihg⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, Nat.one_mul]
    simp only [List.foldl_cons, List.foldl_nil, schedStep]
    refine ⟨by rw [Array.size_set!, ihs], fun t ht => ?_⟩
    rw [Array.getElem!_set!, ihs]
    by_cases hi : 16 + n = t
    · subst hi
      have e16 := ihg (16 + n - 16) (by omega)
      have e15 := ihg (16 + n - 15) (by omega)
      have e7 := ihg (16 + n - 7) (by omega)
      have e2 := ihg (16 + n - 2) (by omega)
      rw [ite_eq_left ⟨rfl, by omega⟩, e16, e15, e7, e2, schedule_ge p Mi (16 + n) (by omega), h0, h1]
      abel
    · rw [ite_eq_right (by omega)]
      exact ihg t (by omega)

/-- One iteration of the round loop (both `sha256` and `sha512` have this shape). -/
def roundStep {w : ℕ} (K : ℕ → BitVec w) (S0 S1 : BitVec w → BitVec w) (W : Array (BitVec w))
    (v : Vars w) (i : ℕ) : Vars w :=
  let s1 := S1 v.e
  let ch := (v.e &&& v.f) ^^^ ((~~~v.e) &&& v.g)
  let t1 := v.hh + (s1 + (ch + (K i + W[i]!)))
  let s0 := S0 v.a
  let maj := (v.a &&& v.b) ^^^ ((v.a &&& v.c) ^^^ (v.b &&& v.c))
  let t2 := s0 + maj
  { hh := v.g, g := v.f, f := v.e, e := v.d + t1, d := v.c, c := v.b, b := v.a, a := t1 + t2 }

/-- The working variables of the model as FIPS 180-4 `Work`. -/
def toWork {w : ℕ} (v : Vars w) : Work w := ⟨v.a, v.b, v.c, v.d, v.e, v.f, v.g, v.hh⟩

/-- **Rounds.** The OCaml round loop is FIPS 180-4 step 3 for `t = 0 … R − 1`. -/
theorem rounds_spec {w : ℕ} (p : Params w) (Wspec : ℕ → BitVec w) (K : ℕ → BitVec w)
    (S0 S1 : BitVec w → BitVec w) (W : Array (BitVec w)) (R : ℕ)
    (hK : ∀ t < R, K t = p.K t) (hW : ∀ t < R, W[t]! = Wspec t)
    (hS0 : ∀ x, S0 x = p.bigSigma0 x) (hS1 : ∀ x, S1 x = p.bigSigma1 x) (v : Vars w) :
    toWork ((List.range R).foldl (roundStep K S0 S1 W) v) =
      (List.range R).foldl (step p Wspec) (toWork v) := by
  refine (foldl_rel (List.range R) (roundStep K S0 S1 W) (step p Wspec) toWork (fun _ => True)
    (fun v i hi _ => ⟨trivial, ?_⟩) v trivial).2
  have hi' := List.mem_range.mp hi
  simp only [roundStep, step, toWork, hK i hi', hW i hi', hS0, hS1, Ch, Maj, BitVec.xor_assoc]
  congr 1 <;> abel

theorem addVars_get {w : ℕ} (h : Array (BitVec w)) (hh : h.size = 8) (v : Vars w) (j : Fin 8) :
    (addVars h v)[j.val]! =
      h[j.val]! + ![v.a, v.b, v.c, v.d, v.e, v.f, v.g, v.hh] j := by
  fin_cases j <;> simp [addVars, hh]

theorem addVars_size {w : ℕ} (h : Array (BitVec w)) (v : Vars w) : (addVars h v).size = h.size := by
  simp [addVars]

/-- FIPS 180-4 step 4, `H_j^{(i)} = (working variable j) + H_j^{(i−1)}`, from the model. -/
theorem compress_eq {w : ℕ} (p : Params w) (H : Fin 8 → BitVec w) (Mi : Fin 16 → BitVec w)
    (h : Array (BitVec w)) (hh : h.size = 8) (hH : ∀ j : Fin 8, h[j.val]! = H j) (v : Vars w)
    (hv : toWork v = (List.range p.rounds).foldl (step p (schedule p Mi))
      ⟨H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7⟩) (j : Fin 8) :
    (addVars h v)[j.val]! = compress p H Mi j := by
  rw [addVars_get h hh, hH, compress]
  rw [← hv]
  fin_cases j <;> simp [toWork, add_comm]

theorem toWork_varsOf {w : ℕ} (h : Array (BitVec w)) (H : Fin 8 → BitVec w)
    (hH : ∀ j : Fin 8, h[j.val]! = H j) :
    toWork (varsOf h) = ⟨H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7⟩ := by
  simp only [toWork, varsOf]
  rw [← hH 0, ← hH 1, ← hH 2, ← hH 3, ← hH 4, ← hH 5, ← hH 6, ← hH 7]
  rfl

end OcamlPq.Hash.Sha2
