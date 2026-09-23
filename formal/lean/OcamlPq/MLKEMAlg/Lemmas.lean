import OcamlPq.MLKEMAlg.Impl

/-!
# Lemmas for the composition proofs

Slices, bytes, sums accumulated by `poly_add` loops, and the linearity of
NTT⁻¹ over finite sums.
-/

namespace OcamlPq.MLKEMAlg

open Spec

/-! ## Slices -/

theorem stringSub_eq_slice (s : Bytes) (off len : ℕ) : stringSub s off len = slice s off (off + len) := by
  simp only [stringSub, slice, List.drop_take]
  congr 1; omega

theorem slice_length (B : Bytes) (a b : ℕ) (h : b ≤ B.length) (hab : a ≤ b) :
    (slice B a b).length = b - a := by
  simp [slice]; omega

theorem slice_slice (B : Bytes) (a b c d : ℕ) (h : a + d ≤ b) :
    slice (slice B a b) c d = slice B (a + c) (a + d) := by
  simp only [slice, List.take_drop, List.drop_drop, List.take_take]
  rw [min_eq_left h]

theorem slice_append_left (x y : Bytes) : slice (x ++ y) 0 x.length = x := by
  simp [slice]

theorem slice_append_right (x y : Bytes) (a b : ℕ) :
    slice (x ++ y) (x.length + a) (x.length + b) = slice y a b := by
  simp only [slice, List.take_append, List.drop_append]
  rw [List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega)]
  simp

theorem slice_append_right' (x y : Bytes) : slice (x ++ y) x.length (x.length + y.length) = y := by
  have := slice_append_right x y 0 y.length
  rw [Nat.add_zero] at this
  rw [this]; simp [slice]

theorem slice_all (B : Bytes) : slice B 0 B.length = B := by simp [slice]

/-- The `i`-th chunk of a concatenation of equal-length chunks. -/
theorem slice_flatten_ofFn {k : ℕ} (c : ℕ) (f : Fin k → Bytes) (hf : ∀ i, (f i).length = c) (i : Fin k) :
    slice (List.ofFn f).flatten (c * i.val) (c * (i.val + 1)) = f i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero, mul_zero, zero_add, mul_one]
      rw [← hf 0, slice_append_left]
    · simp only [Fin.val_succ]
      rw [show c * (j.val + 1) = (f 0).length + c * j.val by rw [hf]; ring,
        show c * (j.val + 1 + 1) = (f 0).length + c * (j.val + 1) by rw [hf]; ring,
        slice_append_right]
      exact ih (fun j => f j.succ) (fun j => hf _) j

theorem flatten_ofFn_length {k : ℕ} (c : ℕ) (f : Fin k → Bytes) (hf : ∀ i, (f i).length = c) :
    (List.ofFn f).flatten.length = k * c := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hf, ih (fun j => f j.succ) (fun _ => hf _)]
    ring

/-! ## Bytes -/

theorem unsafeChr_eq_byte (x : ℕ) : unsafeChr (x : ℤ) = byte x := by
  ext; simp only [unsafeChr, byte]; omega

theorem byteString_eq (x : ℕ) : byteString (x : ℤ) = [byte x] := by
  simp [byteString, unsafeChr_eq_byte]

theorem byte_eq_mk {x : ℕ} (h : x < 256) : byte x = ⟨x, h⟩ := by
  ext; simp [byte, Nat.mod_eq_of_lt h]

/-! ## Accumulation loops -/

section Sums

variable {I : ImplPrims} {S : SpecPrims}

/-- A loop `acc := poly_add acc (f j)` over a list of indices accumulates the
    sum of the spec values. -/
theorem foldl_polyAdd (hR : Refines I S) {ι : Type} (f : ι → IPoly) (hf : ∀ j, Canonical (f j))
    (L : List ι) (init : IPoly) (hinit : Canonical init) :
    Canonical (L.foldl (fun acc j => I.polyAdd acc (f j)) init) ∧
      toSpec (L.foldl (fun acc j => I.polyAdd acc (f j)) init) =
        toSpec init + (L.map fun j => toSpec (f j)).sum := by
  induction L generalizing init with
  | nil => simp [hinit]
  | cons x L ih =>
    obtain ⟨h1, h2⟩ := hR.polyAdd init (f x) hinit (hf x)
    obtain ⟨h3, h4⟩ := ih (I.polyAdd init (f x)) h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2, List.map_cons, List.sum_cons, add_assoc]

/-- The same over `for j = 0 to k - 1`, as a `Finset` sum. -/
theorem foldl_polyAdd_finRange (hR : Refines I S) {k : ℕ} (f : Fin k → IPoly)
    (hf : ∀ j, Canonical (f j)) (init : IPoly) (hinit : Canonical init) :
    Canonical ((List.finRange k).foldl (fun acc j => I.polyAdd acc (f j)) init) ∧
      toSpec ((List.finRange k).foldl (fun acc j => I.polyAdd acc (f j)) init) =
        toSpec init + ∑ j, toSpec (f j) := by
  obtain ⟨h1, h2⟩ := foldl_polyAdd hR f hf (List.finRange k) init hinit
  refine ⟨h1, ?_⟩
  rw [h2, ← List.ofFn_eq_map, List.sum_ofFn]

/-- NTT⁻¹ distributes over finite sums. -/
theorem invNTT_sum (hL : S.Laws) {k : ℕ} (f : Fin k → Poly) :
    S.invNTT (∑ j, f j) = ∑ j, S.invNTT (f j) :=
  map_sum (AddMonoidHom.mk' S.invNTT hL.invNTT_add) f Finset.univ

end Sums

end OcamlPq.MLKEMAlg
