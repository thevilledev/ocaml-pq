import OcamlPq.Encoding.Digits

/-!
# OCaml `Bytes`/`String` operations on byte lists

Byte strings are modelled as `List ℕ` (each entry a byte). These are the
buffer operations the encoders use; each is only applied within bounds, which
the layout theorems check.
-/

namespace OcamlPq.Encoding

theorem getD_lt_of_all {l : List ℕ} {m : ℕ} (hm : 0 < m) (h : ∀ x ∈ l, x < m) (i : ℕ) :
    l.getD i 0 < m := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; exact hm

/-- `Bytes.blit_string src srcoff dst dstoff len`. -/
def blit (src : List ℕ) (srcoff : ℕ) (dst : List ℕ) (dstoff len : ℕ) : List ℕ :=
  dst.take dstoff ++ (src.drop srcoff).take len ++ dst.drop (dstoff + len)

/-- `String.sub s off len`. -/
def sub (s : List ℕ) (off len : ℕ) : List ℕ := (s.drop off).take len

theorem length_blit (src : List ℕ) (dst : List ℕ) (dstoff len : ℕ)
    (hsrc : len ≤ src.length) (hdst : dstoff + len ≤ dst.length) :
    (blit src 0 dst dstoff len).length = dst.length := by
  simp [blit]; omega

/-- Blitting a whole string right after an already written prefix. -/
theorem blit_after_prefix (P src rest : List ℕ) :
    blit src 0 (P ++ rest) P.length src.length = (P ++ src) ++ rest.drop src.length := by
  simp [blit, List.take_left', List.drop_append, List.take_length]

theorem sub_prefix (P X R : List ℕ) : sub (P ++ X ++ R) P.length X.length = X := by
  simp [sub, List.take_left']

theorem sub_prefix' (P X R : List ℕ) (off len : ℕ) (hoff : off = P.length) (hlen : len = X.length) :
    sub (P ++ X ++ R) off len = X := by
  subst hoff hlen; exact sub_prefix P X R

theorem sub_prefix_end (P X : List ℕ) (off len : ℕ) (hoff : off = P.length) (hlen : len = X.length) :
    sub (P ++ X) off len = X := by
  have := sub_prefix' P X [] off len hoff hlen
  simpa using this

theorem length_sub (s : List ℕ) (off len : ℕ) (h : off + len ≤ s.length) :
    (sub s off len).length = len := by
  simp [sub]; omega

theorem sub_lt {s : List ℕ} (hs : ∀ x ∈ s, x < 256) (off len : ℕ) : ∀ x ∈ sub s off len, x < 256 :=
  fun x hx => hs x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

/-- Writing position `E.length` of a buffer whose first `E.length` entries
have been written. -/
theorem set_after_prefix (E init : List ℕ) (x : ℕ) (h : E.length < init.length) :
    (E ++ init.drop E.length).set E.length x = (E ++ [x]) ++ init.drop (E.length + 1) := by
  rw [List.set_append, ite_eq_right (by simp), Nat.sub_self, List.drop_eq_getElem_cons h,
    List.set_cons_zero, List.append_assoc]
  rfl

/-- The bytes of a flattened list of blocks: block `i` of a concatenation of
equal-length blocks sits at offset `i * len`. -/
theorem sub_flatten_blocks (blocks : List (List ℕ)) (len : ℕ)
    (hlen : ∀ b ∈ blocks, b.length = len) (R : List ℕ) (i : ℕ) (hi : i < blocks.length) :
    sub (blocks.flatten ++ R) (i * len) len = blocks[i] := by
  induction blocks generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    have hb := hlen b (by simp)
    cases i with
    | zero =>
      simp only [List.flatten_cons, zero_mul, List.getElem_cons_zero, List.append_assoc]
      have := sub_prefix [] b (bs.flatten ++ R)
      simpa [hb] using this
    | succ i =>
      simp only [List.flatten_cons, List.getElem_cons_succ, List.append_assoc]
      have ih' := ih (fun x hx => hlen x (by simp [hx])) i (by simpa using hi)
      unfold sub at ih' ⊢
      rw [show (i + 1) * len = b.length + i * len by rw [hb]; ring, ← List.drop_drop,
        List.drop_left']
      exact ih'
      rfl

theorem length_flatten_blocks (blocks : List (List ℕ)) (len : ℕ)
    (hlen : ∀ b ∈ blocks, b.length = len) : blocks.flatten.length = blocks.length * len := by
  induction blocks with
  | nil => simp
  | cons b bs ih =>
    simp [hlen b (by simp), ih (fun x hx => hlen x (by simp [hx]))]; ring

end OcamlPq.Encoding
