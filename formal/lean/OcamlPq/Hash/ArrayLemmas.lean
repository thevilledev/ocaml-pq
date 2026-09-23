import Mathlib

/-!
# Small lemmas about `Array.set!` / `[i]!` and `List.set` used by the models
-/

namespace OcamlPq.Hash

theorem Array.getElem!_set! {α : Type*} [Inhabited α] (xs : Array α) (i j : ℕ) (v : α) :
    (xs.set! i v)[j]! = if i = j ∧ j < xs.size then v else xs[j]! := by
  simp only [Array.set!_eq_setIfInBounds]
  by_cases hj : j < xs.size
  · rw [getElem!_pos (xs.setIfInBounds i v) j (by simpa using hj), getElem!_pos xs j hj,
      Array.getElem_setIfInBounds hj]
    by_cases hij : i = j <;> simp [hij, hj]
  · rw [getElem!_neg (xs.setIfInBounds i v) j (by simpa using hj), getElem!_neg xs j hj]
    simp [hj]

theorem Array.size_set! {α : Type*} (xs : Array α) (i : ℕ) (v : α) :
    (xs.set! i v).size = xs.size := by
  simp

theorem List.getElem!_set' {α : Type*} [Inhabited α] (l : List α) (i j : ℕ) (v : α) :
    (l.set i v)[j]! = if i = j ∧ j < l.length then v else l[j]! := by
  by_cases hj : j < l.length
  · rw [getElem!_pos (l.set i v) j (by simpa using hj), getElem!_pos l j hj, List.getElem_set]
    by_cases hij : i = j <;> simp [hij, hj]
  · rw [getElem!_neg (l.set i v) j (by simpa using hj), getElem!_neg l j hj]
    simp [hj]

theorem List.getElem!_replicate_zero (n j : ℕ) : (List.replicate n (0 : UInt8))[j]! = 0 := by
  by_cases hj : j < n
  · rw [getElem!_pos _ j (by simpa using hj)]; simp
  · rw [getElem!_neg _ j (by simpa using hj)]; rfl

/-- Two folds over the same list stay related by `φ` when each step does. -/
theorem foldl_rel {α β γ : Type*} (l : List γ) (F : α → γ → α) (G : β → γ → β) (φ : α → β)
    (inv : α → Prop) (h : ∀ a i, i ∈ l → inv a → inv (F a i) ∧ φ (F a i) = G (φ a) i)
    (a : α) (ha : inv a) : inv (l.foldl F a) ∧ φ (l.foldl F a) = l.foldl G (φ a) := by
  induction l generalizing a with
  | nil => exact ⟨ha, rfl⟩
  | cons i l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := h a i (by simp) ha
    rw [← h2]
    exact ih (fun a' i' hi' ha' => h a' i' (by simp [hi']) ha') _ h1

end OcamlPq.Hash
