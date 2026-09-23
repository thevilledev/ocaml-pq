import Mathlib

/-!
# Little-endian digit lists

Every encoding in FIPS 203 and FIPS 204 turns a list of `w`-bit integers into a
bit string (least significant bit first) and cuts that string into bytes.
Numerically, both the list of `w`-bit integers and the list of bytes are the
little-endian digits of the same natural number, in bases `2 ^ w` and `2 ^ 8`.

`Regroup w v a b` says exactly that: `a` is a list of `w`-bit digits, `b` a
list of `v`-bit digits, both carry the same number of bits, and they denote the
same number. Digit lists are unique (`Nat.ofDigits_inj_of_len_eq`), so each
side of a `Regroup` determines the other. Every equality between an OCaml model
and a FIPS algorithm in this directory is proved by showing that both are
`Regroup`s of the same input.
-/

namespace OcamlPq.Encoding

open Nat (ofDigits)

/-- `a` (digits of width `w`) and `b` (digits of width `v`) are the
little-endian digits of the same number and have the same total bit length. -/
structure Regroup (w v : ℕ) (a b : List ℕ) : Prop where
  length : a.length * w = b.length * v
  left_lt : ∀ x ∈ a, x < 2 ^ w
  right_lt : ∀ x ∈ b, x < 2 ^ v
  value : ofDigits (2 ^ w) a = ofDigits (2 ^ v) b

theorem Regroup.symm {w v : ℕ} {a b : List ℕ} (h : Regroup w v a b) : Regroup v w b a :=
  ⟨h.length.symm, h.right_lt, h.left_lt, h.value.symm⟩

theorem Regroup.trans {w u v : ℕ} {a b c : List ℕ} (h₁ : Regroup w u a b) (h₂ : Regroup u v b c) :
    Regroup w v a c :=
  ⟨h₁.length.trans h₂.length, h₁.left_lt, h₂.right_lt, h₁.value.trans h₂.value⟩

theorem Regroup.refl {w : ℕ} {a : List ℕ} (h : ∀ x ∈ a, x < 2 ^ w) : Regroup w w a a :=
  ⟨rfl, h, h, rfl⟩

/-- The `v`-bit side of a `Regroup` is determined by the `w`-bit side. -/
theorem Regroup.right_unique {w v : ℕ} (hv : 1 ≤ v) {a b₁ b₂ : List ℕ}
    (h₁ : Regroup w v a b₁) (h₂ : Regroup w v a b₂) : b₁ = b₂ := by
  have hb : 1 < 2 ^ v := Nat.one_lt_two_pow (by omega)
  refine Nat.ofDigits_inj_of_len_eq hb ?_ h₁.right_lt h₂.right_lt (h₁.value.symm.trans h₂.value)
  have := h₁.length.symm.trans h₂.length
  exact Nat.eq_of_mul_eq_mul_right (by omega) this

/-- The `w`-bit side of a `Regroup` is determined by the `v`-bit side. -/
theorem Regroup.left_unique {w v : ℕ} (hw : 1 ≤ w) {a₁ a₂ b : List ℕ}
    (h₁ : Regroup w v a₁ b) (h₂ : Regroup w v a₂ b) : a₁ = a₂ :=
  Regroup.right_unique hw h₁.symm h₂.symm

theorem ofDigits_two_pow_lt {w : ℕ} {l : List ℕ} (h : ∀ x ∈ l, x < 2 ^ w) :
    ofDigits (2 ^ w) l < 2 ^ (w * l.length) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := h x (by simp)
    have hl := ih (fun y hy => h y (by simp [hy]))
    rw [Nat.ofDigits_cons, List.length_cons, Nat.mul_succ, pow_add]
    have : ofDigits (2 ^ w) l + 1 ≤ 2 ^ (w * l.length) := hl
    calc x + 2 ^ w * ofDigits (2 ^ w) l < 2 ^ w + 2 ^ w * ofDigits (2 ^ w) l := by omega
      _ = 2 ^ w * (ofDigits (2 ^ w) l + 1) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * l.length) := Nat.mul_le_mul_left _ this
      _ = 2 ^ (w * l.length) * 2 ^ w := by ring

/-- Appending one digit. -/
theorem ofDigits_append_single (b : ℕ) (l : List ℕ) (x : ℕ) :
    ofDigits b (l ++ [x]) = ofDigits b l + b ^ l.length * x := by
  rw [Nat.ofDigits_append, Nat.ofDigits_singleton]

/-- `(range m).map (fun i => x / 2^i % 2)` are the low `m` bits of `x`. -/
theorem ofDigits_bits (x m : ℕ) :
    ofDigits 2 ((List.range m).map (fun i => x / 2 ^ i % 2)) = x % 2 ^ m := by
  induction m with
  | zero => simp [Nat.mod_one]
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, ofDigits_append_single, ih,
      List.length_map, List.length_range, Nat.mod_pow_succ]

theorem bits_lt_two (x m : ℕ) : ∀ y ∈ (List.range m).map (fun i => x / 2 ^ i % 2), y < 2 ^ 1 := by
  intro y hy
  simp only [List.mem_map, List.mem_range] at hy
  obtain ⟨i, -, rfl⟩ := hy
  simpa using Nat.mod_lt _ (by norm_num : 2 > 0)

/-- Concatenating the `c`-bit expansions of `c`-bit integers. -/
theorem regroup_flatMap_bits {c : ℕ} {codes : List ℕ} (h : ∀ x ∈ codes, x < 2 ^ c) :
    Regroup c 1 codes (codes.flatMap fun x => (List.range c).map (fun i => x / 2 ^ i % 2)) := by
  induction codes with
  | nil => exact ⟨by simp, by simp, by simp, by simp⟩
  | cons x l ih =>
    have hx := h x (by simp)
    have ih := ih (fun y hy => h y (by simp [hy]))
    refine ⟨?_, h, ?_, ?_⟩
    · simp only [List.length_cons, List.flatMap_cons, List.length_append, List.length_map,
        List.length_range]
      have := ih.length
      simp only [mul_one] at this ⊢
      rw [← this]; ring
    · intro y hy
      rw [List.flatMap_cons, List.mem_append] at hy
      rcases hy with hy | hy
      · exact bits_lt_two x c y hy
      · exact ih.right_lt y hy
    · have hv := ih.value
      simp only [pow_one] at hv ⊢
      rw [List.flatMap_cons, Nat.ofDigits_append, Nat.ofDigits_cons, ofDigits_bits,
        Nat.mod_eq_of_lt hx, List.length_map, List.length_range, ← hv]

/-- Chunking a digit list: the `c`-bit groups of a bit string. -/
theorem ofDigits_chunks (c N : ℕ) (z : ℕ → ℕ) :
    ofDigits (2 ^ c) ((List.range N).map
        (fun i => ofDigits 2 ((List.range c).map (fun t => z (i * c + t))))) =
      ofDigits 2 ((List.range (N * c)).map z) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, ofDigits_append_single, ih,
      Nat.succ_mul, List.range_add, List.map_append, Nat.ofDigits_append, List.map_map,
      List.length_map, List.length_range, List.length_map, List.length_range, ← pow_mul,
      mul_comm c N]
    rfl

theorem ofDigits_two_lt {l : List ℕ} (h : ∀ x ∈ l, x < 2) : ofDigits 2 l < 2 ^ l.length := by
  have := ofDigits_two_pow_lt (w := 1) (l := l) (by simpa using h)
  simpa using this

/-- `(range l.length).map (l.getD · d) = l`. -/
theorem map_getD_range' {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

/-- `(range l.length).map (l.getD · 0) = l`. -/
theorem map_getD_range (l : List ℕ) : (List.range l.length).map (fun i => l.getD i 0) = l :=
  map_getD_range' l 0

/-- Splitting `w`-bit digits into `c`-bit chunks, as a `Regroup`. -/
theorem regroup_chunks {c N : ℕ} {z : List ℕ} (hz : ∀ x ∈ z, x < 2) (hlen : z.length = N * c) :
    Regroup c 1 ((List.range N).map
        (fun i => ofDigits 2 ((List.range c).map (fun t => z.getD (i * c + t) 0)))) z := by
  refine ⟨?_, ?_, by simpa using hz, ?_⟩
  · simp [hlen]
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, -, rfl⟩ := hx
    have := ofDigits_two_lt (l := (List.range c).map (fun t => z.getD (i * c + t) 0)) (by
      intro y hy
      simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨t, -, rfl⟩ := hy
      by_cases ht : i * c + t < z.length
      · rw [List.getD_eq_getElem _ _ ht]; exact hz _ (List.getElem_mem ht)
      · rw [List.getD_eq_default _ _ (by omega)]; norm_num)
    simpa using this
  · have := ofDigits_chunks c N (fun t => z.getD t 0)
    rw [this, ← hlen, map_getD_range, pow_one]

end OcamlPq.Encoding
