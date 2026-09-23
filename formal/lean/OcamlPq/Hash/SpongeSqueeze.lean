import OcamlPq.Hash.SpongeAbsorb

/-!
# The squeezing phase of `sponge`

* `squeezeLoop_spec`: the OCaml `while` loop (`lib/keccak.ml` lines 103–113)
  fills byte `k` of the output with byte `k mod rate` of the rate part of
  `permute^[k / rate] S`, stops with `!produced = output_length`, and leaves
  the state at `permute^[(output_length − 1) / rate] S`: exactly one
  permutation between consecutive rate-blocks and none after the last.
* `squeeze_spec`: FIPS 202 Algorithm 8 steps 7–10 output bit `t` of
  `Z = Trunc_r(S) ‖ Trunc_r(f(S)) ‖ …`, i.e. bit `t mod r` of `f^[t / r](S)`.
-/

namespace OcamlPq.Hash.Keccak

open FIPS202

/-- Byte `j` of the rate part of a state, as `store64_le` writes it:
`(a.(j / 8) lsr (8 · (j mod 8))) land 0xff`. -/
def blockByte (s : Array (BitVec 64)) (j : ℕ) : UInt8 :=
  byteOfInt64 ((s[j / 8]! >>> (8 * (j % 8))) &&& 0xff#64)

/-- Output byte `k` of the sponge started from state `a0`. -/
def outByte (a0 : Array (BitVec 64)) (rate k : ℕ) : UInt8 :=
  blockByte (permute^[k / rate] a0) (k % rate)

/-- The block-building loop `for i = 0 to rate/8 - 1 do store64_le block (8i) state.(i)`. -/
theorem squeezeBlock_spec (n : ℕ) (state : Array (BitVec 64)) (junk : List UInt8) :
    ((List.range n).foldl (fun blk i => store64Le blk (8 * i) (state[i]!)) junk).length =
      junk.length ∧
    ∀ j, ((List.range n).foldl (fun blk i => store64Le blk (8 * i) (state[i]!)) junk)[j]! =
      if j < 8 * n ∧ j < junk.length then blockByte state j else junk[j]! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [store64Le_length, ih.1], fun j => ?_⟩
    rw [store64Le_get, ih.1, ih.2 j]
    by_cases h1 : 8 * n ≤ j ∧ j < 8 * n + 8 ∧ j < junk.length
    · rw [ite_eq_left h1, ite_eq_left (by omega), blockByte]
      have e1 : j / 8 = n := by omega
      have e2 : j % 8 = j - 8 * n := by omega
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : j < 8 * n ∧ j < junk.length
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem squeezeLoop_done (rate L : ℕ) (junk : ℕ → List UInt8) (fuel : ℕ) (st : Array (BitVec 64))
    (out : List UInt8) : squeezeLoop rate L junk fuel st out L = (st, out, L) := by
  cases fuel <;> simp [squeezeLoop]

/-- **The squeeze loop.** Started after `m` complete blocks (state
`permute^[m] a0`, `!produced = m · rate < L`, the first `m · rate` output bytes
already correct) with enough fuel, the loop ends with `!produced = L`, every
output byte `k < L` equal to `outByte a0 rate k`, and the state
`permute^[(L − 1) / rate] a0`. -/
theorem squeezeLoop_spec (rate L : ℕ) (hr : 0 < rate) (hr8 : rate % 8 = 0)
    (junk : ℕ → List UInt8) (hj : ∀ p, (junk p).length = rate) (a0 : Array (BitVec 64)) :
    ∀ fuel m (out : List UInt8), m * rate < L → L - m * rate < fuel → out.length = L →
      (∀ k < m * rate, out[k]! = outByte a0 rate k) →
      (squeezeLoop rate L junk fuel (permute^[m] a0) out (m * rate)).2.2 = L ∧
      (squeezeLoop rate L junk fuel (permute^[m] a0) out (m * rate)).2.1.length = L ∧
      (∀ k < L, (squeezeLoop rate L junk fuel (permute^[m] a0) out (m * rate)).2.1[k]! =
        outByte a0 rate k) ∧
      (squeezeLoop rate L junk fuel (permute^[m] a0) out (m * rate)).1 =
        permute^[(L - 1) / rate] a0 := by
  intro fuel
  induction fuel with
  | zero => intro m out h1 h2; omega
  | succ fuel ih =>
    intro m out h1 h2 h3 h4
    have h88 : 8 * (rate / 8) = rate := by omega
    obtain ⟨hbl, hbg⟩ := squeezeBlock_spec (rate / 8) (permute^[m] a0) (junk (m * rate))
    have hj' := hj (m * rate)
    simp only [squeezeLoop, ite_eq_left h1]
    generalize hblk : (List.range (rate / 8)).foldl
      (fun blk i => store64Le blk (8 * i) ((permute^[m] a0)[i]!)) (junk (m * rate)) = blk at hbl hbg
    generalize htake : min rate (L - m * rate) = take
    have hmr : (m + 1) * rate = m * rate + rate := by ring
    -- the bytes written by this iteration
    have hnew : ∀ k, m * rate ≤ k → k < m * rate + take → k < L →
        (blitString blk 0 out (m * rate) take)[k]! = outByte a0 rate k := by
      intro k hk1 hk2 hk3
      rw [blitString_get, ite_eq_left ⟨hk1, hk2, by omega⟩, hbg, ite_eq_left (by omega)]
      have hdiv : k / rate = m := Nat.div_eq_of_lt_le (by omega) (by omega)
      have hmod : k % rate = 0 + (k - m * rate) := by
        have := Nat.div_add_mod k rate
        rw [hdiv, Nat.mul_comm] at this
        omega
      rw [outByte, hdiv, hmod]
    have hold : ∀ k, k < m * rate → (blitString blk 0 out (m * rate) take)[k]! = out[k]! := by
      intro k hk
      rw [blitString_get, ite_eq_right (by omega)]
    by_cases hA : m * rate + take < L
    · -- another block follows: one permutation, then continue with `m + 1`
      have ht : take = rate := by omega
      rw [ite_eq_left hA, show m * rate + take = (m + 1) * rate by rw [ht, hmr],
        ← Function.iterate_succ_apply' permute m a0]
      refine ih (m + 1) _ (by omega) (by omega) (by rw [blitString_length, h3]) ?_
      intro k hk
      by_cases hk' : k < m * rate
      · rw [hold k hk', h4 k hk']
      · exact hnew k (by omega) (by omega) (by omega)
    · -- the last block: no permutation
      rw [ite_eq_right hA, show m * rate + take = L by omega, squeezeLoop_done]
      refine ⟨rfl, by rw [blitString_length, h3], ?_, ?_⟩
      · intro k hk
        by_cases hk' : k < m * rate
        · rw [hold k hk', h4 k hk']
        · exact hnew k (by omega) (by omega) hk
      · rw [Nat.div_eq_of_lt_le (k := m) (n := rate) (m := L - 1) (by omega) (by rw [hmr]; omega)]

/-- Bit `t` of FIPS 202's `Z = Trunc_r(S) ‖ Trunc_r(f(S)) ‖ …`. -/
def Zbit (f : Bits → Bits) (R : ℕ) (S0 : Bits) (t : ℕ) : Bool := (f^[t / R] S0).getD (t % R) false

/-- **FIPS 202 squeezing.** Algorithm 8 steps 7–10 return the first `d` bits of
`Z = Trunc_r(S) ‖ Trunc_r(f(S)) ‖ Trunc_r(f(f(S))) ‖ …`. -/
theorem squeeze_spec (f : Bits → Bits) (R d : ℕ) (S0 : Bits)
    (hlen : ∀ m, R ≤ (f^[m] S0).length) :
    ∀ fuel m (Z : Bits), Z.length = m * R → (∀ t (h : t < Z.length), Z[t] = Zbit f R S0 t) →
      (m = 0 ∨ m * R < d) → d ≤ (m + fuel) * R →
      squeeze f R d fuel (f^[m] S0) Z = List.ofFn fun t : Fin d => Zbit f R S0 t := by
  intro fuel
  induction fuel with
  | zero =>
    intro m Z hZ hZg hm hd
    have hd0 : d = 0 := by
      rcases hm with rfl | hm
      · simpa using hd
      · simp at hd; omega
    subst hd0
    have : Z = [] := by
      rcases hm with rfl | hm
      · simpa using hZ
      · omega
    simp [squeeze, this]
  | succ fuel ih =>
    intro m Z hZ hZg hm hd
    have hmr : (m + 1) * R = m * R + R := by ring
    have hS := hlen m
    -- `Z ‖ Trunc_R(f^[m] S0)` holds the first `(m+1)·R` bits
    have hZ' : (Z ++ trunc R (f^[m] S0)).length = (m + 1) * R := by
      simp [trunc, hZ, hmr]; omega
    have hZ'g : ∀ t (h : t < (Z ++ trunc R (f^[m] S0)).length),
        (Z ++ trunc R (f^[m] S0))[t] = Zbit f R S0 t := by
      intro t ht
      rw [List.getElem_append]
      split
      · exact hZg t _
      · rename_i hlt
        simp only [trunc, List.getElem_take]
        rw [hZ'] at ht
        have hdiv : t / R = m := Nat.div_eq_of_lt_le (by omega) (by omega)
        have hmod : t % R = t - Z.length := by
          have := Nat.div_add_mod t R
          rw [hdiv, Nat.mul_comm] at this
          omega
        rw [Zbit, hdiv, hmod, List.getD_eq_getElem]
    simp only [squeeze]
    split
    · rename_i hle
      apply List.ext_getElem
      · simp [trunc]; omega
      · intro t h1 h2
        simp only [trunc, List.getElem_take, List.getElem_ofFn]
        exact hZ'g t _
    · rename_i hlt
      rw [← Function.iterate_succ_apply' f m S0]
      exact ih (m + 1) _ hZ' hZ'g (Or.inr (by omega)) (by rw [hZ'] at hlt; nlinarith)

end OcamlPq.Hash.Keccak
