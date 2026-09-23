import OcamlPq.Hash.KeccakConstants
import OcamlPq.Hash.ArrayLemmas

/-!
# `permute` is Keccak-f[1600]

The main theorem, `permute_eq_KeccakF`: for every 25-lane state `a`,
`laneBits (permute a) = KeccakF (laneBits a)`, where `laneBits` reads lane
`i = x + 5y` as the 64 bits `z = 0 … 63` (least significant first), placed at
string positions `64 i + z` (FIPS 202 §3.1.2: `A[x, y, z] = S[w(5y + x) + z]`).

The proof has three layers:

1. each OCaml loop of one round is characterised lane by lane
   (`thetaCLoop_get` … `chiLoop_get`);
2. those characterisations are compared bit by bit with FIPS 202 θ, ρ, π, χ,
   ι (`permRound_toState`), using `rho_eq`, `roundConstants_eq_RC` and
   `getLsbD_rotl`;
3. the 24 rounds and the string ↔ state conversions are assembled.
-/

namespace OcamlPq.Hash.Keccak

open FIPS202

/-! ## `rotl` -/

/-- `rotl x n` is the rotation `x.rotateLeft n` for `0 ≤ n < 64`
(including the special case `n = 0`, where the OCaml code avoids the
unspecified `shift_right_logical x 64`). -/
theorem rotl_eq_rotateLeft (v : BitVec 64) {n : ℕ} (hn : n < 64) : rotl v n = v.rotateLeft n := by
  unfold rotl
  split
  · subst_vars; rw [BitVec.rotateLeft_def]; simp [BitVec.ushiftRight_eq_zero]
  · rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt hn]

/-- Bit `z` of `rotl v n` is bit `(z − n) mod 64` of `v`: the FIPS 202 lane
rotation `A′[z] = A[(z − n) mod w]`. -/
theorem getLsbD_rotl (v : BitVec 64) {n : ℕ} (hn : n < 64) (z : Fin 64) :
    (rotl v n).getLsbD z.val = v.getLsbD (z - Fin.ofNat 64 n).val := by
  rw [rotl_eq_rotateLeft v hn, BitVec.getLsbD_rotateLeft, Fin.sub_def]
  simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hn]
  have hz := z.isLt
  split
  · congr 1; omega
  · simp only [hz, decide_true, Bool.true_and]; congr 1; omega

theorem getLsbD_rotl_one (v : BitVec 64) (z : Fin 64) :
    (rotl v 1).getLsbD z.val = v.getLsbD (z - 1).val :=
  getLsbD_rotl v (by norm_num) z

/-! ## The loops of one round, lane by lane -/

theorem thetaCLoop_size (a cc : Array (BitVec 64)) : (thetaCLoop a cc).size = cc.size := by
  simp [thetaCLoop, List.range_succ]

theorem thetaDLoop_size (cc d : Array (BitVec 64)) : (thetaDLoop cc d).size = d.size := by
  simp [thetaDLoop, List.range_succ]

theorem thetaALoop_size (a d : Array (BitVec 64)) : (thetaALoop a d).size = a.size := by
  simp [thetaALoop, List.range_succ]

theorem rhoPiLoop_size (a b : Array (BitVec 64)) : (rhoPiLoop a b).size = b.size := by
  simp [rhoPiLoop, List.range_succ]

theorem chiLoop_size (a b : Array (BitVec 64)) : (chiLoop a b).size = a.size := by
  simp [chiLoop, List.range_succ]

theorem thetaCLoop_get (a cc : Array (BitVec 64)) (hc : cc.size = 5) (x : Fin 5) :
    (thetaCLoop a cc)[x.val]! =
      a[x.val]! ^^^ (a[x.val + 5]! ^^^ (a[x.val + 10]! ^^^ (a[x.val + 15]! ^^^ a[x.val + 20]!))) := by
  fin_cases x <;> simp [thetaCLoop, List.range_succ, hc]

theorem thetaDLoop_get (cc d : Array (BitVec 64)) (hd : d.size = 5) (x : Fin 5) :
    (thetaDLoop cc d)[x.val]! = cc[(x - 1).val]! ^^^ rotl (cc[(x + 1).val]!) 1 := by
  fin_cases x <;> simp [thetaDLoop, List.range_succ, hd]

set_option maxHeartbeats 2000000 in
theorem thetaALoop_get (a d : Array (BitVec 64)) (ha : a.size = 25) (x y : Fin 5) :
    (thetaALoop a d)[x.val + 5 * y.val]! = a[x.val + 5 * y.val]! ^^^ d[x.val]! := by
  fin_cases x <;> fin_cases y <;> simp [thetaALoop, List.range_succ, ha]

set_option maxHeartbeats 2000000 in
theorem rhoPiLoop_get (a b : Array (BitVec 64)) (hb : b.size = 25) (x y : Fin 5) :
    (rhoPiLoop a b)[x.val + 5 * y.val]! =
      rotl (a[(x + 3 * y).val + 5 * x.val]!) (rotation[(x + 3 * y).val + 5 * x.val]!) := by
  fin_cases x <;> fin_cases y <;> simp [rhoPiLoop, List.range_succ, hb]

set_option maxHeartbeats 2000000 in
theorem chiLoop_get (a b : Array (BitVec 64)) (ha : a.size = 25) (x y : Fin 5) :
    (chiLoop a b)[x.val + 5 * y.val]! =
      b[x.val + 5 * y.val]! ^^^ ((~~~(b[(x + 1).val + 5 * y.val]!)) &&& b[(x + 2).val + 5 * y.val]!) := by
  fin_cases x <;> fin_cases y <;> simp [chiLoop, List.range_succ, ha]

/-! ## One round, bit by bit -/

/-- The FIPS 202 state array held by a 25-lane OCaml state:
`A[x, y, z]` is bit `z` (least significant first) of `a.(x + 5y)`. -/
def toState (a : Array (BitVec 64)) : State := fun x y z => (a[x.val + 5 * y.val]!).getLsbD z.val

/-- The array sizes that `permute` maintains. -/
structure PermState.WF (s : PermState) : Prop where
  a : s.a.size = 25
  c : s.c.size = 5
  d : s.d.size = 5
  b : s.b.size = 25

theorem permRound_wf (s : PermState) (h : s.WF) (r : ℕ) : (permRound s r).WF where
  a := by simp [permRound, chiLoop_size, thetaALoop_size, h.a]
  c := by simp [permRound, thetaCLoop_size, h.c]
  d := by simp [permRound, thetaDLoop_size, h.d]
  b := by simp [permRound, rhoPiLoop_size, h.b]

@[simp] theorem fin5_val_two : ((2 : Fin 5) : ℕ) = 2 := rfl
@[simp] theorem fin5_val_three : ((3 : Fin 5) : ℕ) = 3 := rfl
@[simp] theorem fin5_val_four : ((4 : Fin 5) : ℕ) = 4 := rfl

section round
variable (s : PermState) (h : s.WF)
include h

/-- After the three θ loops, lane `(x, y)` holds FIPS 202 θ. -/
theorem theta_lane (x y : Fin 5) (z : Fin 64) :
    ((thetaALoop s.a (thetaDLoop (thetaCLoop s.a s.c) s.d))[x.val + 5 * y.val]!).getLsbD z.val =
      theta (toState s.a) x y z := by
  rw [thetaALoop_get _ _ h.a, BitVec.getLsbD_xor, thetaDLoop_get _ _ h.d, BitVec.getLsbD_xor,
    getLsbD_rotl_one, thetaCLoop_get _ _ h.c, thetaCLoop_get _ _ h.c]
  simp [theta, toState]

/-- After the π/ρ loop, lane `(x, y)` of `b` holds FIPS 202 π(ρ(θ(A))). -/
theorem pi_lane (x y : Fin 5) (z : Fin 64) :
    ((rhoPiLoop (thetaALoop s.a (thetaDLoop (thetaCLoop s.a s.c) s.d)) s.b)[x.val + 5 * y.val]!).getLsbD
      z.val = pi (rho (theta (toState s.a))) x y z := by
  rw [rhoPiLoop_get _ _ h.b, getLsbD_rotl _ (rotation_lt _ (by omega)), pi, rho_eq,
    theta_lane s h]

/-- After the χ loop, lane `(x, y)` holds FIPS 202 χ(π(ρ(θ(A)))). -/
theorem chi_lane (x y : Fin 5) (z : Fin 64) :
    ((chiLoop (thetaALoop s.a (thetaDLoop (thetaCLoop s.a s.c) s.d))
      (rhoPiLoop (thetaALoop s.a (thetaDLoop (thetaCLoop s.a s.c) s.d)) s.b))[x.val + 5 * y.val]!).getLsbD
      z.val = chi (pi (rho (theta (toState s.a)))) x y z := by
  rw [chiLoop_get _ _ (by rw [thetaALoop_size]; exact h.a), BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_not, pi_lane s h, pi_lane s h, pi_lane s h]
  simp [chi]

/-- One iteration of the OCaml round loop is FIPS 202 `Rnd(A, ir)`. -/
theorem permRound_toState (r : ℕ) (hr : r < 24) :
    toState (permRound s r).a = Rnd (toState s.a) r := by
  funext x y z
  have hsz : (chiLoop (thetaALoop s.a (thetaDLoop (thetaCLoop s.a s.c) s.d))
      (rhoPiLoop (thetaALoop s.a (thetaDLoop (thetaCLoop s.a s.c) s.d)) s.b)).size = 25 := by
    rw [chiLoop_size, thetaALoop_size, h.a]
  simp only [permRound, toState, Rnd, iota]
  rw [Array.getElem!_set!, hsz]
  by_cases hxy : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := hxy
    have := chi_lane s h 0 0 z
    simp only [Fin.val_zero, mul_zero, add_zero] at this
    simp only [Fin.val_zero, mul_zero, add_zero, and_self, Nat.ofNat_pos, ite_true,
      BitVec.getLsbD_xor, this, roundConstants_eq_RC ⟨r, hr⟩ z]
  · have h1 : ¬ (0 = x.val + 5 * y.val ∧ x.val + 5 * y.val < 25) := by
      rintro ⟨h0, -⟩
      exact hxy ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
    rw [ite_eq_right h1, ite_eq_right hxy]
    exact chi_lane s h x y z

end round

/-! ## The whole permutation -/

theorem foldl_permRound (l : List ℕ) (hl : ∀ r ∈ l, r < 24) (s : PermState) (h : s.WF) :
    (l.foldl permRound s).WF ∧ toState (l.foldl permRound s).a = l.foldl Rnd (toState s.a) := by
  induction l generalizing s with
  | nil => exact ⟨h, rfl⟩
  | cons r l ih =>
    simp only [List.foldl_cons]
    rw [← permRound_toState s h r (hl r (by simp))]
    exact ih (fun r' hr' => hl r' (by simp [hr'])) _ (permRound_wf s h r)

/-- `permute` preserves the array size. -/
theorem permute_size (a : Array (BitVec 64)) (ha : a.size = 25) : (permute a).size = 25 :=
  (foldl_permRound (List.range 24) (fun _ hr => List.mem_range.mp hr) _
    ⟨ha, rfl, rfl, rfl⟩).1.a

/-- `permute` runs the 24 FIPS 202 rounds `Rnd(·, 0)`, …, `Rnd(·, 23)` on
the state array. -/
theorem permute_toState (a : Array (BitVec 64)) (ha : a.size = 25) :
    toState (permute a) = (List.range 24).foldl Rnd (toState a) :=
  (foldl_permRound (List.range 24) (fun _ hr => List.mem_range.mp hr) _ ⟨ha, rfl, rfl, rfl⟩).2

/-- The 1600-bit FIPS 202 string of a 25-lane state: position `64 i + z`
is bit `z` of lane `i`. -/
def laneBits (a : Array (BitVec 64)) : Bits :=
  List.ofFn fun k : Fin 1600 => (a[k.val / 64]!).getLsbD (k.val % 64)

@[simp] theorem laneBits_length (a : Array (BitVec 64)) : (laneBits a).length = 1600 := by
  simp only [laneBits, List.length_ofFn]

theorem ofString_laneBits (a : Array (BitVec 64)) : ofString (laneBits a) = toState a := by
  funext x y z
  have hx := x.isLt; have hy := y.isLt; have hz := z.isLt
  have hk : w * (5 * y.val + x.val) + z.val < 1600 := by simp only [w]; omega
  simp only [ofString, toState, laneBits]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk), List.getElem_ofFn]
  simp only [w]
  congr 2 <;> omega

/-- §3.1.3 state-to-string conversion as a closed formula. -/
theorem toString_eq (A : State) :
    FIPS202.toString A = List.ofFn (fun k : Fin 1600 =>
      A ⟨k.val / 64 % 5, by omega⟩ ⟨k.val / 64 / 5, by omega⟩ ⟨k.val % 64, by omega⟩) := by
  have h1 : FIPS202.toString A = ((List.finRange 5).flatMap fun j => (List.finRange 5).flatMap
      fun i => (List.finRange 64).map fun k => (i, j, k)).map (fun p => A p.1 p.2.1 p.2.2) := by
    simp [FIPS202.toString, plane, lane, List.map_flatMap, List.map_map, Function.comp_def]
  have h2 : ((List.finRange 5).flatMap fun j => (List.finRange 5).flatMap
      fun i => (List.finRange 64).map fun k => (i, j, k)) = List.ofFn (fun k : Fin 1600 =>
      ((⟨k.val / 64 % 5, by omega⟩ : Fin 5), (⟨k.val / 64 / 5, by omega⟩ : Fin 5),
        (⟨k.val % 64, by omega⟩ : Fin 64))) := by
    decide +kernel
  rw [h1, h2, List.map_ofFn]
  rfl

theorem toString_toState (a : Array (BitVec 64)) : FIPS202.toString (toState a) = laneBits a := by
  rw [toString_eq, laneBits]
  congr 1
  funext k
  simp only [toState]
  congr 2
  omega

/-- **`permute` is Keccak-f[1600].** For every 25-lane state, the FIPS 202
string of `permute a` is `KECCAK-f[1600]` (= `KECCAK-p[1600, 24]`) of the
string of `a`. -/
theorem permute_eq_KeccakF (a : Array (BitVec 64)) (ha : a.size = 25) :
    laneBits (permute a) = KeccakF (laneBits a) := by
  rw [KeccakF, KeccakP, ofString_laneBits]
  simp only [ℓ, show 12 + 2 * 6 - 24 = 0 from rfl, ← List.range_eq_range']
  rw [← permute_toState a ha, toString_toState]

end OcamlPq.Hash.Keccak
