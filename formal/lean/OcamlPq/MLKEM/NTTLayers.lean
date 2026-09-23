import OcamlPq.MLKEM.NTTSpec

/-!
# Layer structure of the FIPS 203 NTT

Splits `fipsNtt` and `fipsNttInv` into seven layers: layer `k < 7` has
`len = 2^(7−k)` and `2^k` blocks of size `2·len`; the forward layer uses
`ζ^BitRev7(2^k + b)` on block `b`, the inverse layer `ζ^BitRev7(2^(k+1) − 1 − b)`.
From this:

* `fipsNttInv_fipsNtt`: `NTT⁻¹(NTT(f)) = f` on indices `< 256`;
* `fipsNtt_fipsNttInv`: `NTT(NTT⁻¹(f̂)) = f̂` on indices `< 256`.

The finite facts about `ζ` (`zeta_inv_check`) are kernel evaluations.
-/

namespace OcamlPq.MLKEM

/-- Two arrays agree on the indices `< 256` that the algorithms use. -/
def EqOn256 (g h : Poly) : Prop := ∀ p < 256, g p = h p

theorem layer_blocks {k : ℕ} (hk : k < 7) : 2 ^ k * (2 * 2 ^ (7 - k)) = 256 := by
  rw [← pow_succ', ← pow_add, show k + (7 - k + 1) = 8 by omega]; norm_num

/-- Layer `k` of Algorithm 9 (`len = 2^(7−k)`, starting `i = 2^k`). -/
def nttLayer (k : ℕ) (g : Poly) : Poly :=
  (fipsNttStartLoop (2 ^ (7 - k)) (by positivity) 0 (2 ^ k) g).1

/-- Layer `k` of Algorithm 10 (`len = 2^(7−k)`, starting `i = 2^(k+1) − 1`). -/
def invLayer (k : ℕ) (g : Poly) : Poly :=
  (fipsInvStartLoop (2 ^ (7 - k)) (by positivity) 0 (2 ^ (k + 1) - 1) g).1

/-! ## Block formulas -/

theorem nttLayer_block {k : ℕ} (hk : k < 7) (g : Poly) {b r : ℕ} (hb : b < 2 ^ k)
    (hr : r < 2 * 2 ^ (7 - k)) :
    nttLayer k g (b * (2 * 2 ^ (7 - k)) + r) =
      if r < 2 ^ (7 - k) then
        g (b * (2 * 2 ^ (7 - k)) + r) +
          zeta ^ bitRev7 (2 ^ k + b) * g (b * (2 * 2 ^ (7 - k)) + r + 2 ^ (7 - k))
      else
        g (b * (2 * 2 ^ (7 - k)) + r - 2 ^ (7 - k)) -
          zeta ^ bitRev7 (2 ^ k + b) * g (b * (2 * 2 ^ (7 - k)) + r) := by
  have := (fipsNttStartLoop_spec (2 ^ (7 - k)) (2 ^ k) (by positivity) (layer_blocks hk) _ 0
    (2 ^ k) g rfl (Nat.zero_le _)).2.2 b r (Nat.zero_le _) hb hr
  simp only [zero_mul, Nat.sub_zero] at this
  exact this

theorem nttLayer_ge {k : ℕ} (hk : k < 7) (g : Poly) {p : ℕ} (hp : 256 ≤ p) :
    nttLayer k g p = g p := by
  have := (fipsNttStartLoop_spec (2 ^ (7 - k)) (2 ^ k) (by positivity) (layer_blocks hk) _ 0
    (2 ^ k) g rfl (Nat.zero_le _)).2.1 p (Or.inr hp)
  simp only [zero_mul] at this
  exact this

theorem nttLayer_snd {k : ℕ} (hk : k < 7) (g : Poly) (h : 0 < 2 ^ (7 - k)) :
    (fipsNttStartLoop (2 ^ (7 - k)) h 0 (2 ^ k) g).2 = 2 ^ (k + 1) := by
  have := (fipsNttStartLoop_spec (2 ^ (7 - k)) (2 ^ k) h (layer_blocks hk) _ 0
    (2 ^ k) g rfl (Nat.zero_le _)).1
  simp only [zero_mul, Nat.sub_zero] at this
  rw [this, pow_succ]; ring

theorem two_pow_le_pred {k : ℕ} : 2 ^ k ≤ 2 ^ (k + 1) - 1 := by
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [pow_succ]; omega

theorem invLayer_block {k : ℕ} (hk : k < 7) (g : Poly) {b r : ℕ} (hb : b < 2 ^ k)
    (hr : r < 2 * 2 ^ (7 - k)) :
    invLayer k g (b * (2 * 2 ^ (7 - k)) + r) =
      if r < 2 ^ (7 - k) then
        g (b * (2 * 2 ^ (7 - k)) + r) + g (b * (2 * 2 ^ (7 - k)) + r + 2 ^ (7 - k))
      else
        zeta ^ bitRev7 (2 ^ (k + 1) - 1 - b) *
          (g (b * (2 * 2 ^ (7 - k)) + r) - g (b * (2 * 2 ^ (7 - k)) + r - 2 ^ (7 - k))) := by
  have := (fipsInvStartLoop_spec (2 ^ (7 - k)) (2 ^ k) (by positivity) (layer_blocks hk) _ 0
    (2 ^ (k + 1) - 1) g rfl (Nat.zero_le _) (by simpa using two_pow_le_pred)).2.2 b r
    (Nat.zero_le _) hb hr
  simp only [zero_mul, Nat.sub_zero] at this
  exact this

theorem invLayer_ge {k : ℕ} (hk : k < 7) (g : Poly) {p : ℕ} (hp : 256 ≤ p) :
    invLayer k g p = g p := by
  have := (fipsInvStartLoop_spec (2 ^ (7 - k)) (2 ^ k) (by positivity) (layer_blocks hk) _ 0
    (2 ^ (k + 1) - 1) g rfl (Nat.zero_le _) (by simpa using two_pow_le_pred)).2.1 p (Or.inr hp)
  simp only [zero_mul] at this
  exact this

theorem invLayer_snd {k : ℕ} (hk : k < 7) (g : Poly) (h : 0 < 2 ^ (7 - k)) :
    (fipsInvStartLoop (2 ^ (7 - k)) h 0 (2 ^ (k + 1) - 1) g).2 = 2 ^ k - 1 := by
  have := (fipsInvStartLoop_spec (2 ^ (7 - k)) (2 ^ k) h (layer_blocks hk) _ 0
    (2 ^ (k + 1) - 1) g rfl (Nat.zero_le _) (by simpa using two_pow_le_pred)).1
  simp only [zero_mul, Nat.sub_zero] at this
  rw [this, pow_succ]; omega

/-! ## Index arithmetic inside a block -/

/-- Decomposition `p = b·(2m) + r` of an index below 256 into block and offset. -/
theorem layer_decomp {k : ℕ} (hk : k < 7) {p : ℕ} (hp : p < 256) :
    p / (2 * 2 ^ (7 - k)) < 2 ^ k ∧ p % (2 * 2 ^ (7 - k)) < 2 * 2 ^ (7 - k) ∧
      p = p / (2 * 2 ^ (7 - k)) * (2 * 2 ^ (7 - k)) + p % (2 * 2 ^ (7 - k)) := by
  refine ⟨Nat.div_lt_of_lt_mul ?_, Nat.mod_lt _ (by positivity), (Nat.div_add_mod' _ _).symm⟩
  rw [Nat.mul_comm, layer_blocks hk]; exact hp

theorem block_up (m p : ℕ) (hm : 0 < m) (h : p % (2 * m) < m) :
    (p + m) / (2 * m) = p / (2 * m) ∧ (p + m) % (2 * m) = p % (2 * m) + m := by
  have hd := Nat.div_add_mod p (2 * m)
  set q := p / (2 * m)
  set r := p % (2 * m)
  have e : p + m = 2 * m * q + (r + m) := by omega
  have h1 : (r + m) / (2 * m) = 0 := Nat.div_eq_of_lt (by omega)
  have h2 : (r + m) % (2 * m) = r + m := Nat.mod_eq_of_lt (by omega)
  rw [e, Nat.mul_add_div (by omega), Nat.mul_add_mod, h1, h2]
  simp

theorem block_down (m p : ℕ) (hm : 0 < m) (h : m ≤ p % (2 * m)) :
    (p - m) / (2 * m) = p / (2 * m) ∧ (p - m) % (2 * m) = p % (2 * m) - m := by
  have hd := Nat.div_add_mod p (2 * m)
  have hlt := Nat.mod_lt p (show 2 * m > 0 by omega)
  set q := p / (2 * m)
  set r := p % (2 * m)
  have e : p - m = 2 * m * q + (r - m) := by omega
  have h1 : (r - m) / (2 * m) = 0 := Nat.div_eq_of_lt (by omega)
  have h2 : (r - m) % (2 * m) = r - m := Nat.mod_eq_of_lt (by omega)
  rw [e, Nat.mul_add_div (by omega), Nat.mul_add_mod, h1, h2]
  simp

/-- `nttLayer` at an arbitrary index `p < 256`. -/
theorem nttLayer_apply {k : ℕ} (hk : k < 7) (g : Poly) {p : ℕ} (hp : p < 256) :
    nttLayer k g p =
      if p % (2 * 2 ^ (7 - k)) < 2 ^ (7 - k) then
        g p + zeta ^ bitRev7 (2 ^ k + p / (2 * 2 ^ (7 - k))) * g (p + 2 ^ (7 - k))
      else
        g (p - 2 ^ (7 - k)) - zeta ^ bitRev7 (2 ^ k + p / (2 * 2 ^ (7 - k))) * g p := by
  obtain ⟨hb, hr, he⟩ := layer_decomp hk hp
  conv_lhs => rw [he]
  rw [nttLayer_block hk g hb hr, ← he]

theorem invLayer_apply {k : ℕ} (hk : k < 7) (g : Poly) {p : ℕ} (hp : p < 256) :
    invLayer k g p =
      if p % (2 * 2 ^ (7 - k)) < 2 ^ (7 - k) then g p + g (p + 2 ^ (7 - k))
      else zeta ^ bitRev7 (2 ^ (k + 1) - 1 - p / (2 * 2 ^ (7 - k))) *
        (g p - g (p - 2 ^ (7 - k))) := by
  obtain ⟨hb, hr, he⟩ := layer_decomp hk hp
  conv_lhs => rw [he]
  rw [invLayer_block hk g hb hr, ← he]

/-- In the lower half of a block, `p + len` is still below 256. -/
theorem layer_up_lt {k : ℕ} (hk : k < 7) {p : ℕ} (hp : p < 256)
    (h : p % (2 * 2 ^ (7 - k)) < 2 ^ (7 - k)) : p + 2 ^ (7 - k) < 256 := by
  obtain ⟨hb, hr, he⟩ := layer_decomp hk hp
  have h1 := Nat.mul_le_mul_right (2 * 2 ^ (7 - k)) hb
  rw [layer_blocks hk, Nat.succ_mul] at h1
  generalize p / (2 * 2 ^ (7 - k)) = b at *
  generalize p % (2 * 2 ^ (7 - k)) = r at *
  generalize 2 ^ (7 - k) = M at *
  omega

/-- In the upper half of a block, `p ≥ len`. -/
theorem layer_down_le {k : ℕ} (hk : k < 7) {p : ℕ} (hp : p < 256)
    (h : ¬ p % (2 * 2 ^ (7 - k)) < 2 ^ (7 - k)) : 2 ^ (7 - k) ≤ p := by
  obtain ⟨-, -, he⟩ := layer_decomp hk hp
  generalize p / (2 * 2 ^ (7 - k)) = b at *
  generalize p % (2 * 2 ^ (7 - k)) = r at *
  generalize 2 ^ (7 - k) = M at *
  omega

/-! ## Congruence and linearity of the layers -/

theorem nttLayer_congr {k : ℕ} (hk : k < 7) {g h : Poly} (hgh : EqOn256 g h) :
    EqOn256 (nttLayer k g) (nttLayer k h) := by
  intro p hp
  rw [nttLayer_apply hk g hp, nttLayer_apply hk h hp]
  split_ifs with hr
  · rw [hgh p hp, hgh _ (layer_up_lt hk hp hr)]
  · rw [hgh p hp, hgh _ (lt_of_le_of_lt (Nat.sub_le _ _) hp)]

theorem invLayer_congr {k : ℕ} (hk : k < 7) {g h : Poly} (hgh : EqOn256 g h) :
    EqOn256 (invLayer k g) (invLayer k h) := by
  intro p hp
  rw [invLayer_apply hk g hp, invLayer_apply hk h hp]
  split_ifs with hr
  · rw [hgh p hp, hgh _ (layer_up_lt hk hp hr)]
  · rw [hgh p hp, hgh _ (lt_of_le_of_lt (Nat.sub_le _ _) hp)]

theorem nttLayer_smul {k : ℕ} (hk : k < 7) (c : Zq) (g : Poly) :
    EqOn256 (nttLayer k (fun p => c * g p)) (fun p => c * nttLayer k g p) := by
  intro p hp
  dsimp only
  rw [nttLayer_apply hk _ hp, nttLayer_apply hk g hp]
  split_ifs <;> ring

theorem invLayer_smul {k : ℕ} (hk : k < 7) (c : Zq) (g : Poly) :
    EqOn256 (invLayer k (fun p => c * g p)) (fun p => c * invLayer k g p) := by
  intro p hp
  dsimp only
  rw [invLayer_apply hk _ hp, invLayer_apply hk g hp]
  split_ifs <;> ring

/-! ## Each inverse layer undoes its forward layer (up to a factor 2) -/

set_option maxRecDepth 100000 in
/-- `ζ^BitRev7(2^(k+1)−1−b) · ζ^BitRev7(2^k+b) = −1`: the inverse layer's
    zeta is `−ζ⁻¹` of the forward layer's zeta for the same block. -/
theorem zeta_inv_check :
    ∀ k < 7, ∀ b < 2 ^ k, zeta ^ bitRev7 (2 ^ (k + 1) - 1 - b) * zeta ^ bitRev7 (2 ^ k + b) = -1 := by
  unfold zeta; decide +kernel

theorem invLayer_nttLayer {k : ℕ} (hk : k < 7) (g : Poly) :
    EqOn256 (invLayer k (nttLayer k g)) (fun p => 2 * g p) := by
  intro p hp
  obtain ⟨hb, hr2, -⟩ := layer_decomp hk hp
  have hz := zeta_inv_check k hk _ hb
  have hm : 0 < 2 ^ (7 - k) := by positivity
  rw [invLayer_apply hk _ hp]
  split_ifs with hr
  · obtain ⟨u1, u2⟩ := block_up _ p hm hr
    rw [nttLayer_apply hk g hp, nttLayer_apply hk g (layer_up_lt hk hp hr), u1, u2,
      ite_eq_left hr, ite_eq_right (by omega), Nat.add_sub_cancel]
    ring
  · have hle := layer_down_le hk hp hr
    obtain ⟨d1, d2⟩ := block_down _ p hm (by omega)
    rw [nttLayer_apply hk g hp, nttLayer_apply hk g (by omega), d1, d2,
      ite_eq_right hr, ite_eq_left (by omega), Nat.sub_add_cancel hle]
    linear_combination (-2 * g p) * hz

theorem nttLayer_invLayer {k : ℕ} (hk : k < 7) (g : Poly) :
    EqOn256 (nttLayer k (invLayer k g)) (fun p => 2 * g p) := by
  intro p hp
  obtain ⟨hb, hr2, -⟩ := layer_decomp hk hp
  have hz := zeta_inv_check k hk _ hb
  have hm : 0 < 2 ^ (7 - k) := by positivity
  rw [nttLayer_apply hk _ hp]
  split_ifs with hr
  · obtain ⟨u1, u2⟩ := block_up _ p hm hr
    rw [invLayer_apply hk g hp, invLayer_apply hk g (layer_up_lt hk hp hr), u1, u2,
      ite_eq_left hr, ite_eq_right (by omega), Nat.add_sub_cancel]
    linear_combination (g (p + 2 ^ (7 - k)) - g p) * hz
  · have hle := layer_down_le hk hp hr
    obtain ⟨d1, d2⟩ := block_down _ p hm (by omega)
    rw [invLayer_apply hk g hp, invLayer_apply hk g (by omega), d1, d2,
      ite_eq_right hr, ite_eq_left (by omega), Nat.sub_add_cancel hle]
    linear_combination (g (p - 2 ^ (7 - k)) - g p) * hz

/-! ## Algorithms 9 and 10 as compositions of layers -/

/-- Layers `0, …, n−1` of Algorithm 9, applied in that order. -/
def nttLayers (n : ℕ) (f : Poly) : Poly := (List.range n).foldl (fun g k => nttLayer k g) f

/-- Layers `n−1, …, 0` of Algorithm 10, applied in that order. -/
def invLayers (n : ℕ) (f : Poly) : Poly := (List.range n).foldr (fun k g => invLayer k g) f

theorem nttLayers_succ (n : ℕ) (f : Poly) : nttLayers (n + 1) f = nttLayer n (nttLayers n f) := by
  simp [nttLayers, List.range_succ, List.foldl_append]

theorem invLayers_succ (n : ℕ) (f : Poly) : invLayers (n + 1) f = invLayers n (invLayer n f) := by
  simp [invLayers, List.range_succ, List.foldr_append]

theorem fipsNttLenLoop_eq : ∀ j k (g : Poly), 7 - k = j → k ≤ 7 →
    fipsNttLenLoop (2 ^ (7 - k)) (2 ^ k) g =
      (List.range' k (7 - k)).foldl (fun g k => nttLayer k g) g := by
  intro j
  induction j with
  | zero =>
    intro k g hj hk
    rw [fipsNttLenLoop, dite_eq_right (by rw [hj]; norm_num), hj]
    rfl
  | succ j ih =>
    intro k g hj hk
    have hk7 : k < 7 := by omega
    have hge : 2 ^ (7 - k) ≥ 2 := by
      rw [show 7 - k = (6 - k) + 1 by omega, pow_succ]
      have : 1 ≤ 2 ^ (6 - k) := Nat.one_le_two_pow
      omega
    rw [fipsNttLenLoop, dite_eq_left hge]
    simp only
    rw [nttLayer_snd hk7 g]
    have hdiv : 2 ^ (7 - k) / 2 = 2 ^ (7 - (k + 1)) := by
      rw [show 7 - k = (7 - (k + 1)) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    rw [hdiv]
    change fipsNttLenLoop (2 ^ (7 - (k + 1))) (2 ^ (k + 1)) (nttLayer k g) = _
    rw [ih (k + 1) (nttLayer k g) (by omega) (by omega),
      show 7 - k = (7 - (k + 1)) + 1 by omega, List.range'_succ, List.foldl_cons]

/-- Algorithm 9 is the composition of its seven layers. -/
theorem fipsNtt_eq_layers (f : Poly) : fipsNtt f = nttLayers 7 f := by
  have := fipsNttLenLoop_eq 7 0 f rfl (by norm_num)
  simp only [Nat.sub_zero, pow_zero] at this
  rw [fipsNtt, show (128 : ℕ) = 2 ^ 7 by norm_num, this, nttLayers, List.range_eq_range']

theorem fipsInvLenLoop_eq : ∀ n len (h : 0 < len) (g : Poly), len = 2 ^ (8 - n) → n ≤ 7 →
    fipsInvLenLoop len h (2 ^ n - 1) g = invLayers n g := by
  intro n
  induction n with
  | zero =>
    intro len h g hlen _
    rw [fipsInvLenLoop, ite_eq_right (by rw [hlen]; norm_num)]
    rfl
  | succ n ih =>
    intro len h g hlen hn
    have hn7 : n < 7 := by omega
    have hlen' : len = 2 ^ (7 - n) := by rw [hlen, show 8 - (n + 1) = 7 - n by omega]
    have hle : len ≤ 128 := by
      rw [hlen', show (128 : ℕ) = 2 ^ 7 by norm_num]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [fipsInvLenLoop, ite_eq_left hle]
    simp only
    subst hlen'
    rw [invLayer_snd hn7 g]
    change fipsInvLenLoop (2 * 2 ^ (7 - n)) _ (2 ^ n - 1) (invLayer n g) = _
    rw [ih (2 * 2 ^ (7 - n)) _ (invLayer n g) (by
      rw [← pow_succ']; congr 1; omega) (by omega), invLayers_succ]

/-- Algorithm 10 is the composition of its seven layers followed by the
    scaling by `3303 = 128⁻¹`. -/
theorem fipsNttInv_eq_layers (f : Poly) : fipsNttInv f = fun p => invLayers 7 f p * 3303 := by
  unfold fipsNttInv
  dsimp only
  rw [show (127 : ℕ) = 2 ^ 7 - 1 by norm_num, fipsInvLenLoop_eq 7 2 _ f (by norm_num) le_rfl]

/-! ## Inverse theorems -/

theorem invLayers_congr {n : ℕ} (hn : n ≤ 7) {g h : Poly} (hgh : EqOn256 g h) :
    EqOn256 (invLayers n g) (invLayers n h) := by
  induction n generalizing g h with
  | zero => exact hgh
  | succ n ih =>
    rw [invLayers_succ, invLayers_succ]
    exact ih (by omega) (invLayer_congr (by omega) hgh)

theorem invLayers_smul {n : ℕ} (hn : n ≤ 7) (c : Zq) (g : Poly) :
    EqOn256 (invLayers n (fun p => c * g p)) (fun p => c * invLayers n g p) := by
  induction n generalizing g with
  | zero => intro p _; rfl
  | succ n ih =>
    intro p hp
    rw [invLayers_succ, invLayers_succ,
      invLayers_congr (by omega) (invLayer_smul (by omega) c g) p hp]
    exact ih (by omega) _ p hp

theorem nttLayers_congr {n : ℕ} (hn : n ≤ 7) {g h : Poly} (hgh : EqOn256 g h) :
    EqOn256 (nttLayers n g) (nttLayers n h) := by
  induction n with
  | zero => exact hgh
  | succ n ih =>
    rw [nttLayers_succ, nttLayers_succ]
    exact nttLayer_congr (by omega) (ih (by omega))

theorem nttLayers_smul {n : ℕ} (hn : n ≤ 7) (c : Zq) (g : Poly) :
    EqOn256 (nttLayers n (fun p => c * g p)) (fun p => c * nttLayers n g p) := by
  induction n with
  | zero => intro p _; rfl
  | succ n ih =>
    intro p hp
    rw [nttLayers_succ, nttLayers_succ, nttLayer_congr (by omega) (ih (by omega)) p hp]
    exact nttLayer_smul (by omega) c _ p hp

theorem invLayers_nttLayers {n : ℕ} (hn : n ≤ 7) (f : Poly) :
    EqOn256 (invLayers n (nttLayers n f)) (fun p => 2 ^ n * f p) := by
  induction n with
  | zero => intro p _; simp [invLayers, nttLayers]
  | succ n ih =>
    intro p hp
    rw [nttLayers_succ, invLayers_succ,
      invLayers_congr (by omega) (invLayer_nttLayer (by omega) _) p hp,
      invLayers_smul (by omega) 2 _ p hp]
    dsimp only
    rw [ih (by omega) p hp]
    ring

theorem nttLayers_invLayers {n : ℕ} (hn : n ≤ 7) (g : Poly) :
    EqOn256 (nttLayers n (invLayers n g)) (fun p => 2 ^ n * g p) := by
  induction n generalizing g with
  | zero => intro p _; simp [invLayers, nttLayers]
  | succ n ih =>
    intro p hp
    rw [invLayers_succ, nttLayers_succ,
      nttLayer_congr (by omega) (ih (by omega) (invLayer n g)) p hp,
      nttLayer_smul (by omega) _ _ p hp]
    dsimp only
    rw [nttLayer_invLayer (show n < 7 by omega) g p hp]
    ring

/-- `NTT⁻¹(NTT(f)) = f` (FIPS 203 Algorithms 9 and 10). -/
theorem fipsNttInv_fipsNtt (f : Poly) : EqOn256 (fipsNttInv (fipsNtt f)) f := by
  intro p hp
  rw [fipsNttInv_eq_layers, fipsNtt_eq_layers]
  dsimp only
  rw [invLayers_nttLayers le_rfl f p hp]
  linear_combination (f p) * inv128

/-- `NTT(NTT⁻¹(f̂)) = f̂` (FIPS 203 Algorithms 9 and 10). -/
theorem fipsNtt_fipsNttInv (g : Poly) : EqOn256 (fipsNtt (fipsNttInv g)) g := by
  intro p hp
  rw [fipsNttInv_eq_layers, fipsNtt_eq_layers,
    show (fun p => invLayers 7 g p * 3303) = (fun p => 3303 * invLayers 7 g p) by
      funext p; ring,
    nttLayers_smul le_rfl _ _ p hp]
  dsimp only
  rw [nttLayers_invLayers le_rfl g p hp]
  linear_combination (g p) * inv128

theorem fipsNtt_congr {f g : Poly} (h : EqOn256 f g) : EqOn256 (fipsNtt f) (fipsNtt g) := by
  rw [fipsNtt_eq_layers, fipsNtt_eq_layers]; exact nttLayers_congr le_rfl h

theorem fipsNttInv_congr {f g : Poly} (h : EqOn256 f g) :
    EqOn256 (fipsNttInv f) (fipsNttInv g) := by
  intro p hp
  rw [fipsNttInv_eq_layers, fipsNttInv_eq_layers]
  dsimp only
  rw [invLayers_congr le_rfl h p hp]

end OcamlPq.MLKEM
