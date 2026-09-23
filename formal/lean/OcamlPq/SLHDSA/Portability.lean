import OcamlPq.SLHDSA.Params

/-!
# SLH-DSA: portability of the `int` intermediates

Every OCaml `int` computed by `slhdsa_engine.ml` other than the FORS
accumulator `total` (which wraps and is handled in `Base2b.lean`) is
non-negative and below `2^30`, hence `Portable`: its value is the same on
63-bit native, 32-bit `js_of_ocaml` and 31-bit native/wasm `int`s, and every
value passed to `set_u32_be` is in `[0, 2^32)`. The layer and type written
by `address_compressed` (`Char.unsafe_chr`) are below 256.

The theorems bound each intermediate in terms of the parameters (valid for
every value the code can reach, by the loop ranges quoted), and the
per-set constants are checked for all twelve parameter sets.
-/

namespace OcamlPq.SLHDSA.Portability

/-- The per-set constants that bound every `int` of the engine. -/
theorem param_bounds : ∀ P ∈ allParams,
    P.k * 2 ^ P.a ≤ 2 ^ 19 ∧ 2 ^ P.a ≤ 2 ^ 14 ∧ 2 ^ P.treeHeight ≤ 2 ^ 9 ∧
      P.signatureSize < 2 ^ 16 ∧ P.len ≤ 67 ∧ P.d ≤ 22 ∧ P.m ≤ 49 ∧ P.a ≤ 14 ∧
      P.treeHeight ≤ 9 ∧ P.n ≤ 32 ∧ P.treeHeight * P.n ≤ 2 ^ 9 ∧ P.a * P.n ≤ 2 ^ 9 ∧
      P.len * P.n ≤ 2 ^ 12 ∧ 1 ≤ P.a ∧ 1 ≤ P.treeHeight := by
  decide +kernel

/-- FORS tree indices (`fors_sign`/`fors_public_key_from_signature`,
    `treehash`, `compute_root`, lines 342–367, 375–388, 422–459): for
    `tree < k` and local index `i < 2^a`, the values
    `index_offset = tree lsl a`, `selected = indices.(tree) + index_offset`,
    `index + index_offset`, and `(i lsr t) + (index_offset lsr t)` (for
    every shift `t`) are all below `k·2^a ≤ 2^19`. -/
theorem fors_indices (P : Params) (hP : P ∈ allParams) (tree i t : ℕ) (htree : tree < P.k)
    (hi : i < 2 ^ P.a) :
    tree * 2 ^ P.a < 2 ^ 30 ∧ i + tree * 2 ^ P.a < 2 ^ 30 ∧
      (i >>> t) + ((tree * 2 ^ P.a) >>> t) < 2 ^ 30 := by
  obtain ⟨hk, -⟩ := param_bounds P hP
  have h1 : i + tree * 2 ^ P.a < P.k * 2 ^ P.a := by
    have : (tree + 1) * 2 ^ P.a ≤ P.k * 2 ^ P.a := Nat.mul_le_mul_right _ htree
    nlinarith
  have h2 : (i >>> t) + ((tree * 2 ^ P.a) >>> t) ≤ i + tree * 2 ^ P.a :=
    Nat.add_le_add (Nat.shiftRight_le _ _) (Nat.shiftRight_le _ _)
  refine ⟨by omega, by omega, by omega⟩

/-- XMSS indices (`merkle_sign`, `merkle_root`, `verify_formatted`,
    `split_message_digest`): leaf indices, keypair addresses and tree indices
    `(i lsr t)` are below `2^h′ ≤ 2^9`; `1 lsl height` is at most `2^14`. -/
theorem xmss_indices (P : Params) (hP : P ∈ allParams) (i t : ℕ) (hi : i < 2 ^ P.treeHeight) :
    i < 2 ^ 30 ∧ i >>> t < 2 ^ 30 ∧ 2 ^ P.treeHeight < 2 ^ 30 ∧ 2 ^ P.a < 2 ^ 30 := by
  obtain ⟨-, ha, hh, -⟩ := param_bounds P hP
  have := Nat.shiftRight_le i t
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- `treehash` bookkeeping: heights and `field1 = node_height + 1` are at
    most `height ≤ 14`, `offset ≤ height + 1`, and the blit offsets
    `heights.(…) * P.n ≤ height·n ≤ 2^9`. -/
theorem treehash_ints (P : Params) (hP : P ∈ allParams) (height z : ℕ)
    (hheight : height = P.a ∨ height = P.treeHeight) (hz : z ≤ height) :
    z + 1 < 2 ^ 30 ∧ z * P.n ≤ 2 ^ 9 ∧ height * P.n ≤ 2 ^ 9 := by
  obtain ⟨-, -, -, -, -, -, -, ha, hh, -, hhn, han, -⟩ := param_bounds P hP
  have hn := Nat.mul_le_mul_right P.n hz
  rcases hheight with rfl | rfl <;> refine ⟨by omega, by omega, by omega⟩

/-- WOTS+: chain addresses `index < len ≤ 67`, hash addresses
    `position ≤ 15`, chain lengths `≤ 15`, the checksum
    `Σ (15 − digit) ≤ 15·2n ≤ 960` and `checksum lsl 4 ≤ 15360`, the nibble
    index `index / 2 < n`, and the signature offsets `index * n < len·n`. -/
theorem wots_ints (P : Params) (hP : P ∈ allParams) (index csum : ℕ) (hi : index < P.len)
    (hc : csum ≤ 15 * (2 * P.n)) :
    index < 2 ^ 30 ∧ csum * 2 ^ 4 < 2 ^ 30 ∧ index * P.n < 2 ^ 30 := by
  obtain ⟨-, -, -, -, hl, -, -, -, -, hn, -, -, hln, -⟩ := param_bounds P hP
  have := Nat.mul_le_mul_right P.n hi.le
  refine ⟨by omega, by omega, by omega⟩

/-- `message_to_fors_indices` bookkeeping: `!input ≤ ⌈k·a/8⌉ ≤ m`,
    `!bits < a + 8`, and `mask = (1 lsl a) − 1` are small. -/
theorem fors_loop_ints (P : Params) (hP : P ∈ allParams) (inp bits : ℕ)
    (hinp : inp ≤ P.forsMessageBytes) (hbits : bits < P.a + 8) :
    inp < 2 ^ 30 ∧ bits < 2 ^ 30 ∧ 2 ^ P.a - 1 < 2 ^ 30 := by
  obtain ⟨-, ha, -, -, -, -, hm, ha14, -⟩ := param_bounds P hP
  have hfm := (initChecks_all P hP).2.1
  refine ⟨by omega, by omega, by omega⟩

/-- Byte positions of `verify_formatted` and `fors_public_key_from_signature`
    never exceed `signature_size < 2^16`. -/
theorem position_ints (P : Params) (hP : P ∈ allParams) (pos : ℕ) (hpos : pos ≤ P.signatureSize) :
    pos < 2 ^ 30 := by
  obtain ⟨-, -, -, hs, -⟩ := param_bounds P hP
  omega

/-- Every value written by `set_u32_be` (layer `< d`, type `≤ 6`, keypair
    `< 2^h′`, `field1 ≤ max(len − 1, a, h′)`, `field2 < max(16, k·2^a,
    2^h′)`) is in `[0, 2^32)`; the layer and the type are below 256, as
    `address_compressed` requires. -/
theorem address_fields (P : Params) (hP : P ∈ allParams) (layer typ keypair f1 f2 : ℕ)
    (hl : layer < P.d) (ht : typ ≤ 6) (hk : keypair < 2 ^ P.treeHeight)
    (hf1 : f1 ≤ P.len ∨ f1 ≤ P.a ∨ f1 ≤ P.treeHeight)
    (hf2 : f2 < 16 ∨ f2 < P.k * 2 ^ P.a ∨ f2 < 2 ^ P.treeHeight) :
    layer < 256 ∧ typ < 256 ∧ layer < 2 ^ 32 ∧ typ < 2 ^ 32 ∧ keypair < 2 ^ 32 ∧
      f1 < 2 ^ 32 ∧ f2 < 2 ^ 32 := by
  obtain ⟨hka, -, hh, -, hlen, hd, -, ha, hth, -⟩ := param_bounds P hP
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- All of the above are `Portable`. -/
theorem portable_of_lt {x : ℕ} (h : x < 2 ^ 30) : Portable (x : ℤ) := Portable.of_nat_lt h

end OcamlPq.SLHDSA.Portability
