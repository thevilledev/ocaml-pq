import OcamlPq.Hash.SpongeSqueeze

/-!
# `sponge`, SHA3-256, SHA3-512, SHAKE128, SHAKE256 are FIPS 202

Main results (all for every input byte string `M`):

* `spongeWith_eq_of`: `lib/keccak.ml` `sponge_with ~permute ~rate ~suffix
  ~output_length` is FIPS 202 `SPONGE[f, pad10*1, 8·rate](M ‖ ds,
  8·output_length)` for the function `f` that `permute` computes
  (`Implements`), whenever `0 < rate`, `8 ∣ rate`, `rate ≤ 200` and the suffix
  byte encodes `ds` (`SuffixOK`), for every content of the uninitialised
  `Bytes.create` buffers. `spongeWith_eq` is the case of `permute`, with
  `f = KECCAK-f[1600]`.
* `sha3_256_eq`, `sha3_512_eq`, `shake128_eq`, `shake256_eq`: the four
  entry points equal FIPS 202 §6.1/§6.2 on the bit strings of their inputs.
* `rates`: the rates 168/136/72 are `(1600 − 2·{128, 256, 512}) / 8`.
* `shake128_prefix`, `shake256_prefix`: output of length `L` is a prefix of
  output of length `L′ ≥ L`.
* `sponge_final_state`: the squeeze loop applies the permutation exactly
  `⌈output_length / rate⌉ − 1` times (0 when `output_length = 0`).
* `fips202Shake128_neg` etc.: `Mlkem.Fips202` rejects negative lengths.
-/

namespace OcamlPq.Hash.Keccak

open FIPS202

/-- The model's output: length `L`, byte `k` is `outByte`. -/
theorem spongeWith_get (perm : Array (BitVec 64) → Array (BitVec 64)) (r suffix L : ℕ) (hr : 0 < r)
    (hr8 : r % 8 = 0) (oj : List UInt8) (bj : ℕ → List UInt8) (hoj : oj.length = L)
    (hbj : ∀ p, (bj p).length = r) (M : List UInt8) :
    (spongeWith perm r suffix L oj bj M).length = L ∧
    ∀ k < L, (spongeWith perm r suffix L oj bj M)[k]! = outByte perm (absorb perm r suffix M) r k := by
  show (squeezeLoop perm r L bj (L + 1) (absorb perm r suffix M) oj 0).2.1.length = L ∧
    ∀ k < L, (squeezeLoop perm r L bj (L + 1) (absorb perm r suffix M) oj 0).2.1[k]! =
      outByte perm (absorb perm r suffix M) r k
  by_cases hL : L = 0
  · subst hL
    rw [squeezeLoop_done]
    exact ⟨hoj, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · have h := squeezeLoop_spec perm r L hr hr8 bj hbj (absorb perm r suffix M) (L + 1) 0 oj
      (by simp; omega) (by omega) hoj (by simp)
    rw [Function.iterate_zero_apply, Nat.zero_mul] at h
    exact ⟨h.2.1, h.2.2.1⟩

/-- **Permutation count.** The squeeze loop leaves the state at
`perm^[(L − 1) / rate]` of the absorbed state: one `perm` between
consecutive output blocks and none after the last (and none at all for
`L = 0`, where `(0 − 1) / rate = 0`). -/
theorem sponge_final_state (perm : Array (BitVec 64) → Array (BitVec 64)) (r suffix L : ℕ)
    (hr : 0 < r) (hr8 : r % 8 = 0) (oj : List UInt8) (bj : ℕ → List UInt8) (hoj : oj.length = L)
    (hbj : ∀ p, (bj p).length = r) (M : List UInt8) :
    (squeezeLoop perm r L bj (L + 1) (absorb perm r suffix M) oj 0).1 =
      perm^[(L - 1) / r] (absorb perm r suffix M) := by
  by_cases hL : L = 0
  · subst hL
    rw [squeezeLoop_done, show (0 - 1) / r = 0 by simp, Function.iterate_zero_apply]
  · have h := squeezeLoop_spec perm r L hr hr8 bj hbj (absorb perm r suffix M) (L + 1) 0 oj
      (by simp; omega) (by omega) hoj (by simp)
    rw [Function.iterate_zero_apply, Nat.zero_mul] at h
    exact h.2.2.2

theorem laneBits_getElem (a : Array (BitVec 64)) (k : ℕ) (hk : k < (laneBits a).length) :
    (laneBits a)[k] = (a[k / 64]!).getLsbD (k % 64) := by
  simp only [laneBits, List.getElem_ofFn]

/-- Bit `t mod 8` of output byte `t / 8` is bit `t` of FIPS 202's `Z`. -/
theorem outByte_bit {perm : Array (BitVec 64) → Array (BitVec 64)} {f : Bits → Bits}
    (hp : Implements perm f) (a0 : Array (BitVec 64)) (ha : a0.size = 25) (r : ℕ) (hr : 0 < r)
    (hr200 : r ≤ 200) (t : ℕ) :
    (outByte perm a0 r (t / 8)).toNat.testBit (t % 8) = Zbit f (8 * r) (laneBits a0) t := by
  have hdm := Nat.div_add_mod t (8 * r)
  have hs : t % (8 * r) < 8 * r := Nat.mod_lt _ (by omega)
  set q := t / (8 * r)
  set s := t % (8 * r)
  have ht : t = 8 * (r * q) + s := by rw [← hdm]; ring
  have h1 : t / 8 = r * q + s / 8 := by omega
  have h2 : (t / 8) / r = q := Nat.div_eq_of_lt_le (by rw [h1, Nat.mul_comm]; omega)
    (by rw [h1, Nat.add_mul, Nat.mul_comm]; omega)
  have h3 : (t / 8) % r = s / 8 := by
    have := Nat.div_add_mod (t / 8) r
    rw [h2] at this; omega
  rw [outByte, h2, h3, blockByte, testBit_byteOfInt64 _ _ _ (Nat.mod_lt _ (by norm_num)), Zbit,
    ← (hp.iterate a0 ha q).2, List.getD_eq_getElem _ _ (by rw [laneBits_length]; omega),
    laneBits_getElem]
  have h4 : s / 8 / 8 = s / 64 := by omega
  have h5 : 8 * (s / 8 % 8) + t % 8 = s % 64 := by omega
  rw [h4, h5]

/-- **`sponge_with` is the FIPS 202 sponge.** For every permutation `perm`
that computes a function `f` on FIPS 202 strings and every input `M`, the bit
string of `sponge_with ~permute:perm ~rate ~suffix ~output_length M` is
`SPONGE[f, pad10*1, 8·rate](M ‖ ds, 8·output_length)`, whatever the initial
contents of the `Bytes.create` buffers. -/
theorem spongeWith_eq_of {perm : Array (BitVec 64) → Array (BitVec 64)} {f : Bits → Bits}
    (hp : Implements perm f) (r suffix L : ℕ) (ds : Bits) (hr : 0 < r) (hr8 : r % 8 = 0)
    (hr200 : r ≤ 200) (hs : SuffixOK suffix ds) (oj : List UInt8) (bj : ℕ → List UInt8)
    (hoj : oj.length = L) (hbj : ∀ p, (bj p).length = r) (M : List UInt8) :
    bytesToBits (spongeWith perm r suffix L oj bj M) =
      FIPS202.sponge f pad101 (8 * r) (bytesToBits M ++ ds) (8 * L) := by
  obtain ⟨hsz, habs⟩ := absorb_spec hp r suffix ds M hr hr8 hr200 hs
  have hsq := squeeze_spec f (8 * r) (8 * L) (laneBits (absorb perm r suffix M))
    (fun m => by rw [← (hp.iterate _ hsz m).2, laneBits_length]; omega)
    (8 * L + 1) 0 [] (by simp) (by simp) (Or.inl rfl) (by nlinarith)
  rw [Function.iterate_zero_apply] at hsq
  show _ = squeeze f (8 * r) (8 * L) (8 * L + 1)
    ((List.range ((padded r M ds).length / (8 * r))).foldl
        (fun S i => f (xorBits S (((padded r M ds).drop (i * (8 * r))).take (8 * r) ++
          List.replicate (b - 8 * r) false)))
        (List.replicate b false)) []
  rw [← habs, hsq]
  obtain ⟨hlen, hget⟩ := spongeWith_get perm r suffix L hr hr8 oj bj hoj hbj M
  apply List.ext_getElem (by simp [hlen])
  intro t h1 h2
  have ht : t < 8 * L := by simpa using h2
  rw [bytesToBits_getElem, List.getElem_ofFn,
    ← getElem!_pos (spongeWith perm r suffix L oj bj M) (t / 8) (by rw [hlen]; omega),
    hget _ (by omega), outByte_bit hp _ hsz r hr hr200 t]

/-- **`sponge` is the FIPS 202 sponge.** For every input `M`, the bit string
of `sponge ~rate ~suffix ~output_length M` is
`SPONGE[KECCAK-f[1600], pad10*1, 8·rate](M ‖ ds, 8·output_length)`, whatever the
initial contents of the `Bytes.create` buffers. -/
theorem spongeWith_eq (r suffix L : ℕ) (ds : Bits) (hr : 0 < r) (hr8 : r % 8 = 0)
    (hr200 : r ≤ 200) (hs : SuffixOK suffix ds) (oj : List UInt8) (bj : ℕ → List UInt8)
    (hoj : oj.length = L) (hbj : ∀ p, (bj p).length = r) (M : List UInt8) :
    bytesToBits (spongeWith permute r suffix L oj bj M) =
      FIPS202.sponge KeccakF pad101 (8 * r) (bytesToBits M ++ ds) (8 * L) :=
  spongeWith_eq_of permute_implements r suffix L ds hr hr8 hr200 hs oj bj hoj hbj M

/-- The result of `sponge_with` does not depend on the unspecified initial
contents of `Bytes.create`. -/
theorem spongeWith_eq_spongeZ (perm : Array (BitVec 64) → Array (BitVec 64)) (r suffix L : ℕ)
    (hr : 0 < r) (hr8 : r % 8 = 0) (oj : List UInt8) (bj : ℕ → List UInt8) (hoj : oj.length = L)
    (hbj : ∀ p, (bj p).length = r) (M : List UInt8) :
    spongeWith perm r suffix L oj bj M = spongeZ perm r suffix L M := by
  obtain ⟨h1, h2⟩ := spongeWith_get perm r suffix L hr hr8 oj bj hoj hbj M
  obtain ⟨h3, h4⟩ := spongeWith_get perm r suffix L hr hr8 _ _ (List.length_replicate ..)
    (fun _ => List.length_replicate ..) M
  apply List.ext_getElem (by rw [h1, spongeZ, h3])
  intro k hk1 hk2
  rw [← getElem!_pos _ k hk1, ← getElem!_pos _ k hk2, h2 k (by omega), spongeZ, h4 k (by omega)]

/-- The result of `sponge` does not depend on the unspecified initial contents
of `Bytes.create`. -/
theorem spongeWith_eq_sponge (r suffix L : ℕ) (hr : 0 < r) (hr8 : r % 8 = 0) (oj : List UInt8)
    (bj : ℕ → List UInt8) (hoj : oj.length = L) (hbj : ∀ p, (bj p).length = r) (M : List UInt8) :
    spongeWith permute r suffix L oj bj M = sponge r suffix L M :=
  spongeWith_eq_spongeZ permute r suffix L hr hr8 oj bj hoj hbj M

/-! ## The four FIPS 202 functions -/

/-- The rates are `(1600 − 2·{128, 256, 512}) / 8` bytes (FIPS 202 §6: capacity
`c = 2·security`). -/
theorem rates : 8 * 168 = 1600 - 2 * 128 ∧ 8 * 136 = 1600 - 2 * 256 ∧ 8 * 72 = 1600 - 2 * 512 := by
  decide

/-- **SHA3-256.** `Keccak.sha3_256 M` is FIPS 202 `SHA3-256(M)`. -/
theorem sha3_256_eq (M : List UInt8) : bytesToBits (sha3_256 M) = SHA3_256 (bytesToBits M) :=
  spongeWith_eq 136 6 32 [false, true] (by norm_num) (by norm_num) (by norm_num) suffixOK_sha3
    _ _ (List.length_replicate ..) (fun _ => List.length_replicate ..) M

/-- **SHA3-512.** `Keccak.sha3_512 M` is FIPS 202 `SHA3-512(M)`. -/
theorem sha3_512_eq (M : List UInt8) : bytesToBits (sha3_512 M) = SHA3_512 (bytesToBits M) :=
  spongeWith_eq 72 6 64 [false, true] (by norm_num) (by norm_num) (by norm_num) suffixOK_sha3
    _ _ (List.length_replicate ..) (fun _ => List.length_replicate ..) M

/-- **SHAKE128.** `Keccak.shake128 ~output_length:L M` is FIPS 202
`SHAKE128(M, 8L)`, for every `L ≥ 0`. -/
theorem shake128_eq (L : ℕ) (M : List UInt8) :
    bytesToBits (shake128 L M) = SHAKE128 (bytesToBits M) (8 * L) :=
  spongeWith_eq 168 0x1f L [true, true, true, true] (by norm_num) (by norm_num) (by norm_num)
    suffixOK_shake _ _ (List.length_replicate ..) (fun _ => List.length_replicate ..) M

/-- **SHAKE256.** `Keccak.shake256 ~output_length:L M` is FIPS 202
`SHAKE256(M, 8L)`, for every `L ≥ 0`. -/
theorem shake256_eq (L : ℕ) (M : List UInt8) :
    bytesToBits (shake256 L M) = SHAKE256 (bytesToBits M) (8 * L) :=
  spongeWith_eq 136 0x1f L [true, true, true, true] (by norm_num) (by norm_num) (by norm_num)
    suffixOK_shake _ _ (List.length_replicate ..) (fun _ => List.length_replicate ..) M

theorem shake128_length (L : ℕ) (M : List UInt8) : (shake128 L M).length = L :=
  (spongeWith_get permute 168 0x1f L (by norm_num) (by norm_num) _ _ (List.length_replicate ..)
    (fun _ => List.length_replicate ..) M).1

theorem shake256_length (L : ℕ) (M : List UInt8) : (shake256 L M).length = L :=
  (spongeWith_get permute 136 0x1f L (by norm_num) (by norm_num) _ _ (List.length_replicate ..)
    (fun _ => List.length_replicate ..) M).1

theorem spongeZ_get (perm : Array (BitVec 64) → Array (BitVec 64)) (r suffix L : ℕ) (hr : 0 < r)
    (hr8 : r % 8 = 0) (M : List UInt8) :
    (spongeZ perm r suffix L M).length = L ∧
    ∀ k < L, (spongeZ perm r suffix L M)[k]! = outByte perm (absorb perm r suffix M) r k :=
  spongeWith_get perm r suffix L hr hr8 _ _ (List.length_replicate ..)
    (fun _ => List.length_replicate ..) M

theorem sponge_get (r suffix L : ℕ) (hr : 0 < r) (hr8 : r % 8 = 0) (M : List UInt8) :
    (sponge r suffix L M).length = L ∧
    ∀ k < L, (sponge r suffix L M)[k]! = outByte permute (absorb permute r suffix M) r k :=
  spongeZ_get permute r suffix L hr hr8 M

/-- **Prefix consistency** of `sponge_with`, for every permutation. -/
theorem spongeZ_prefix (perm : Array (BitVec 64) → Array (BitVec 64)) (r suffix : ℕ) (hr : 0 < r)
    (hr8 : r % 8 = 0) (L L' : ℕ) (h : L ≤ L') (M : List UInt8) :
    spongeZ perm r suffix L M = (spongeZ perm r suffix L' M).take L := by
  obtain ⟨h1, h2⟩ := spongeZ_get perm r suffix L hr hr8 M
  obtain ⟨h3, h4⟩ := spongeZ_get perm r suffix L' hr hr8 M
  apply List.ext_getElem (by rw [h1, List.length_take, h3]; omega)
  intro k hk1 hk2
  have hk : k < L := by rw [h1] at hk1; exact hk1
  rw [List.getElem_take, ← getElem!_pos _ k hk1, h2 k hk,
    ← getElem!_pos _ k (by rw [h3]; omega), h4 k (by omega)]

theorem sponge_prefix (r suffix : ℕ) (hr : 0 < r) (hr8 : r % 8 = 0) (L L' : ℕ) (h : L ≤ L')
    (M : List UInt8) : sponge r suffix L M = (sponge r suffix L' M).take L :=
  spongeZ_prefix permute r suffix hr hr8 L L' h M

/-- **Prefix consistency.** `shake128 ~output_length:L x` is a prefix of
`shake128 ~output_length:L′ x` whenever `L ≤ L′`. -/
theorem shake128_prefix (L L' : ℕ) (h : L ≤ L') (M : List UInt8) :
    shake128 L M = (shake128 L' M).take L :=
  sponge_prefix 168 0x1f (by norm_num) (by norm_num) L L' h M

/-- **Prefix consistency.** `shake256 ~output_length:L x` is a prefix of
`shake256 ~output_length:L′ x` whenever `L ≤ L′`. -/
theorem shake256_prefix (L L' : ℕ) (h : L ≤ L') (M : List UInt8) :
    shake256 L M = (shake256 L' M).take L :=
  sponge_prefix 136 0x1f (by norm_num) (by norm_num) L L' h M

/-! ## `Mlkem.Fips202` (`lib/mlkem.ml` lines 5–17) -/

/-- `Mlkem.Fips202.shake128`, `lib/mlkem.ml` lines 8–11; `invalid_arg` is
`Except.error`. `output_length` is an OCaml `int`, so it is an integer here. -/
def fips202Shake128 (outputLength : ℤ) (input : List UInt8) : Except String (List UInt8) :=
  if outputLength < 0 then .error "Mlkem.Fips202.shake128: negative output length"
  else .ok (shake128 outputLength.toNat input)

/-- `Mlkem.Fips202.shake256`, `lib/mlkem.ml` lines 13–16. -/
def fips202Shake256 (outputLength : ℤ) (input : List UInt8) : Except String (List UInt8) :=
  if outputLength < 0 then .error "Mlkem.Fips202.shake256: negative output length"
  else .ok (shake256 outputLength.toNat input)

theorem fips202Shake128_neg (L : ℤ) (hL : L < 0) (M : List UInt8) :
    fips202Shake128 L M = .error "Mlkem.Fips202.shake128: negative output length" := by
  simp [fips202Shake128, hL]

theorem fips202Shake256_neg (L : ℤ) (hL : L < 0) (M : List UInt8) :
    fips202Shake256 L M = .error "Mlkem.Fips202.shake256: negative output length" := by
  simp [fips202Shake256, hL]

theorem fips202Shake128_ok (L : ℕ) (M : List UInt8) :
    ∃ out, fips202Shake128 L M = .ok out ∧ bytesToBits out = SHAKE128 (bytesToBits M) (8 * L) :=
  ⟨shake128 L M, by simp [fips202Shake128], shake128_eq L M⟩

theorem fips202Shake256_ok (L : ℕ) (M : List UInt8) :
    ∃ out, fips202Shake256 L M = .ok out ∧ bytesToBits out = SHAKE256 (bytesToBits M) (8 * L) :=
  ⟨shake256 L M, by simp [fips202Shake256], shake256_eq L M⟩

end OcamlPq.Hash.Keccak
