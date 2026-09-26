import OcamlPq.Hash.Sponge
import OcamlPq.Hash.TurboShakeSpec

/-!
# `turboshake128` and `turboshake256` are RFC 9861 TurboSHAKE

Main results, for every input byte string `M`, output length `L` and domain
byte `D` in `0x01`–`0x7F`:

* `turboshake128_eq`, `turboshake256_eq`: `lib/keccak.ml` `turboshake128` and
  `turboshake256` are RFC 9861 `TurboSHAKE128(M, D, L)` and
  `TurboSHAKE256(M, D, L)`, whatever the initial contents of the
  `Bytes.create` buffers (`turboshake_eq`).
* `turboSHAKE_eq_pad101`: RFC 9861's byte-level padding of `M ‖ D` is FIPS 202
  `pad10*1` applied to `M ‖ ds`, where `ds` are the bits of `D` below its
  highest set bit (`domainBits`), as the RFC states.
* `turboshake128_prefix`, `turboshake256_prefix`: output of length `L` is a
  prefix of output of length `L′ ≥ L`.
* `rfc9861Turboshake128_ok` etc.: `Mlkem.Rfc9861` returns TurboSHAKE for a
  domain in `0x01`–`0x7F` and a non-negative length, and rejects everything
  else with the message the OCaml raises.

The proof reuses the sponge theorems. `permute_from 12` computes
`KECCAK-p[1600, 12]` (`permuteFrom_implements`), so `spongeWith_eq_of` makes
the model FIPS 202 `SPONGE[KECCAK-p[1600, 12], pad10*1, 8·rate](M ‖ ds, 8·L)`,
and `turboSHAKE_eq_pad101` turns that into RFC 9861's definition.
-/

namespace OcamlPq.Hash.Keccak

open FIPS202 RFC9861

/-! ## The domain byte -/

/-- The index of the highest set bit of `D` among bits 0–6. -/
def topBit (D : ℕ) : ℕ := (List.range 7).foldl (fun acc k => if D.testBit k then k else acc) 0

/-- The FIPS 202 domain bits that a domain byte `D` in `0x01`–`0x7F` carries:
its bits below the highest set bit, which is the first `1` of `pad10*1`
(RFC 9861 §2.2). -/
def domainBits (D : ℕ) : Bits := (List.range (topBit D)).map D.testBit

/-- The default domain `0x1F` carries SHAKE's `1111`, and `0x06` SHA-3's `01`. -/
theorem domainBits_1f : domainBits 0x1f = [true, true, true, true] := by decide
theorem domainBits_06 : domainBits 0x06 = [false, true] := by decide

/-- Every domain byte in `0x01`–`0x7F` is a valid `suffix` of `sponge_with`,
encoding `domainBits D`. -/
theorem suffixOK_domain (D : ℕ) (h1 : 1 ≤ D) (h2 : D < 128) : SuffixOK D (domainBits D) := by
  have key : ∀ d : Fin 128, 1 ≤ d.val → (domainBits d.val).length ≤ 6 ∧
      ∀ k : Fin 8, d.val.testBit k.val =
        if h : k.val < (domainBits d.val).length then (domainBits d.val)[k.val]
        else decide (k.val = (domainBits d.val).length) := by
    decide +kernel
  obtain ⟨hl, hb⟩ := key ⟨D, h2⟩ h1
  exact ⟨hl, h2, fun k hk => hb ⟨k, hk⟩⟩

/-! ## RFC 9861's padding is `pad10*1` -/

/-- `padInput` in closed form: `M ‖ D ‖ 00^z` with `z = R − 1 − |M| mod R`,
and `80` XORed into its last byte, at index `⌊|M| / R⌋ · R + R − 1`. -/
theorem padInput_eq (R : ℕ) (hR : 0 < R) (M : List UInt8) (D : UInt8) :
    padInput R M D = (M ++ [D] ++ List.replicate (R - 1 - M.length % R) 0).modify
      (M.length / R * R + R - 1) (· ^^^ 0x80) := by
  have hdm : M.length / R * R + M.length % R = M.length := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod M.length R
  have hm := Nat.mod_lt M.length hR
  have hmod : (M.length + 1) % R = if M.length % R + 1 = R then 0 else M.length % R + 1 := by
    rw [Nat.add_mod]
    by_cases h1 : R = 1
    · subst h1; simp [Nat.mod_one]
    · rw [Nat.mod_eq_of_lt (show 1 < R by omega)]
      by_cases h : M.length % R + 1 = R
      · rw [ite_eq_left h, h, Nat.mod_self]
      · rw [ite_eq_right h, Nat.mod_eq_of_lt (by omega)]
  unfold padInput
  simp only [List.length_append, List.length_singleton]
  generalize M.length / R * R = Q at *
  by_cases h : M.length % R + 1 = R
  · rw [hmod, ite_eq_left h, ite_eq_left rfl, show R - 1 - M.length % R = 0 by omega,
      List.replicate_zero, List.append_nil]
    congr 1
    simp
    omega
  · rw [hmod, ite_eq_right h, ite_eq_right (by omega)]
    simp only [List.length_append, List.length_singleton, List.length_replicate]
    rw [show R - (M.length % R + 1) = R - 1 - M.length % R by omega]
    congr 1
    simp
    omega

theorem xor_128 : ∀ x : Fin 128, x.val ^^^ 128 = x.val ||| 128 := by decide +kernel

/-- The padded input of RFC 9861 is the input's full blocks followed by the
tail block that `sponge_with` builds (`lib/keccak.ml` lines 99–104): the
suffix byte there is `D`, and OR-ing `0x80` into the last byte is XORing it,
since that byte is `D < 0x80` or `0`. -/
theorem padInput_eq_tail (R : ℕ) (hR : 0 < R) (M : List UInt8) (D : ℕ) (hD : D < 128) :
    padInput R M (UInt8.ofNat D) = M.take (M.length / R * R) ++ tailBlock R D M := by
  have hdm : M.length / R * R + M.length % R = M.length := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod M.length R
  have hm := Nat.mod_lt M.length hR
  have hD' : (UInt8.ofNat D).toNat = D := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  rw [padInput_eq R hR]
  apply List.ext_getElem
  · simp [tailBlock_length]; omega
  intro j h1 h2
  simp only [List.length_modify, List.length_append, List.length_singleton,
    List.length_replicate] at h1
  rw [List.getElem_modify]
  by_cases hj : j < M.length / R * R
  · rw [ite_eq_right (by omega), List.getElem_append_left (by simp; omega),
      List.getElem_append_left (by omega), List.getElem_append_left (by simp; omega),
      List.getElem_take]
  · have hk : j - M.length / R * R < R := by omega
    conv => rhs; rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_take, Nat.min_eq_left (show M.length / R * R ≤ M.length by omega)]
    rw [← getElem!_pos (tailBlock R D M) _ (by rw [tailBlock_length]; exact hk)]
    apply UInt8.toNat_inj.mp
    rw [tailBlock_toNat R D M hR hD _ hk, show M.length / R * R + (j - M.length / R * R) = j by omega]
    -- the byte of `M ‖ D ‖ 00…` at `j`
    have hbase : ∀ h, ((M ++ [UInt8.ofNat D] ++ List.replicate (R - 1 - M.length % R) 0)[j]'h).toNat =
        if j - M.length / R * R < M.length % R then (M[j]!).toNat
        else if j - M.length / R * R = M.length % R then D else 0 := by
      intro h
      by_cases hA : j < M.length
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega),
          ite_eq_left (by omega), getElem!_pos M j hA]
      · by_cases hB : j = M.length
        · subst hB
          rw [List.getElem_append_left (by simp), List.getElem_append_right (by omega),
            ite_eq_right (by omega), ite_eq_left (by omega)]
          simp [hD']
        · rw [List.getElem_append_right (by simp; omega), List.getElem_replicate,
            ite_eq_right (by omega), ite_eq_right (by omega)]
          rfl
    by_cases hL : M.length / R * R + R - 1 = j
    · rw [ite_eq_left hL, UInt8.toNat_xor, hbase, ite_eq_left (by omega : j - M.length / R * R = R - 1)]
      have h128 : (128 : UInt8).toNat = 128 := rfl
      rw [h128, ite_eq_right (show ¬ (j - M.length / R * R < M.length % R) by omega)]
      by_cases hB : j - M.length / R * R = M.length % R
      · rw [ite_eq_left hB]; exact xor_128 ⟨D, hD⟩
      · rw [ite_eq_right hB]; rfl
    · rw [ite_eq_right hL, hbase, ite_eq_right (by omega : ¬ j - M.length / R * R = R - 1),
        Nat.or_zero]

/-- FIPS 202's `P = M ‖ ds ‖ pad10*1` is the input's full blocks followed by
the tail block. -/
theorem padded_eq_bytes (R suffix : ℕ) (M : List UInt8) (ds : Bits) (hR : 0 < R)
    (hs : SuffixOK suffix ds) :
    padded R M ds = bytesToBits (M.take (M.length / R * R) ++ tailBlock R suffix M) := by
  have hlenP := padded_length R M ds hR hs.len
  have hlast := padded_block_last R suffix M ds hR hs
  have hqR : M.length / R * R ≤ M.length := Nat.div_mul_le_self _ _
  have e1 : M.length / R * (8 * R) = 8 * (M.length / R * R) := by ring
  have e2 : (M.length / R + 1) * (8 * R) = 8 * (M.length / R * R) + 8 * R := by ring
  rw [e1] at hlast
  rw [bytesToBits_append, ← List.take_append_drop (8 * (M.length / R * R)) (padded R M ds)]
  congr 1
  · unfold padded
    rw [List.append_assoc, List.take_append_of_le_length (by simp; omega), bytesToBits_take]
  · rw [← hlast, List.take_of_length_le (by
      rw [List.length_drop, show (padded R M ds).length = _ from hlenP, e2]; omega)]

/-- FIPS 202's `P` for `M ‖ domainBits D` is RFC 9861's padded input. -/
theorem padded_eq_padInput (R D : ℕ) (hR : 0 < R) (hD1 : 1 ≤ D) (hD2 : D < 128)
    (M : List UInt8) :
    padded R M (domainBits D) = bytesToBits (padInput R M (UInt8.ofNat D)) := by
  rw [padded_eq_bytes R D M _ hR (suffixOK_domain D hD1 hD2), padInput_eq_tail R hR M D hD2]

/-- **RFC 9861's padding is `pad10*1`.** TurboSHAKE with rate `R` and domain
byte `D` is `SPONGE[KECCAK-p[1600, 12], pad10*1, 8·R](M ‖ ds, 8·L)` with
`ds = domainBits D`. -/
theorem turboSHAKE_eq_pad101 (R D : ℕ) (hR : 0 < R) (hD1 : 1 ≤ D) (hD2 : D < 128)
    (M : List UInt8) (L : ℕ) :
    turboSHAKE R M (UInt8.ofNat D) L =
      FIPS202.sponge KP pad101 (8 * R) (bytesToBits M ++ domainBits D) (8 * L) := by
  have h := padded_eq_padInput R D hR hD1 hD2 M
  unfold padded at h
  simp only [turboSHAKE, FIPS202.sponge, noPad, List.append_nil, h]

/-! ## The model -/

/-- **TurboSHAKE.** `sponge_with ~permute:(permute_from 12) ~rate:R ~suffix:D`
is RFC 9861 TurboSHAKE with rate `R` and domain byte `D`, for every rate the
sponge admits, every `D` in `0x01`–`0x7F`, and whatever the initial contents of
the `Bytes.create` buffers. -/
theorem turboshake_eq (R D L : ℕ) (hR : 0 < R) (hR8 : R % 8 = 0) (hR200 : R ≤ 200)
    (hD1 : 1 ≤ D) (hD2 : D < 128) (oj : List UInt8) (bj : ℕ → List UInt8) (hoj : oj.length = L)
    (hbj : ∀ p, (bj p).length = R) (M : List UInt8) :
    bytesToBits (spongeWith (permuteFrom 12) R D L oj bj M) = turboSHAKE R M (UInt8.ofNat D) L := by
  rw [turboSHAKE_eq_pad101 R D hR hD1 hD2]
  exact spongeWith_eq_of (permuteFrom_implements 12 (by norm_num)) R D L (domainBits D) hR hR8
    hR200 (suffixOK_domain D hD1 hD2) oj bj hoj hbj M

/-- **TurboSHAKE128.** `Keccak.turboshake128 ~domain:D ~output_length:L M` is
RFC 9861 `TurboSHAKE128(M, D, L)` for every `D` in `0x01`–`0x7F` and `L ≥ 0`. -/
theorem turboshake128_eq (D L : ℕ) (M : List UInt8) (hD1 : 1 ≤ D) (hD2 : D < 128) :
    bytesToBits (turboshake128 D L M) = TurboSHAKE128 M (UInt8.ofNat D) L :=
  turboshake_eq 168 D L (by norm_num) (by norm_num) (by norm_num) hD1 hD2 _ _
    (List.length_replicate ..) (fun _ => List.length_replicate ..) M

/-- **TurboSHAKE256.** `Keccak.turboshake256 ~domain:D ~output_length:L M` is
RFC 9861 `TurboSHAKE256(M, D, L)` for every `D` in `0x01`–`0x7F` and `L ≥ 0`. -/
theorem turboshake256_eq (D L : ℕ) (M : List UInt8) (hD1 : 1 ≤ D) (hD2 : D < 128) :
    bytesToBits (turboshake256 D L M) = TurboSHAKE256 M (UInt8.ofNat D) L :=
  turboshake_eq 136 D L (by norm_num) (by norm_num) (by norm_num) hD1 hD2 _ _
    (List.length_replicate ..) (fun _ => List.length_replicate ..) M

/-- The rates are `(1600 − 2·{128, 256}) / 8` bytes: RFC 9861's capacities of
32 and 64 bytes. -/
theorem turboshake_rates : 8 * 168 = 1600 - 2 * 128 ∧ 8 * 136 = 1600 - 2 * 256 := by decide

theorem turboshake128_length (D L : ℕ) (M : List UInt8) : (turboshake128 D L M).length = L :=
  (spongeZ_get (permuteFrom 12) 168 D L (by norm_num) (by norm_num) M).1

theorem turboshake256_length (D L : ℕ) (M : List UInt8) : (turboshake256 D L M).length = L :=
  (spongeZ_get (permuteFrom 12) 136 D L (by norm_num) (by norm_num) M).1

/-- **Prefix consistency** (RFC 9861 §2.1): `turboshake128 ~domain:D
~output_length:L M` is a prefix of the output of length `L′ ≥ L`. -/
theorem turboshake128_prefix (D L L' : ℕ) (h : L ≤ L') (M : List UInt8) :
    turboshake128 D L M = (turboshake128 D L' M).take L :=
  spongeZ_prefix (permuteFrom 12) 168 D (by norm_num) (by norm_num) L L' h M

/-- **Prefix consistency** for `turboshake256`. -/
theorem turboshake256_prefix (D L L' : ℕ) (h : L ≤ L') (M : List UInt8) :
    turboshake256 D L M = (turboshake256 D L' M).take L :=
  spongeZ_prefix (permuteFrom 12) 136 D (by norm_num) (by norm_num) L L' h M

/-! ## `Mlkem.Rfc9861` (`lib/mlkem.ml` lines 19–35) -/

/-- `Mlkem.Rfc9861.turboshake128`, `lib/mlkem.ml` lines 22–30: `check`, then
`Keccak.turboshake128`; `invalid_arg` is `Except.error`. `domain` and
`output_length` are OCaml `int`s, so they are integers here; `domain` defaults
to `0x1F`. -/
def rfc9861Turboshake128 (domain outputLength : ℤ) (input : List UInt8) :
    Except String (List UInt8) :=
  if outputLength < 0 then .error "Mlkem.Rfc9861.turboshake128: negative output length"
  else if domain < 0x01 ∨ domain > 0x7f then
    .error "Mlkem.Rfc9861.turboshake128: domain outside 0x01-0x7F"
  else .ok (turboshake128 domain.toNat outputLength.toNat input)

/-- `Mlkem.Rfc9861.turboshake256`, `lib/mlkem.ml` lines 22–27 and 32–34. -/
def rfc9861Turboshake256 (domain outputLength : ℤ) (input : List UInt8) :
    Except String (List UInt8) :=
  if outputLength < 0 then .error "Mlkem.Rfc9861.turboshake256: negative output length"
  else if domain < 0x01 ∨ domain > 0x7f then
    .error "Mlkem.Rfc9861.turboshake256: domain outside 0x01-0x7F"
  else .ok (turboshake256 domain.toNat outputLength.toNat input)

theorem rfc9861Turboshake128_ok (D L : ℕ) (hD1 : 1 ≤ D) (hD2 : D ≤ 0x7f) (M : List UInt8) :
    ∃ out, rfc9861Turboshake128 D L M = .ok out ∧
      bytesToBits out = TurboSHAKE128 M (UInt8.ofNat D) L :=
  ⟨turboshake128 D L M, by
    rw [rfc9861Turboshake128, ite_eq_right (by omega), ite_eq_right (by omega)]; simp,
    turboshake128_eq D L M hD1 (by omega)⟩

theorem rfc9861Turboshake256_ok (D L : ℕ) (hD1 : 1 ≤ D) (hD2 : D ≤ 0x7f) (M : List UInt8) :
    ∃ out, rfc9861Turboshake256 D L M = .ok out ∧
      bytesToBits out = TurboSHAKE256 M (UInt8.ofNat D) L :=
  ⟨turboshake256 D L M, by
    rw [rfc9861Turboshake256, ite_eq_right (by omega), ite_eq_right (by omega)]; simp,
    turboshake256_eq D L M hD1 (by omega)⟩

theorem rfc9861Turboshake128_neg (D L : ℤ) (hL : L < 0) (M : List UInt8) :
    rfc9861Turboshake128 D L M = .error "Mlkem.Rfc9861.turboshake128: negative output length" := by
  simp [rfc9861Turboshake128, hL]

theorem rfc9861Turboshake256_neg (D L : ℤ) (hL : L < 0) (M : List UInt8) :
    rfc9861Turboshake256 D L M = .error "Mlkem.Rfc9861.turboshake256: negative output length" := by
  simp [rfc9861Turboshake256, hL]

/-- A domain byte outside `0x01`–`0x7F`, which would collide with the padding,
is rejected. -/
theorem rfc9861Turboshake128_domain (D L : ℤ) (hL : 0 ≤ L) (hD : D < 0x01 ∨ D > 0x7f)
    (M : List UInt8) :
    rfc9861Turboshake128 D L M = .error "Mlkem.Rfc9861.turboshake128: domain outside 0x01-0x7F" := by
  simp [rfc9861Turboshake128, show ¬ L < 0 by omega, hD]

theorem rfc9861Turboshake256_domain (D L : ℤ) (hL : 0 ≤ L) (hD : D < 0x01 ∨ D > 0x7f)
    (M : List UInt8) :
    rfc9861Turboshake256 D L M = .error "Mlkem.Rfc9861.turboshake256: domain outside 0x01-0x7F" := by
  simp [rfc9861Turboshake256, show ¬ L < 0 by omega, hD]

end OcamlPq.Hash.Keccak
