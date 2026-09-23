import OcamlPq.MLKEMAlg.RefineKEM

/-!
# Key parsing and serialisation

* `parseEk_ok_iff`, `parseEk_repr`: `parse_ek` (= `encapsulation_key_of_octets`)
  succeeds exactly on the inputs that pass the FIPS 203 §7.2 encapsulation key
  check (type check and modulus check), and then returns a record that
  represents its input.
* `encapsulationKeyToOctets_parseEk`, `parseEk_toOctets`: the two round trips
  between records and octets.
* `ofExpanded_ok_iff`, `ofExpanded_repr`: `decapsulation_key_of_expanded`
  succeeds iff the key passes the §7.3 checks (length, hash check) **and** two
  checks that FIPS 203 does not require for decapsulation: the embedded
  encapsulation key passes the §7.2 modulus check, and every 12-bit
  coefficient of `ŝ` is below `q`. The implementation is therefore stricter
  than FIPS 203 §7.3 (see the module doc of `MLKEMAlg.lean`).
* `toExpanded_ofExpanded`: serialising a parsed expanded key gives back its input.
* `ofSeed_toSeed`: `decapsulation_key_to_seed ∘ decapsulation_key_of_seed = Some`.
-/

namespace OcamlPq.MLKEMAlg

open Spec Impl

variable {P : Params} {K : Keccak} {I : ImplPrims} {S : SpecPrims}

/-! ## The parsing loop -/

section ParseLoop

variable (I)

/-- Decoding `r` consecutive 384-byte chunks starting with chunk `i`. -/
def decodeAll (s : Bytes) : ℕ → ℕ → Option (List IPoly)
  | 0, _ => some []
  | r + 1, i =>
    match I.decode12 s (i * 384) with
    | none => none
    | some p => (decodeAll s r (i + 1)).map (p :: ·)

theorem parseLoop_eq (what : String) (s : Bytes) (r : ℕ) (acc : List IPoly) (i : ℕ) :
    parseLoop I what s r acc i =
      match decodeAll I s r i with
      | some l => .ok (acc.reverse ++ l)
      | none => .error (.invalidEncoding (what ++ " contains an unreduced coefficient")) := by
  induction r generalizing acc i with
  | zero => simp [parseLoop, decodeAll]
  | succ r ih =>
    simp only [parseLoop, decode12E, decodeAll, Params.encodingSize12]
    cases h : I.decode12 s (i * 384) with
    | none => rfl
    | some p =>
      simp only [ih]
      cases decodeAll I s r (i + 1) <;> simp

theorem decodeAll_some (s : Bytes) (r i : ℕ) (l : List IPoly) (h : decodeAll I s r i = some l) :
    l.length = r ∧ ∀ j, j < r → I.decode12 s ((i + j) * 384) = some (l.getD j polyZero) := by
  induction r generalizing i l with
  | zero => simp [decodeAll] at h; subst h; simp
  | succ r ih =>
    simp only [decodeAll] at h
    cases hd : I.decode12 s (i * 384) with
    | none => rw [hd] at h; simp at h
    | some p =>
      rw [hd] at h
      cases hr : decodeAll I s r (i + 1) with
      | none => rw [hr] at h; simp at h
      | some l' =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := ih (i + 1) l' hr
        refine ⟨by simp [h1], fun j hj => ?_⟩
        cases j with
        | zero => simpa using hd
        | succ j =>
          have := h2 j (by omega)
          rw [show i + 1 + j = i + (j + 1) by ring] at this
          simpa using this

theorem decodeAll_isSome (s : Bytes) (r i : ℕ) :
    (decodeAll I s r i).isSome ↔ ∀ j < r, (I.decode12 s ((i + j) * 384)).isSome := by
  induction r generalizing i with
  | zero => simp [decodeAll]
  | succ r ih =>
    simp only [decodeAll]
    cases hd : I.decode12 s (i * 384) with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_forall]
      exact ⟨0, by omega, by simp [hd]⟩
    | some p =>
      simp only [Option.isSome_map, ih]
      constructor
      · intro h j hj
        cases j with
        | zero => simp [hd]
        | succ j =>
          have := h j (by omega)
          rwa [show i + 1 + j = i + (j + 1) by ring] at this
      · intro h j hj
        have := h (j + 1) (by omega)
        rwa [show i + (j + 1) = i + 1 + j by ring] at this

end ParseLoop

theorem slice_congr {B : Bytes} {a a' b b' : ℕ} (h1 : a = a') (h2 : b = b') :
    slice B a b = slice B a' b' := by rw [h1, h2]

/-- The chunk that `decode_12` reads, as a FIPS slice. -/
theorem chunk_eq (s : Bytes) (i : ℕ) : stringSub s (i * 384) 384 = slice s (384 * i) (384 * (i + 1)) := by
  rw [stringSub_eq_slice]; congr 1 <;> ring

/-- The parsing loop succeeds iff every chunk passes the modulus check, and
    then entry `i` is canonical and decodes chunk `i`. -/
theorem parseLoop_spec (hR : Refines I S) (what : String) (s : Bytes) (k : ℕ)
    (hs : 384 * k ≤ s.length) :
    ((∃ l, parseLoop I what s k [] 0 = .ok l) ↔
      ∀ i : Fin k, S.byteEncode12 (S.byteDecode12 (slice s (384 * i.val) (384 * (i.val + 1)))) =
        slice s (384 * i.val) (384 * (i.val + 1))) ∧
    ∀ l, parseLoop I what s k [] 0 = .ok l →
      ∀ i : Fin k, Canonical (arrayOfList (k := k) l i) ∧
        toSpec (arrayOfList (k := k) l i) = S.byteDecode12 (slice s (384 * i.val) (384 * (i.val + 1))) := by
  have hchunk : ∀ j < k, j * 384 + 384 ≤ s.length := fun j hj => by nlinarith
  constructor
  · rw [parseLoop_eq]
    constructor
    · rintro ⟨l, hl⟩ i
      cases hd : decodeAll I s k 0 with
      | none => rw [hd] at hl; simp at hl
      | some l' =>
        have hsome : (decodeAll I s k 0).isSome := by rw [hd]; rfl
        have := (decodeAll_isSome I s k 0).1 hsome i.val i.isLt
        rw [zero_add, (hR.decode12 s _ (hchunk i.val i.isLt)).2, chunk_eq] at this
        exact this
    · intro h
      have hsome : (decodeAll I s k 0).isSome := by
        rw [decodeAll_isSome]
        intro j hj
        rw [zero_add, (hR.decode12 s _ (hchunk j hj)).2, chunk_eq]
        exact h ⟨j, hj⟩
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hsome
      exact ⟨l, by rw [hl]; simp⟩
  · intro l hl i
    rw [parseLoop_eq] at hl
    cases hd : decodeAll I s k 0 with
    | none => rw [hd] at hl; simp at hl
    | some l' =>
      rw [hd] at hl
      simp only [List.reverse_nil, List.nil_append, Except.ok.injEq] at hl
      subst hl
      obtain ⟨-, h2⟩ := decodeAll_some I s k 0 l' hd
      have := h2 i.val i.isLt
      rw [zero_add] at this
      obtain ⟨h3, h4⟩ := (hR.decode12 s _ (hchunk i.val i.isLt)).1 _ this
      rw [chunk_eq] at h4
      exact ⟨h3, h4⟩

/-! ## `parse_ek` -/

section ParseEk

variable (hR : Refines I S)
include hR

/-- **Encapsulation key check.** `parse_ek` (= `encapsulation_key_of_octets`)
    succeeds iff its input passes the FIPS 203 §7.2 type check and modulus
    check. -/
theorem parseEk_ok_iff (EK : Bytes) : (∃ ek, parseEk P K I EK = .ok ek) ↔ ekCheck P S EK := by
  have hek := P.ekSize_eq
  unfold parseEk ekCheck
  by_cases hl : EK.length = P.ekSize
  · rw [ite_eq_right (by simpa using hl)]
    have hspec := parseLoop_spec hR "encapsulation key" EK P.k (by omega)
    constructor
    · rintro ⟨ek, hek'⟩
      refine ⟨by omega, hspec.1.1 ?_⟩
      revert hek'
      cases hp : parseLoop I "encapsulation key" EK P.k [] 0 with
      | error e => simp
      | ok l => intro; exact ⟨l, rfl⟩
    · rintro ⟨-, hmod⟩
      obtain ⟨l, hlp⟩ := hspec.1.2 hmod
      rw [hlp]
      exact ⟨_, rfl⟩
  · rw [ite_eq_left (by simpa using hl)]
    simp only [invalidLength, reduceCtorEq, exists_false, false_iff, not_and]
    intro h; omega

/-- A record returned by `parse_ek` represents its input. -/
theorem parseEk_repr {EK : Bytes} {ek : EncapsulationKey P.k} (h : parseEk P K I EK = .ok ek) :
    EkRepr P K S ek EK := by
  have hek := P.ekSize_eq
  unfold parseEk at h
  by_cases hl : EK.length = P.ekSize
  · rw [ite_eq_right (by simpa using hl)] at h
    have hspec := parseLoop_spec hR "encapsulation key" EK P.k (by omega)
    cases hp : parseLoop I "encapsulation key" EK P.k [] 0 with
    | error e => rw [hp] at h; simp at h
    | ok l =>
      rw [hp] at h
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨rfl, hl, ?_, fun i => (hspec.2 l hp i).1, fun i => (hspec.2 l hp i).2, rfl, rfl⟩
      simp only [Params.encodingSize12]
      rw [stringSub_eq_slice, mul_comm]
  · rw [ite_eq_left (by simpa using hl)] at h
    simp [invalidLength] at h

omit hR in
/-- `encapsulation_key_to_octets ∘ encapsulation_key_of_octets = id` on the
    inputs where parsing succeeds. -/
theorem encapsulationKeyToOctets_parseEk {EK : Bytes} {ek : EncapsulationKey P.k}
    (hRepr : EkRepr P K S ek EK) : encapsulationKeyToOctets P ek = EK := by
  simp only [encapsulationKeyToOctets, hRepr.encoded, ← hRepr.length, stringSub_zero_length]

omit hR in
/-- A record is determined by the octets it represents. -/
theorem EkRepr.unique {EK : Bytes} {ek ek' : EncapsulationKey P.k} (h : EkRepr P K S ek EK)
    (h' : EkRepr P K S ek' EK) : ek = ek' := by
  have ht : ek.t = ek'.t := funext fun i =>
    Canonical.eq_of_toSpec (h.t_canon i) (h'.t_canon i) (by rw [h.t_spec, h'.t_spec])
  have hrho : ek.rho = ek'.rho := by rw [h.rho, h'.rho]
  have ha : ek.a = ek'.a := by rw [h.a, h'.a, hrho]
  have hh : ek.h = ek'.h := by rw [h.h, h'.h]
  have he : ek.encoded = ek'.encoded := by rw [h.encoded, h'.encoded]
  cases ek; cases ek'
  simp_all

/-- `encapsulation_key_of_octets ∘ encapsulation_key_to_octets = Ok` on every
    record that represents octets passing the §7.2 check; in particular on
    every key produced by `keygen_internal` (`keygen_ekCheck`). -/
theorem parseEk_toOctets {EK : Bytes} {ek : EncapsulationKey P.k} (hRepr : EkRepr P K S ek EK)
    (hcheck : ekCheck P S EK) : parseEk P K I (encapsulationKeyToOctets P ek) = .ok ek := by
  rw [encapsulationKeyToOctets_parseEk hRepr]
  obtain ⟨ek', hek'⟩ := (parseEk_ok_iff hR EK).2 hcheck
  rw [hek', (parseEk_repr hR hek').unique hRepr]

end ParseEk

/-- The encapsulation key produced by FIPS 203 key generation passes the §7.2
    check. -/
theorem keygen_ekCheck (hR : Refines I S) (hL : S.Laws) (d z : Bytes) :
    ekCheck P S (keyGenInternal P K S d z).1 := by
  simp only [keyGenInternal, kpkeKeyGen]
  have hρ : (G K (d ++ [byte P.k])).1.length = 32 := by
    simp [G, slice, K.sha3_512_length]
  refine ⟨by rw [List.length_append, encodeVec12_length hR, hρ], fun i => ?_⟩
  have hi := i.isLt
  rw [slice_append_of_le _ _ _ _ (by rw [encodeVec12_length hR]; nlinarith), slice_encodeVec12 hR,
    hL.byteDecode12_byteEncode12]

/-! ## `decapsulation_key_of_expanded` -/

theorem slice_append_slice (B : Bytes) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    slice B a b ++ slice B b c = slice B a c := by
  simp only [slice]
  have hb : B.take b = (B.take c).take b := by rw [List.take_take, min_eq_left hbc]
  rw [hb, List.drop_take]
  conv_rhs => rw [← List.take_append_drop (b - a) ((B.take c).drop a), List.drop_drop]
  rw [show a + (b - a) = b by omega]

theorem flatten_slices (B : Bytes) (c k : ℕ) :
    (List.ofFn fun i : Fin k => slice B (c * i.val) (c * (i.val + 1))).flatten = slice B 0 (c * k) := by
  induction k with
  | zero => simp [slice]
  | succ k ih =>
    rw [List.ofFn_succ_last, List.flatten_concat]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, slice_append_slice _ _ _ _ (by omega) (by nlinarith)]

section OfExpanded

variable (hR : Refines I S)
include hR

/-- A key returned by `decapsulation_key_of_expanded` represents its input and
    carries no seed. -/
theorem ofExpanded_repr {DK : Bytes} {dk : DecapsulationKey P.k}
    (h : decapsulationKeyOfExpanded P K I DK = .ok dk) : DkRepr P K S dk DK ∧ dk.seed = none := by
  have hdk := P.dkSize_eq
  have hek := P.ekSize_eq
  unfold decapsulationKeyOfExpanded at h
  by_cases hl : DK.length = P.dkSize
  swap
  · rw [ite_eq_left (by simpa using hl)] at h; simp [invalidLength] at h
  rw [ite_eq_right (by simpa using hl)] at h
  have hspec := parseLoop_spec hR "expanded decapsulation key" DK P.k (by omega)
  cases hp : parseLoop I "expanded decapsulation key" DK P.k [] 0 with
  | error e => rw [hp] at h; simp at h
  | ok sl =>
    rw [hp] at h
    simp only at h
    cases hpe : parseEk P K I (stringSub DK (P.k * Params.encodingSize12) P.ekSize) with
    | error e => rw [hpe] at h; simp at h
    | ok ek =>
      rw [hpe] at h
      simp only at h
      have hrepr := parseEk_repr hR hpe
      have hhlen : ek.h.length = 32 := by rw [hrepr.h, K.sha3_256_length]
      have hsub : (stringSub DK (P.k * Params.encodingSize12 + P.ekSize) 32).length = 32 :=
        stringSub_length (by simp only [Params.encodingSize12]; omega)
      rw [ctEqual_spec _ _ (by rw [hsub, hhlen])] at h
      by_cases heq : stringSub DK (P.k * Params.encodingSize12 + P.ekSize) 32 = ek.h
      swap
      · rw [ite_eq_right heq] at h; simp at h
      rw [ite_eq_left heq] at h
      simp only [ne_eq, not_true_eq_false, ite_false, Except.ok.injEq] at h
      subst h
      have hsubEk : stringSub DK (P.k * Params.encodingSize12) P.ekSize =
          slice DK (384 * P.k) (768 * P.k + 32) := by
        simp only [Params.encodingSize12]; rw [stringSub_eq_slice]; exact slice_congr (by ring) (by omega)
      rw [hsubEk] at hrepr
      refine ⟨⟨hl, fun i => (hspec.2 sl hp i).1, fun i => (hspec.2 sl hp i).2, hrepr, ?_, ?_⟩, rfl⟩
      · show ek.h = _
        rw [← heq, stringSub_eq_slice]; simp only [Params.encodingSize12]
        exact slice_congr (by omega) (by omega)
      · show stringSub DK _ 32 = _
        rw [stringSub_eq_slice]; simp only [Params.encodingSize12]
        exact slice_congr (by omega) (by omega)

/-- **Decapsulation key check.** `decapsulation_key_of_expanded` succeeds
    iff (1) the key passes the FIPS 203 §7.3 checks (length `768k + 96` and
    `H(dk[384k : 768k + 32]) = dk[768k + 32 : 768k + 64]`), (2) the embedded
    encapsulation key passes the §7.2 check, and (3) every chunk of `ŝ` passes
    the modulus check. (2) and (3) are not required by FIPS 203 §7.3. -/
theorem ofExpanded_ok_iff (DK : Bytes) :
    (∃ dk, decapsulationKeyOfExpanded P K I DK = .ok dk) ↔
      dkCheck P K DK ∧ ekCheck P S (slice DK (384 * P.k) (768 * P.k + 32)) ∧
      ∀ i : Fin P.k, S.byteEncode12 (S.byteDecode12 (slice DK (384 * i.val) (384 * (i.val + 1)))) =
        slice DK (384 * i.val) (384 * (i.val + 1)) := by
  have hdk := P.dkSize_eq
  have hek := P.ekSize_eq
  constructor
  · rintro ⟨dk, h⟩
    obtain ⟨hrepr, -⟩ := ofExpanded_repr hR h
    have hl := hrepr.length
    refine ⟨⟨by omega, ?_⟩, ?_, ?_⟩
    · rw [H, ← hrepr.ek.h, hrepr.h]
    · -- the embedded key is parsed by `parse_ek`
      have hsubEk : stringSub DK (P.k * Params.encodingSize12) P.ekSize =
          slice DK (384 * P.k) (768 * P.k + 32) := by
        simp only [Params.encodingSize12]; rw [stringSub_eq_slice]; exact slice_congr (by ring) (by omega)
      unfold decapsulationKeyOfExpanded at h
      rw [ite_eq_right (by simpa using hl)] at h
      cases hp : parseLoop I "expanded decapsulation key" DK P.k [] 0 with
      | error e => rw [hp] at h; simp at h
      | ok sl =>
        rw [hp] at h
        simp only at h
        cases hpe : parseEk P K I (stringSub DK (P.k * Params.encodingSize12) P.ekSize) with
        | error e => rw [hpe] at h; simp at h
        | ok ek =>
          have := (parseEk_ok_iff (P := P) (K := K) hR
            (stringSub DK (P.k * Params.encodingSize12) P.ekSize)).1 ⟨ek, hpe⟩
          rwa [hsubEk] at this
    · have hspec := parseLoop_spec hR "expanded decapsulation key" DK P.k (by omega)
      unfold decapsulationKeyOfExpanded at h
      rw [ite_eq_right (by simpa using hl)] at h
      apply hspec.1.1
      cases hp : parseLoop I "expanded decapsulation key" DK P.k [] 0 with
      | error e => rw [hp] at h; simp at h
      | ok sl => exact ⟨sl, rfl⟩
  · rintro ⟨⟨hl, hhash⟩, hekc, hs⟩
    have hspec := parseLoop_spec hR "expanded decapsulation key" DK P.k (by omega)
    obtain ⟨sl, hp⟩ := hspec.1.2 hs
    have hsub : stringSub DK (P.k * Params.encodingSize12) P.ekSize = slice DK (384 * P.k) (768 * P.k + 32) := by
      simp only [Params.encodingSize12]
      rw [stringSub_eq_slice]; exact slice_congr (by ring) (by omega)
    obtain ⟨ek, hpe⟩ := (parseEk_ok_iff (P := P) (K := K) hR
      (stringSub DK (P.k * Params.encodingSize12) P.ekSize)).2 (by rw [hsub]; exact hekc)
    have hrepr := parseEk_repr hR hpe
    have hhs : stringSub DK (P.k * Params.encodingSize12 + P.ekSize) 32 = ek.h := by
      rw [hrepr.h, hsub]
      simp only [H] at hhash
      rw [hhash, stringSub_eq_slice]; simp only [Params.encodingSize12]
      exact slice_congr (by omega) (by omega)
    unfold decapsulationKeyOfExpanded
    rw [ite_eq_right (by omega), hp]
    simp only
    rw [hpe]
    simp only
    rw [ctEqual_spec _ _ (by rw [hhs]), ite_eq_left hhs]
    simp

/-- `decapsulation_key_to_expanded ∘ decapsulation_key_of_expanded = id` on
    the inputs where parsing succeeds. -/
theorem toExpanded_ofExpanded (g : ℕ → Byte) {DK : Bytes} {dk : DecapsulationKey P.k}
    (h : decapsulationKeyOfExpanded P K I DK = .ok dk) :
    decapsulationKeyToExpanded P I g dk = DK := by
  have hdk := P.dkSize_eq
  have hek := P.ekSize_eq
  obtain ⟨hrepr, -⟩ := ofExpanded_repr hR h
  obtain ⟨-, -, hmod⟩ := (ofExpanded_ok_iff hR DK).1 ⟨dk, h⟩
  have hl := hrepr.length
  have henc := hrepr.ek.encoded
  have hencl : dk.ek.encoded.length = P.ekSize := by
    rw [henc, slice_length _ _ _ (by omega) (by omega)]; omega
  rw [toExpanded_eq hR g dk hrepr.s_canon hencl
      (by rw [hrepr.h, slice_length _ _ _ (by omega) (by omega)]; omega)
      (by rw [hrepr.z, slice_length _ _ _ (by omega) (by omega)]; omega)]
  have hs : encodeVec12 P S (fun i => toSpec (dk.s i)) = slice DK 0 (384 * P.k) := by
    rw [← flatten_slices]
    unfold encodeVec12
    congr 1
    apply congrArg List.ofFn; funext i
    simp only [hrepr.s_spec, hmod]
  rw [hs, henc, hrepr.h, hrepr.z, slice_append_slice _ _ _ _ (by omega) (by omega),
    slice_append_slice _ _ _ _ (by omega) (by omega), slice_append_slice _ _ _ _ (by omega) (by omega),
    show 768 * P.k + 96 = DK.length by omega, slice_all]

end OfExpanded

/-! ## Seeds -/

/-- **Seed round trip.** For a 64-byte seed, `decapsulation_key_of_seed`
    succeeds (it runs `keygen_internal` on `seed[0:32]`, `seed[32:64]`), and
    `decapsulation_key_to_seed` returns the seed. -/
theorem ofSeed_toSeed (g : ℕ → Byte) (seed : Bytes) (h : seed.length = 64) :
    ∃ dk, decapsulationKeyOfSeed P K I g seed = .ok dk ∧
      keygenInternal P K I g (stringSub seed 0 32) (stringSub seed 32 32) = .ok dk ∧
      decapsulationKeyToSeed dk = some seed := by
  have h1 : (stringSub seed 0 32).length = 32 := stringSub_length (by omega)
  have h2 : (stringSub seed 32 32).length = 32 := stringSub_length (by omega)
  have hcat : stringSub seed 0 32 ++ stringSub seed 32 32 = seed := by
    simp only [stringSub, List.drop_zero]
    rw [List.take_of_length_le (l := List.drop 32 seed) (by simp; omega), List.take_append_drop]
  unfold decapsulationKeyOfSeed
  rw [ite_eq_right (by simp [Params.seedSize, h]), keygenInternal_unfold P K I g _ _ h1 h2]
  refine ⟨_, rfl, rfl, ?_⟩
  simp only [decapsulationKeyToSeed, Option.map_some, hcat, stringSub_zero_length]

/-- `decapsulation_key_of_seed` rejects seeds that are not 64 bytes long. -/
theorem ofSeed_length (g : ℕ → Byte) (seed : Bytes) (h : seed.length ≠ 64) :
    decapsulationKeyOfSeed P K I g seed = invalidLength "decapsulation key seed" 64 seed.length := by
  unfold decapsulationKeyOfSeed
  rw [ite_eq_left (by simpa [Params.seedSize] using h)]
  rfl

end OcamlPq.MLKEMAlg
