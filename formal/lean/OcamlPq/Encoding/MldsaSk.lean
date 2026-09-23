import OcamlPq.Encoding.MldsaLayout

/-!
# ML-DSA expanded signing keys

Models of `encode_expanded_signing_key` (`mldsa/mldsa_engine.ml`
lines 488–493) and `decode_expanded_signing_key` (lines 495–529).

* `encodeSk_eq_spec`: the encoder is FIPS 204 `skEncode` (Algorithm 24).
* `decodeSk_regions`: the decoder reads `ρ` from `[0, 32)`, `K` from
  `[32, 64)`, `tr` from `[64, 128)`, `s₁[i]` from `128 + i·E`, `s₂[i]` from
  `128 + (ℓ + i)·E` and `t₀[i]` from `128 + (ℓ + k)·E + 416·i`
  (`E = 32·eta_bits`): exactly the regions the encoder writes, tiling a key of
  length `signing_key_size`.
* `decodeSk_encodeSk`: decoding an encoded key gives back its parts.
* `encodeSk_decodeSk`: canonicity — an accepted key is the encoding of what
  it decodes to.
-/

namespace OcamlPq.Encoding.Mldsa

open OcamlPq.Encoding
open OcamlPq.Encoding.Packer

theorem set_append_replicate' {α : Type} (E : List α) (x d : α) (m : ℕ) :
    (E ++ List.replicate (m + 1) d).set E.length x = E ++ [x] ++ List.replicate m d := by
  rw [List.set_append]
  simp [List.replicate_succ]

/-- `encode_expanded_signing_key` (lines 488–493):
`String.concat "" [rho; key; tr; pack_eta s1…; pack_eta s2…; pack_t0 t0…]`. -/
def encodeSk (P : Params) (rho key tr : List ℕ) (s1 s2 t0 : List (List ℤ)) : List ℕ :=
  rho ++ key ++ tr ++ (s1.map (packEta P.eta)).flatten ++ (s2.map (packEta P.eta)).flatten ++
    (t0.map packT0).flatten

/-- One iteration of `decode_eta_vector` (lines 507–511):
```
let encoded = sub octets !position eta_packed_bytes in
position := !position + eta_packed_bytes;
match unpack_eta encoded with
| Ok polynomial -> output.(index) <- polynomial
| Error value -> error := Some value
``` -/
def etaStep (P : Params) (octets : List ℕ) (st : List (List ℤ) × Bool × ℕ) (index : ℕ) :
    List (List ℤ) × Bool × ℕ :=
  let encoded := sub octets st.2.2 P.etaPackedBytes
  let position := st.2.2 + P.etaPackedBytes
  match unpackEta P.eta encoded with
  | some polynomial => (st.1.set index polynomial, st.2.1, position)
  | none => (st.1, true, position)

/-- `decode_eta_vector length` (lines 503–513) from `position`: the result
and the advanced `position`. -/
def decodeEtaVector (P : Params) (octets : List ℕ) (length position : ℕ) :
    Option (List (List ℤ)) × ℕ :=
  let st := (List.range length).foldl (etaStep P octets) (List.replicate length [], false, position)
  (if st.2.1 then none else some st.1, st.2.2)

/-- `decode_expanded_signing_key octets` (lines 495–529); `none` is
`Error _`. -/
def decodeSk (P : Params) (octets : List ℕ) :
    Option (List ℕ × List ℕ × List ℕ × List (List ℤ) × List (List ℤ) × List (List ℤ)) :=
  if octets.length ≠ P.skSize then none
  else
    let rho := sub octets 0 32
    let key := sub octets 32 32
    let tr := sub octets 64 64
    match decodeEtaVector P octets P.l 128 with
    | (none, _) => none
    | (some s1, position) =>
      match decodeEtaVector P octets P.k position with
      | (none, _) => none
      | (some s2, position) =>
        let t0 := (List.range P.k).map (fun index =>
          unpackT0 (sub octets (position + index * 416) 416))
        some (rho, key, tr, s1, s2, t0)

/-- The block `decode_eta_vector` reads in iteration `i`. -/
def etaBlock (P : Params) (octets : List ℕ) (position i : ℕ) : List ℕ :=
  sub octets (position + i * P.etaPackedBytes) P.etaPackedBytes

theorem etaStep_fold (P : Params) (octets : List ℕ) (length position : ℕ) :
    ∀ m, m ≤ length →
      let st := (List.range m).foldl (etaStep P octets) (List.replicate length [], false, position)
      st.2.2 = position + m * P.etaPackedBytes ∧
      (st.2.1 = true ↔ ∃ i < m, unpackEta P.eta (etaBlock P octets position i) = none) ∧
      ((∀ i < m, (unpackEta P.eta (etaBlock P octets position i)).isSome) →
        st.1 = (List.range m).map (fun i => (unpackEta P.eta (etaBlock P octets position i)).getD [])
          ++ List.replicate (length - m) []) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    simp only at h1 h2 h3 ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hst : (List.range m).foldl (etaStep P octets)
      (List.replicate length [], false, position) = st at h1 h2 h3
    unfold etaStep
    simp only
    have hblk : sub octets st.2.2 P.etaPackedBytes = etaBlock P octets position m := by
      rw [h1]; rfl
    rw [hblk]
    cases hu : unpackEta P.eta (etaBlock P octets position m) with
    | none =>
      simp only
      refine ⟨by rw [h1]; ring, ⟨fun _ => ⟨m, by omega, hu⟩, fun _ => trivial⟩, fun hall => ?_⟩
      have := hall m (by omega)
      rw [hu] at this; simp at this
    | some p =>
      simp only
      refine ⟨by rw [h1]; ring, ?_, fun hall => ?_⟩
      · rw [h2]
        constructor
        · rintro ⟨i, hi, hn⟩; exact ⟨i, by omega, hn⟩
        · rintro ⟨i, hi, hn⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | he
          · exact ⟨i, hlt, hn⟩
          · subst he; rw [hu] at hn; cases hn
      · rw [h3 (fun i hi => hall i (by omega))]
        obtain ⟨r, hr⟩ : ∃ r, length - m = r + 1 := ⟨length - m - 1, by omega⟩
        have := set_append_replicate' ((List.range m).map
          (fun i => (unpackEta P.eta (etaBlock P octets position i)).getD [])) p [] r
        simp only [List.length_map, List.length_range] at this
        rw [hr, this, List.map_append, List.map_singleton, hu,
          show length - (m + 1) = r by omega]
        rfl

theorem decodeEtaVector_eq (P : Params) (octets : List ℕ) (length position : ℕ) :
    decodeEtaVector P octets length position =
      (if ∀ i < length, (unpackEta P.eta (etaBlock P octets position i)).isSome
       then some ((List.range length).map
         (fun i => (unpackEta P.eta (etaBlock P octets position i)).getD []))
       else none, position + length * P.etaPackedBytes) := by
  obtain ⟨h1, h2, h3⟩ := etaStep_fold P octets length position length le_rfl
  unfold decodeEtaVector
  simp only
  rw [h1]
  by_cases hall : ∀ i < length, (unpackEta P.eta (etaBlock P octets position i)).isSome
  · have hflag : ((List.range length).foldl (etaStep P octets)
        (List.replicate length [], false, position)).2.1 = false := by
      cases hf : ((List.range length).foldl (etaStep P octets)
        (List.replicate length [], false, position)).2.1
      · rfl
      · obtain ⟨i, hi, hn⟩ := h2.mp hf
        have := hall i hi
        rw [hn] at this; cases this
    rw [hflag, ite_eq_left hall, h3 hall, Nat.sub_self, List.replicate_zero, List.append_nil]
    rfl
  · have hflag : ((List.range length).foldl (etaStep P octets)
        (List.replicate length [], false, position)).2.1 = true := by
      apply h2.mpr
      push Not at hall
      obtain ⟨i, hi, hn⟩ := hall
      exact ⟨i, hi, by simpa using hn⟩
    rw [hflag, ite_eq_right hall]
    rfl

/-! ## FIPS 204 `skEncode` -/

/-- FIPS 204 Algorithm 24, `skEncode(ρ, K, tr, s₁, s₂, t₀)`. -/
def skEncode (P : Params) (rho key tr : List ℕ) (s1 s2 t0 : List (List ℤ)) : List ℕ :=
  let sk := rho ++ key ++ tr
  let sk := (List.range P.l).foldl (fun sk i => sk ++ Spec.bitPack (s1.getD i []) P.eta P.eta) sk
  let sk := (List.range P.k).foldl (fun sk i => sk ++ Spec.bitPack (s2.getD i []) P.eta P.eta) sk
  (List.range P.k).foldl (fun sk i => sk ++ Spec.bitPack (t0.getD i []) (2 ^ 12 - 1) (2 ^ 12)) sk

/-- A well-formed expanded signing key. -/
structure SkInput (P : Params) (rho key tr : List ℕ) (s1 s2 t0 : List (List ℤ)) : Prop where
  rho_len : rho.length = 32
  key_len : key.length = 32
  tr_len : tr.length = 64
  bytes_lt : ∀ x ∈ rho ++ key ++ tr, x < 256
  s1_len : s1.length = P.l
  s2_len : s2.length = P.k
  t0_len : t0.length = P.k
  s1_poly : ∀ p ∈ s1, p.length = 256 ∧ ∀ v ∈ p, EtaRange P.eta v
  s2_poly : ∀ p ∈ s2, p.length = 256 ∧ ∀ v ∈ p, EtaRange P.eta v
  t0_poly : ∀ p ∈ t0, p.length = 256 ∧ ∀ v ∈ p, T0Range v

theorem encodeSk_eq_spec (P : Params) (hP : P.Valid) (rho key tr : List ℕ)
    (s1 s2 t0 : List (List ℤ)) (hin : SkInput P rho key tr s1 s2 t0) :
    encodeSk P rho key tr s1 s2 t0 = skEncode P rho key tr s1 s2 t0 := by
  unfold encodeSk skEncode
  simp only
  rw [Spec.foldl_append_range, Spec.foldl_append_range, Spec.foldl_append_range]
  have e1 : (List.range P.l).flatMap (fun i => Spec.bitPack (s1.getD i []) P.eta P.eta) =
      (s1.map (packEta P.eta)).flatten := by
    rw [← hin.s1_len, Spec.flatMap_range_getD' s1 [] (fun p => Spec.bitPack p P.eta P.eta),
      List.flatMap_def, List.map_congr_left (fun p hp =>
        packEta_eq P.eta hP.1 p (hin.s1_poly p hp).1 (hin.s1_poly p hp).2)]
  have e2 : (List.range P.k).flatMap (fun i => Spec.bitPack (s2.getD i []) P.eta P.eta) =
      (s2.map (packEta P.eta)).flatten := by
    rw [← hin.s2_len, Spec.flatMap_range_getD' s2 [] (fun p => Spec.bitPack p P.eta P.eta),
      List.flatMap_def, List.map_congr_left (fun p hp =>
        packEta_eq P.eta hP.1 p (hin.s2_poly p hp).1 (hin.s2_poly p hp).2)]
  have e3 : (List.range P.k).flatMap (fun i => Spec.bitPack (t0.getD i []) (2 ^ 12 - 1) (2 ^ 12)) =
      (t0.map packT0).flatten := by
    rw [← hin.t0_len, Spec.flatMap_range_getD' t0 [] (fun p => Spec.bitPack p (2 ^ 12 - 1) (2 ^ 12)),
      List.flatMap_def, List.map_congr_left (fun p hp =>
        packT0_eq p (hin.t0_poly p hp).1 (hin.t0_poly p hp).2)]
  rw [e1, e2, e3]

/-! ## Regions -/

theorem length_packEta (P : Params) (p : List ℤ) (hp : p.length = 256) :
    (packEta P.eta p).length = P.etaPackedBytes := by
  unfold packEta; rw [length_packCodes]; simp [hp, Params.etaPackedBytes]

theorem length_packT0 (p : List ℤ) (hp : p.length = 256) : (packT0 p).length = 416 := by
  unfold packT0; rw [length_packCodes]; simp [hp]

/-- **The signing-key regions.** In a key `ρ ‖ K ‖ tr ‖ S₁ ‖ S₂ ‖ T₀` with
blocks of the right lengths, the decoder's `sub` calls read exactly `ρ`, `K`,
`tr`, the `i`-th block of `S₁`, of `S₂` and of `T₀`. -/
theorem decodeSk_regions (P : Params) (rho key tr : List ℕ) (S1 S2 T0 : List (List ℕ))
    (hrho : rho.length = 32) (hkey : key.length = 32) (htr : tr.length = 64)
    (hS1 : ∀ b ∈ S1, b.length = P.etaPackedBytes) (hS2 : ∀ b ∈ S2, b.length = P.etaPackedBytes)
    (hT0 : ∀ b ∈ T0, b.length = 416) (hl : S1.length = P.l) (hk2 : S2.length = P.k)
    (hk0 : T0.length = P.k) :
    let octets := rho ++ key ++ tr ++ S1.flatten ++ S2.flatten ++ T0.flatten
    octets.length = P.skSize ∧
    sub octets 0 32 = rho ∧ sub octets 32 32 = key ∧ sub octets 64 64 = tr ∧
    (∀ i (hi : i < P.l), etaBlock P octets 128 i = S1[i]'(by omega)) ∧
    (∀ i (hi : i < P.k), etaBlock P octets (128 + P.l * P.etaPackedBytes) i = S2[i]'(by omega)) ∧
    (∀ i (hi : i < P.k), sub octets (128 + P.l * P.etaPackedBytes + P.k * P.etaPackedBytes + i * 416)
      416 = T0[i]'(by omega)) := by
  intro octets
  have f1 := length_flatten_blocks S1 _ hS1
  have f2 := length_flatten_blocks S2 _ hS2
  have f3 := length_flatten_blocks T0 _ hT0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [octets, List.length_append, hrho, hkey, htr, f1, f2, f3, hl, hk2, hk0, Params.skSize]
    ring
  · have := sub_prefix' [] rho (key ++ tr ++ S1.flatten ++ S2.flatten ++ T0.flatten) 0 32 rfl
      hrho.symm
    simp only [octets, List.nil_append, List.append_assoc] at this ⊢; exact this
  · have := sub_prefix' rho key (tr ++ S1.flatten ++ S2.flatten ++ T0.flatten) 32 32 hrho.symm
      hkey.symm
    simp only [octets, List.append_assoc] at this ⊢; exact this
  · have := sub_prefix' (rho ++ key) tr (S1.flatten ++ S2.flatten ++ T0.flatten) 64 64
      (by simp [hrho, hkey]) htr.symm
    simp only [octets, List.append_assoc] at this ⊢; exact this
  · intro i hi
    unfold etaBlock
    have := sub_block S1 _ hS1 (rho ++ key ++ tr) (S2.flatten ++ T0.flatten) i (by omega)
    simp only [List.length_append, hrho, hkey, htr, List.append_assoc] at this
    simp only [octets, List.append_assoc]
    rw [← this]
  · intro i hi
    unfold etaBlock
    have := sub_block S2 _ hS2 (rho ++ key ++ tr ++ S1.flatten) T0.flatten i (by omega)
    simp only [List.length_append, hrho, hkey, htr, f1, hl, List.append_assoc] at this
    simp only [octets, List.append_assoc]
    rw [show 128 + P.l * P.etaPackedBytes + i * P.etaPackedBytes =
      32 + (32 + (64 + P.l * P.etaPackedBytes)) + i * P.etaPackedBytes by ring, this]
  · intro i hi
    have := sub_block T0 416 hT0 (rho ++ key ++ tr ++ S1.flatten ++ S2.flatten) [] i (by omega)
    simp only [List.length_append, hrho, hkey, htr, f1, f2, hl, hk2, List.append_nil,
      List.append_assoc] at this
    simp only [octets, List.append_assoc]
    rw [show 128 + P.l * P.etaPackedBytes + P.k * P.etaPackedBytes + i * 416 =
      32 + (32 + (64 + (P.l * P.etaPackedBytes + P.k * P.etaPackedBytes))) + i * 416 by ring, this]

/-! ## Round trips -/

theorem packEta_lt (P : Params) (hP : P.Valid) (p : List ℤ) (hp : p.length = 256)
    (hr : ∀ v ∈ p, EtaRange P.eta v) : ∀ x ∈ packEta P.eta p, x < 256 := by
  have hcodes : ∀ x ∈ p.map (fun v => ((P.eta : ℤ) - v).toNat), x < 2 ^ etaBits P.eta := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ha, hb⟩ := hr v hv
    have := (eta_cases P.eta hP.1).2.2
    omega
  have hreg := packCodes_regroup hcodes (by simp [hp]; exact ⟨32 * etaBits P.eta, by ring⟩)
  exact hreg.right_lt

theorem unpackEta_packEta (P : Params) (hP : P.Valid) (p : List ℤ) (hp : p.length = 256)
    (hr : ∀ v ∈ p, EtaRange P.eta v) : unpackEta P.eta (packEta P.eta p) = some p := by
  rw [unpackEta_eq_some_iff P.eta hP.1 _
    (by rw [length_packEta P p hp, Params.etaPackedBytes_eq]) (packEta_lt P hP p hp hr)]
  exact ⟨hp, hr, rfl⟩

theorem packT0_lt (p : List ℤ) (hp : p.length = 256) (hr : ∀ v ∈ p, T0Range v) :
    ∀ x ∈ packT0 p, x < 256 := by
  have hcodes : ∀ x ∈ p.map (fun v => ((2 ^ 12 : ℕ) - v : ℤ).toNat), x < 2 ^ 13 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ha, hb⟩ := hr v hv
    push_cast
    omega
  exact (packCodes_regroup hcodes (by simp [hp])).right_lt

theorem sub_split (s : List ℕ) (o a b : ℕ) : sub s o (a + b) = sub s o a ++ sub s (o + a) b := by
  unfold sub; rw [List.take_add, List.drop_drop]

theorem sub_three (s : List ℕ) (a b c : ℕ) :
    sub s 0 a ++ sub s a b ++ sub s (a + b) c = sub s 0 (a + b + c) := by
  rw [sub_split s 0 (a + b) c, sub_split s 0 a b, zero_add, zero_add]

theorem flatten_sub_blocks (s : List ℕ) (off n len : ℕ) :
    ((List.range n).map (fun i => sub s (off + i * len) len)).flatten = sub s off (n * len) := by
  induction n with
  | zero => simp [sub]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih, List.map_singleton,
      List.flatten_singleton, Nat.succ_mul, sub_split]

theorem decodeSk_encodeSk (P : Params) (hP : P.Valid) (rho key tr : List ℕ)
    (s1 s2 t0 : List (List ℤ)) (hin : SkInput P rho key tr s1 s2 t0) :
    decodeSk P (encodeSk P rho key tr s1 s2 t0) = some (rho, key, tr, s1, s2, t0) := by
  have hS1 : ∀ b ∈ s1.map (packEta P.eta), b.length = P.etaPackedBytes := by
    intro b hb; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact length_packEta P p (hin.s1_poly p hp).1
  have hS2 : ∀ b ∈ s2.map (packEta P.eta), b.length = P.etaPackedBytes := by
    intro b hb; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact length_packEta P p (hin.s2_poly p hp).1
  have hT0 : ∀ b ∈ t0.map packT0, b.length = 416 := by
    intro b hb; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact length_packT0 p (hin.t0_poly p hp).1
  obtain ⟨hlen, r1, r2, r3, r4, r5, r6⟩ := decodeSk_regions P rho key tr _ _ _ hin.rho_len
    hin.key_len hin.tr_len hS1 hS2 hT0 (by simp [hin.s1_len]) (by simp [hin.s2_len])
    (by simp [hin.t0_len])
  unfold encodeSk decodeSk
  rw [ite_eq_right (by rw [hlen]; simp)]
  have hb1 : ∀ i (hi : i < P.l), unpackEta P.eta (etaBlock P (rho ++ key ++ tr ++
      (s1.map (packEta P.eta)).flatten ++ (s2.map (packEta P.eta)).flatten ++
      (t0.map packT0).flatten) 128 i) = some (s1[i]'(by rw [hin.s1_len]; exact hi)) := by
    intro i hi
    rw [r4 i hi, List.getElem_map]
    have hmem := List.getElem_mem (show i < s1.length by rw [hin.s1_len]; exact hi)
    exact unpackEta_packEta P hP _ (hin.s1_poly _ hmem).1 (hin.s1_poly _ hmem).2
  have hb2 : ∀ i (hi : i < P.k), unpackEta P.eta (etaBlock P (rho ++ key ++ tr ++
      (s1.map (packEta P.eta)).flatten ++ (s2.map (packEta P.eta)).flatten ++
      (t0.map packT0).flatten) (128 + P.l * P.etaPackedBytes) i) =
      some (s2[i]'(by rw [hin.s2_len]; exact hi)) := by
    intro i hi
    rw [r5 i hi, List.getElem_map]
    have hmem := List.getElem_mem (show i < s2.length by rw [hin.s2_len]; exact hi)
    exact unpackEta_packEta P hP _ (hin.s2_poly _ hmem).1 (hin.s2_poly _ hmem).2
  rw [decodeEtaVector_eq, ite_eq_left (fun i hi => by rw [hb1 i hi]; rfl)]
  simp only
  rw [decodeEtaVector_eq, ite_eq_left (fun i hi => by rw [hb2 i hi]; rfl)]
  simp only [Option.some.injEq, Prod.mk.injEq]
  refine ⟨r1, r2, r3, ?_, ?_, ?_⟩
  · apply List.ext_getElem
    · simp [hin.s1_len]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [hb1 i (by simpa using h1)]; rfl
  · apply List.ext_getElem
    · simp [hin.s2_len]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [hb2 i (by simpa using h1)]; rfl
  · apply List.ext_getElem
    · simp [hin.t0_len]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [r6 i (by simpa using h1), List.getElem_map]
      have hmem := List.getElem_mem h2
      exact unpackT0_packT0 _ (hin.t0_poly _ hmem).1 (hin.t0_poly _ hmem).2

/-- **Canonicity of signing keys.** If `decode_expanded_signing_key` accepts
`octets`, then `octets` is exactly the encoding of the decoded parts. -/
theorem encodeSk_decodeSk (P : Params) (hP : P.Valid) (octets : List ℕ)
    (hb : ∀ x ∈ octets, x < 256) (rho key tr : List ℕ) (s1 s2 t0 : List (List ℤ))
    (hdec : decodeSk P octets = some (rho, key, tr, s1, s2, t0)) :
    encodeSk P rho key tr s1 s2 t0 = octets := by
  have hlen : octets.length = P.skSize := by
    unfold decodeSk at hdec
    by_contra hne
    rw [ite_eq_left hne] at hdec
    cases hdec
  have hE := Params.etaPackedBytes_eq P
  obtain ⟨-, h1, -⟩ := eta_cases P.eta hP.1
  unfold decodeSk at hdec
  rw [ite_eq_right (by rw [hlen]; simp), decodeEtaVector_eq] at hdec
  try simp only at hdec
  split_ifs at hdec with hall1
  · try simp only at hdec
    rw [decodeEtaVector_eq] at hdec
    try simp only at hdec
    split_ifs at hdec with hall2
    · simp only [Option.some.injEq, Prod.mk.injEq] at hdec
      obtain ⟨hr, hk, ht, hs1, hs2, ht0⟩ := hdec
      subst hr hk ht hs1 hs2 ht0
      have hblk : ∀ position i, position + i * P.etaPackedBytes + P.etaPackedBytes ≤ octets.length →
          (unpackEta P.eta (etaBlock P octets position i)).isSome →
          packEta P.eta ((unpackEta P.eta (etaBlock P octets position i)).getD []) =
            etaBlock P octets position i := by
        intro position i hle hsome
        obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
        rw [hp]
        exact ((unpackEta_eq_some_iff P.eta hP.1 _ (by
          rw [length_sub _ _ _ hle, hE]) (sub_lt hb _ _) p).mp hp).2.2
      unfold encodeSk
      rw [List.map_map, List.map_map, List.map_map]
      simp only [Function.comp_def]
      rw [List.map_congr_left (fun i hi => hblk 128 i (by
          rw [List.mem_range] at hi; rw [hlen]; unfold Params.skSize; nlinarith)
          (hall1 i (List.mem_range.mp hi))),
        List.map_congr_left (fun i hi => hblk (128 + P.l * P.etaPackedBytes) i (by
          rw [List.mem_range] at hi; rw [hlen]; unfold Params.skSize; nlinarith)
          (hall2 i (List.mem_range.mp hi))),
        List.map_congr_left (fun i hi => packT0_unpackT0 _ (length_sub _ _ _ (by
          rw [List.mem_range] at hi; rw [hlen]; unfold Params.skSize; nlinarith)) (sub_lt hb _ _))]
      unfold etaBlock
      rw [flatten_sub_blocks, flatten_sub_blocks]
      rw [flatten_sub_blocks, ← sub_split, ← sub_split, ← sub_split,
        show 32 + 32 + 64 + P.l * P.etaPackedBytes = 128 + P.l * P.etaPackedBytes by ring, sub_three]
      have hfull : sub octets 0 octets.length = octets := by simp [sub]
      conv_rhs => rw [← hfull]
      congr 1
      rw [hlen]; unfold Params.skSize; ring

end OcamlPq.Encoding.Mldsa
