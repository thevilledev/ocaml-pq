import OcamlPq.MLKEMAlg.SampleCBD
import OcamlPq.MLKEMAlg.SampleNTT
import OcamlPq.MLKEMAlg.ConstTime

/-!
# Building blocks verified elsewhere

Two other parts of the project verify the arithmetic layer
(lib/mlkem_engine.ml:105-228: field operations, `poly_add`, `poly_sub`, `ntt`,
`inverse_ntt`, `ntt_mul`, `compress`, `decompress`) and the byte packing
(`encode_12`, `decode_12`, `encode_compressed`, `decode_compressed`). Here
those functions are parameters:

* `SpecPrims`: the FIPS 203 operations at spec level (NTT, NTT⁻¹,
  MultiplyNTTs, ByteEncode₁₂, ByteDecode₁₂, ByteEncode_d ∘ Compress_d,
  Decompress_d ∘ ByteDecode_d).
* `ImplPrims`: the OCaml functions at implementation level.
* `Refines`: the refinement facts that the other parts prove, stated as
  explicit hypotheses. Every theorem that uses them takes `Refines I S` as an
  argument.
* `SpecPrims.Laws`: two spec-level facts: NTT⁻¹ is additive, and
  ByteDecode₁₂ ∘ ByteEncode₁₂ = id (FIPS 203 §4.2.1).
-/

namespace OcamlPq.MLKEMAlg

/-- The spec-level building blocks of FIPS 203. -/
structure SpecPrims where
  /-- Algorithm 9. -/
  NTT : Poly → Poly
  /-- Algorithm 10. -/
  invNTT : Poly → Poly
  /-- Algorithm 11. -/
  multiplyNTTs : Poly → Poly → Poly
  /-- Algorithm 5 with `d = 12`, on coefficients in `ℤ_q`. -/
  byteEncode12 : Poly → Bytes
  /-- Algorithm 6 with `d = 12` (which reduces modulo `q`). -/
  byteDecode12 : Bytes → Poly
  /-- `ByteEncode_d ∘ Compress_d` (Algorithm 5 and eq. 4.7). -/
  compressEncode : ℕ → Poly → Bytes
  /-- `Decompress_d ∘ ByteDecode_d` (Algorithm 6 and eq. 4.8). -/
  decodeDecompress : ℕ → Bytes → Poly

/-- Spec-level facts about the building blocks. -/
structure SpecPrims.Laws (S : SpecPrims) : Prop where
  invNTT_add : ∀ f g, S.invNTT (f + g) = S.invNTT f + S.invNTT g
  byteDecode12_byteEncode12 : ∀ f, S.byteDecode12 (S.byteEncode12 f) = f

/-- The implementation-level building blocks of lib/mlkem_engine.ml. -/
structure ImplPrims where
  /-- `ntt` (lines 170-189). -/
  ntt : IPoly → IPoly
  /-- `inverse_ntt` (lines 191-213). -/
  inverseNtt : IPoly → IPoly
  /-- `ntt_mul` (lines 215-226). -/
  nttMul : IPoly → IPoly → IPoly
  /-- `poly_add` (lines 140-141). -/
  polyAdd : IPoly → IPoly → IPoly
  /-- `poly_sub` (lines 143-144). -/
  polySub : IPoly → IPoly → IPoly
  /-- `encode_12` (lines 228-237). -/
  encode12 : IPoly → Bytes
  /-- `decode_12 ~what s off` (lines 239-249); `none` is its `Error`. -/
  decode12 : Bytes → ℕ → Option IPoly
  /-- `encode_compressed d f` (lines 251-265). -/
  encodeCompressed : ℕ → IPoly → Bytes
  /-- `decode_compressed d s off` (lines 267-283). -/
  decodeCompressed : ℕ → Bytes → ℕ → IPoly

/-- The compression widths the code uses: 1 (messages) and `du`, `dv` of the
    three parameter sets. -/
def Widths : Set ℕ := {1, 4, 5, 10, 11}

/-- The refinement facts proved for the building blocks elsewhere, stated as
    hypotheses. Each says that on canonical inputs the OCaml function computes
    the FIPS 203 operation and returns canonical coefficients, and gives the
    output length (a byte string) or the bytes read (a decoder). -/
structure Refines (I : ImplPrims) (S : SpecPrims) : Prop where
  ntt : ∀ p, Canonical p → Canonical (I.ntt p) ∧ toSpec (I.ntt p) = S.NTT (toSpec p)
  inverseNtt : ∀ p, Canonical p →
    Canonical (I.inverseNtt p) ∧ toSpec (I.inverseNtt p) = S.invNTT (toSpec p)
  nttMul : ∀ p r, Canonical p → Canonical r →
    Canonical (I.nttMul p r) ∧ toSpec (I.nttMul p r) = S.multiplyNTTs (toSpec p) (toSpec r)
  polyAdd : ∀ p r, Canonical p → Canonical r →
    Canonical (I.polyAdd p r) ∧ toSpec (I.polyAdd p r) = toSpec p + toSpec r
  polySub : ∀ p r, Canonical p → Canonical r →
    Canonical (I.polySub p r) ∧ toSpec (I.polySub p r) = toSpec p - toSpec r
  encode12 : ∀ p, Canonical p →
    I.encode12 p = S.byteEncode12 (toSpec p) ∧ (I.encode12 p).length = 384
  /-- `decode_12` reads the 384 bytes at `off`. It succeeds iff they pass the
      FIPS 203 §7.2 modulus check, and then returns their decoding. -/
  decode12 : ∀ s off, off + 384 ≤ s.length →
    (∀ p, I.decode12 s off = some p →
      Canonical p ∧ toSpec p = S.byteDecode12 (stringSub s off 384)) ∧
    ((I.decode12 s off).isSome ↔
      S.byteEncode12 (S.byteDecode12 (stringSub s off 384)) = stringSub s off 384)
  encodeCompressed : ∀ d ∈ Widths, ∀ p, Canonical p →
    I.encodeCompressed d p = S.compressEncode d (toSpec p) ∧
      (I.encodeCompressed d p).length = 32 * d
  decodeCompressed : ∀ d ∈ Widths, ∀ s off, off + 32 * d ≤ s.length →
    Canonical (I.decodeCompressed d s off) ∧
      toSpec (I.decodeCompressed d s off) = S.decodeDecompress d (stringSub s off (32 * d))

theorem Params.Valid.widths {P : Params} (h : P.Valid) : P.du ∈ Widths ∧ P.dv ∈ Widths := by
  rcases h with rfl | rfl | rfl <;> simp [Widths, mlkem512, mlkem768, mlkem1024]

/-- Canonical representatives are determined by their residues. -/
theorem Canonical.eq_of_toSpec {p p' : IPoly} (hp : Canonical p) (hp' : Canonical p')
    (h : toSpec p = toSpec p') : p = p' := by
  funext i
  have h1 := congrFun h i
  simp only [toSpec] at h1
  have := (ZMod.intCast_eq_intCast_iff' (p i) (p' i) q).1 h1
  rw [Int.emod_eq_of_lt (hp i).1 (hp i).2, Int.emod_eq_of_lt (hp' i).1 (hp' i).2] at this
  exact this

end OcamlPq.MLKEMAlg
