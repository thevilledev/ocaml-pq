import OcamlPq.MLKEMAlg.Spec

/-!
# Models of K-PKE, the KEM and key handling in lib/mlkem_engine.ml

Models of lib/mlkem_engine.ml lines 336-525, parameterised by the parameter
set `P`, the Keccak functions `K`, and the building blocks `I`.

* Records (`encapsulation_key`, `decapsulation_key`) are Lean structures; an
  OCaml array of length `k` is `Fin k → α`.
* `Array.init k (fun _ -> sample_secret ())`, whose closure increments a
  `nonce` reference, is `arrayInitST` threading the counter.
* `Bytes.create` is an arbitrary buffer passed as an argument (`g`, `g₁`,
  `g₂`). The theorems hold for every such buffer.
* `sample_ntt` is its total extension `sampleNttTotal` (see `SampleNTT.lean`).
-/

namespace OcamlPq.MLKEMAlg.Impl

open OcamlPq.MLKEMAlg

/-- The OCaml `error` type (lib/mlkem_engine.ml:1-3). -/
inductive MlkemError
  | invalidLength (what : String) (expected actual : ℕ)
  | invalidEncoding (msg : String)
  deriving DecidableEq

/-- `invalid_length what expected actual` (lib/mlkem_engine.ml:99-100). -/
def invalidLength {α : Type} (what : String) (expected actual : ℕ) : Except MlkemError α :=
  .error (.invalidLength what expected actual)

/-- `encapsulation_key` (lib/mlkem_engine.ml:79-85). -/
structure EncapsulationKey (k : ℕ) where
  t : Fin k → IPoly
  a : Fin k → Fin k → IPoly
  rho : Bytes
  h : Bytes
  encoded : Bytes

/-- `decapsulation_key` (lib/mlkem_engine.ml:87-92). -/
structure DecapsulationKey (k : ℕ) where
  seed : Option Bytes
  z : Bytes
  s : Fin k → IPoly
  ek : EncapsulationKey k

variable (P : Params) (K : Keccak) (I : ImplPrims)

/-- `decode_12 ~what s off` with its error value (lib/mlkem_engine.ml:239-249). -/
def decode12E (what : String) (s : Bytes) (off : ℕ) : Except MlkemError IPoly :=
  match I.decode12 s off with
  | some p => .ok p
  | none => .error (.invalidEncoding (what ++ " contains an unreduced coefficient"))

/-- `decode_message s = decode_compressed 1 s 0` (lib/mlkem_engine.ml:286). -/
def decodeMessage (s : Bytes) : IPoly := I.decodeCompressed 1 s 0

/-- `encode_message f = encode_compressed 1 f` (lib/mlkem_engine.ml:285). -/
def encodeMessage (f : IPoly) : Bytes := I.encodeCompressed 1 f

/-- The matrix `Array.init k (fun row -> Array.init k (fun col -> sample_ntt rho col row))`
    (lib/mlkem_engine.ml:356 and 367). -/
noncomputable def matrix (rho : Bytes) : Fin P.k → Fin P.k → IPoly :=
  fun row col => sampleNttTotal K rho col.val row.val

/-- `encode_ek t rho` (lib/mlkem_engine.ml:336-342). -/
def encodeEk (g : ℕ → Byte) (t : Fin P.k → IPoly) (rho : Bytes) : Bytes :=
  let out := blitChunks Params.encodingSize12 0 (fun i => I.encode12 (t i)) g
  let out := blitString rho 0 out (P.k * Params.encodingSize12) 32
  bufToList out 0 P.ekSize

/-- The recursive `parse acc i` loop of `parse_ek` (lib/mlkem_engine.ml:348-353)
    and `parse_s` of `decapsulation_key_of_expanded` (lines 424-429). OCaml
    tests `i = k`; the model recurses on `remaining = k - i`, which is the same
    loop since `i` starts at 0 and increases by 1. -/
def parseLoop (what : String) (s : Bytes) : (remaining : ℕ) → List IPoly → ℕ →
    Except MlkemError (List IPoly)
  | 0, acc, _ => .ok acc.reverse
  | r + 1, acc, i =>
    match decode12E I what s (i * Params.encodingSize12) with
    | .error e => .error e
    | .ok p => parseLoop what s r (p :: acc) (i + 1)

/-- `Array.of_list l` read as an array of length `k`. -/
def arrayOfList {k : ℕ} (l : List IPoly) : Fin k → IPoly := fun i => l.getD i.val polyZero

/-- `parse_ek encoded` (lib/mlkem_engine.ml:344-360). -/
noncomputable def parseEk (encoded : Bytes) : Except MlkemError (EncapsulationKey P.k) :=
  if encoded.length ≠ P.ekSize then
    invalidLength "encapsulation key" P.ekSize encoded.length
  else
    match parseLoop I "encapsulation key" encoded P.k [] 0 with
    | .error e => .error e
    | .ok tl =>
      let t : Fin P.k → IPoly := arrayOfList tl
      let rho := stringSub encoded (P.k * Params.encodingSize12) 32
      let a := matrix P K rho
      .ok { t, a, rho, h := K.sha3_256 encoded, encoded }

/-- `keygen_internal ~d ~z` (lib/mlkem_engine.ml:362-385). -/
noncomputable def keygenInternal (g : ℕ → Byte) (d z : Bytes) :
    Except MlkemError (DecapsulationKey P.k) :=
  if d.length ≠ 32 then invalidLength "key-generation seed d" 32 d.length
  else if z.length ≠ 32 then invalidLength "implicit-rejection seed z" 32 z.length
  else
    let expanded := K.sha3_512 (d ++ byteString P.k)
    let rho := stringSub expanded 0 32
    let sigma := stringSub expanded 32 32
    let a := matrix P K rho
    let sampleSecret : ℕ → IPoly × ℕ := fun nonce => (I.ntt (sampleCbd K P.eta1 sigma nonce), nonce + 1)
    let sr := arrayInitST P.k sampleSecret 0
    let er := arrayInitST P.k sampleSecret sr.2
    let s := sr.1
    let e := er.1
    let t : Fin P.k → IPoly := fun row =>
      (List.finRange P.k).foldl (fun total col => I.polyAdd total (I.nttMul (a row col) (s col))) (e row)
    let encoded := encodeEk P I g t rho
    let ek : EncapsulationKey P.k := { t, a, rho, h := K.sha3_256 encoded, encoded }
    .ok { seed := some (d ++ z), z, s, ek }

/-- `decapsulation_key_of_seed seed` (lib/mlkem_engine.ml:387-390). -/
noncomputable def decapsulationKeyOfSeed (g : ℕ → Byte) (seed : Bytes) :
    Except MlkemError (DecapsulationKey P.k) :=
  if seed.length ≠ Params.seedSize then invalidLength "decapsulation key seed" Params.seedSize seed.length
  else keygenInternal P K I g (stringSub seed 0 32) (stringSub seed 32 32)

/-- `decapsulation_key_to_seed dk` (lib/mlkem_engine.ml:392). -/
def decapsulationKeyToSeed {k : ℕ} (dk : DecapsulationKey k) : Option Bytes :=
  dk.seed.map (fun x => stringSub x 0 x.length)

/-- `encapsulation_key_to_octets ek` (lib/mlkem_engine.ml:396). -/
def encapsulationKeyToOctets (ek : EncapsulationKey P.k) : Bytes := stringSub ek.encoded 0 P.ekSize

/-- `decapsulation_key_to_expanded dk` (lib/mlkem_engine.ml:398-406). -/
def decapsulationKeyToExpanded (g : ℕ → Byte) (dk : DecapsulationKey P.k) : Bytes :=
  let out := blitChunks Params.encodingSize12 0 (fun i => I.encode12 (dk.s i)) g
  let out := blitString dk.ek.encoded 0 out (P.k * Params.encodingSize12) P.ekSize
  let out := blitString dk.ek.h 0 out (P.k * Params.encodingSize12 + P.ekSize) 32
  let out := blitString dk.z 0 out (P.dkSize - 32) 32
  bufToList out 0 P.dkSize

/-- `decapsulation_key_of_expanded encoded` (lib/mlkem_engine.ml:419-445). -/
noncomputable def decapsulationKeyOfExpanded (encoded : Bytes) :
    Except MlkemError (DecapsulationKey P.k) :=
  if encoded.length ≠ P.dkSize then
    invalidLength "expanded decapsulation key" P.dkSize encoded.length
  else
    match parseLoop I "expanded decapsulation key" encoded P.k [] 0 with
    | .error e => .error e
    | .ok sl =>
      let s : Fin P.k → IPoly := arrayOfList sl
      let ekOffset := P.k * Params.encodingSize12
      let ekBytes := stringSub encoded ekOffset P.ekSize
      match parseEk P K I ekBytes with
      | .error e => .error e
      | .ok ek =>
        let hOffset := ekOffset + P.ekSize
        let h := stringSub encoded hOffset 32
        if ctEqual h ek.h ≠ 1 then
          .error (.invalidEncoding "expanded decapsulation key has inconsistent H(ek)")
        else
          let z := stringSub encoded (hOffset + 32) 32
          .ok { seed := none, z, s, ek }

/-- `ciphertext_of_octets encoded` (lib/mlkem_engine.ml:447-450). -/
def ciphertextOfOctets (encoded : Bytes) : Except MlkemError Bytes :=
  if encoded.length ≠ P.ctSize then invalidLength "ciphertext" P.ctSize encoded.length
  else .ok (stringSub encoded 0 P.ctSize)

/-- `pke_encrypt ek message randomness` (lib/mlkem_engine.ml:455-492). -/
def pkeEncrypt (g : ℕ → Byte) (ek : EncapsulationKey P.k) (message randomness : Bytes) : Bytes :=
  let sampleNttSecret : ℕ → IPoly × ℕ :=
    fun nonce => (I.ntt (sampleCbd K P.eta1 randomness nonce), nonce + 1)
  let sampleRingSecret : ℕ → IPoly × ℕ :=
    fun nonce => (sampleCbd K P.eta2 randomness nonce, nonce + 1)
  let rr := arrayInitST P.k sampleNttSecret 0
  let e1r := arrayInitST P.k sampleRingSecret rr.2
  let e2r := sampleRingSecret e1r.2
  let r := rr.1
  let e1 := e1r.1
  let e2 := e2r.1
  let u : Fin P.k → IPoly := fun col =>
    (List.finRange P.k).foldl
      (fun total row => I.polyAdd total (I.inverseNtt (I.nttMul (ek.a row col) (r row)))) (e1 col)
  let vNtt := (List.finRange P.k).foldl (fun acc i => I.polyAdd acc (I.nttMul (ek.t i) (r i))) polyZero
  let v := I.polyAdd (I.polyAdd (I.inverseNtt vNtt) e2) (decodeMessage I message)
  let out := blitChunks P.encodingSizeU 0 (fun i => I.encodeCompressed P.du (u i)) g
  let out := blitString (I.encodeCompressed P.dv v) 0 out (P.k * P.encodingSizeU) P.encodingSizeV
  bufToList out 0 P.ctSize

/-- `encapsulate_internal ek ~randomness` (lib/mlkem_engine.ml:494-500). -/
def encapsulateInternal (g : ℕ → Byte) (ek : EncapsulationKey P.k) (randomness : Bytes) :
    Except MlkemError (Bytes × Bytes) :=
  if randomness.length ≠ 32 then invalidLength "encapsulation randomness" 32 randomness.length
  else
    let gg := K.sha3_512 (randomness ++ ek.h)
    let secret := stringSub gg 0 32
    let coins := stringSub gg 32 32
    .ok (pkeEncrypt P K I g ek randomness coins, secret)

/-- `pke_decrypt dk ciphertext` (lib/mlkem_engine.ml:502-509). -/
def pkeDecrypt (dk : DecapsulationKey P.k) (ciphertext : Bytes) : Bytes :=
  let u : Fin P.k → IPoly := fun i => I.decodeCompressed P.du ciphertext (i.val * P.encodingSizeU)
  let v := I.decodeCompressed P.dv ciphertext (P.k * P.encodingSizeU)
  let mask := (List.finRange P.k).foldl
    (fun acc i => I.polyAdd acc (I.nttMul (dk.s i) (I.ntt (u i)))) polyZero
  encodeMessage I (I.polySub v (I.inverseNtt mask))

/-- `decapsulate dk ciphertext` (lib/mlkem_engine.ml:520-526). `g₁` and `g₂`
    are the uninitialised buffers of `pke_encrypt` and `select_secret`. -/
def decapsulate (g₁ g₂ : ℕ → Byte) (dk : DecapsulationKey P.k) (ciphertext : Bytes) : Bytes :=
  let message := pkeDecrypt P I dk ciphertext
  let gg := K.sha3_512 (message ++ dk.ek.h)
  let candidate := stringSub gg 0 32
  let coins := stringSub gg 32 32
  let rejection := K.shake256Out 32 (dk.z ++ ciphertext)
  let expected := pkeEncrypt P K I g₁ dk.ek message coins
  selectSecret g₂ (ctEqual ciphertext expected) candidate rejection

end OcamlPq.MLKEMAlg.Impl
