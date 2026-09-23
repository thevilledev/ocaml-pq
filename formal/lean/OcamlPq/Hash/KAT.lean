import OcamlPq.Hash.Sponge
import OcamlPq.Hash.HmacMgf1

/-!
# Known-answer tests, at the level of the specifications

Each model evaluation is kernel-checked (`decide +kernel`, no `native_decide`),
and the equivalence theorems then carry the published digest over to the
FIPS 202 / FIPS 180-4 / FIPS 198-1 transcriptions. So these are theorems about
the *specifications* (`FIPS202.SHA3_256 [] = …` etc.), which validates the
transcriptions against the published answers.

Sources: FIPS 202 / NIST CSRC example values (SHA3-256(""), SHA3-512(""),
SHAKE128("", 256 bits), SHAKE256("", 256 bits)), FIPS 180-4 / NIST examples
(SHA-256("abc"), the 448-bit two-block message, SHA-512("abc"), the 896-bit
two-block message), RFC 4231 test case 1 (HMAC-SHA-256/512). The values were
cross-checked with Python's `hashlib`/`hmac`.
-/

namespace OcamlPq.Hash.KAT

open FIPS202 FIPS180 Keccak Sha2

/-! ## FIPS 202 -/

set_option maxRecDepth 100000 in
theorem sha3_256_empty_model : sha3_256 [] =
    [167, 255, 198, 248, 191, 30, 215, 102, 81, 193, 71, 86, 160, 97, 214, 98, 245, 128, 255, 77,
     228, 59, 73, 250, 130, 216, 10, 75, 128, 248, 67, 74] := by
  decide +kernel

/-- `SHA3-256("") = a7ffc6f8…f8434a`. -/
theorem SHA3_256_empty : SHA3_256 [] = bytesToBits
    [167, 255, 198, 248, 191, 30, 215, 102, 81, 193, 71, 86, 160, 97, 214, 98, 245, 128, 255, 77,
     228, 59, 73, 250, 130, 216, 10, 75, 128, 248, 67, 74] := by
  rw [← sha3_256_empty_model, sha3_256_eq]; rfl

set_option maxRecDepth 100000 in
theorem sha3_512_empty_model : sha3_512 [] =
    [166, 159, 115, 204, 162, 58, 154, 197, 200, 181, 103, 220, 24, 90, 117, 110, 151, 201, 130,
     22, 79, 226, 88, 89, 224, 209, 220, 193, 71, 92, 128, 166, 21, 178, 18, 58, 241, 245, 249,
     76, 17, 227, 233, 64, 44, 58, 197, 88, 245, 0, 25, 157, 149, 182, 211, 227, 1, 117, 133,
     134, 40, 29, 205, 38] := by
  decide +kernel

/-- `SHA3-512("") = a69f73cc…281dcd26`. -/
theorem SHA3_512_empty : SHA3_512 [] = bytesToBits
    [166, 159, 115, 204, 162, 58, 154, 197, 200, 181, 103, 220, 24, 90, 117, 110, 151, 201, 130,
     22, 79, 226, 88, 89, 224, 209, 220, 193, 71, 92, 128, 166, 21, 178, 18, 58, 241, 245, 249,
     76, 17, 227, 233, 64, 44, 58, 197, 88, 245, 0, 25, 157, 149, 182, 211, 227, 1, 117, 133,
     134, 40, 29, 205, 38] := by
  rw [← sha3_512_empty_model, sha3_512_eq]; rfl

set_option maxRecDepth 100000 in
theorem shake128_empty_model : shake128 32 [] =
    [127, 156, 43, 164, 232, 143, 130, 125, 97, 96, 69, 80, 118, 5, 133, 62, 215, 59, 128, 147,
     246, 239, 188, 136, 235, 26, 110, 172, 250, 102, 239, 38] := by
  decide +kernel

/-- `SHAKE128("", 256) = 7f9c2ba4…fa66ef26`. -/
theorem SHAKE128_empty : SHAKE128 [] 256 = bytesToBits
    [127, 156, 43, 164, 232, 143, 130, 125, 97, 96, 69, 80, 118, 5, 133, 62, 215, 59, 128, 147,
     246, 239, 188, 136, 235, 26, 110, 172, 250, 102, 239, 38] := by
  rw [← shake128_empty_model, shake128_eq]; rfl

set_option maxRecDepth 100000 in
theorem shake256_empty_model : shake256 32 [] =
    [70, 185, 221, 43, 11, 168, 141, 19, 35, 59, 63, 235, 116, 62, 235, 36, 63, 205, 82, 234,
     98, 184, 27, 130, 181, 12, 39, 100, 110, 213, 118, 47] := by
  decide +kernel

/-- `SHAKE256("", 256) = 46b9dd2b…d5762f`. -/
theorem SHAKE256_empty : SHAKE256 [] 256 = bytesToBits
    [70, 185, 221, 43, 11, 168, 141, 19, 35, 59, 63, 235, 116, 62, 235, 36, 63, 205, 82, 234,
     98, 184, 27, 130, 181, 12, 39, 100, 110, 213, 118, 47] := by
  rw [← shake256_empty_model, shake256_eq]; rfl

set_option maxRecDepth 100000 in
/-- Two squeeze blocks (200 > 168 output bytes). -/
theorem shake128_empty_200_model : shake128 200 [] =
    [127, 156, 43, 164, 232, 143, 130, 125, 97, 96, 69, 80, 118, 5, 133, 62, 215, 59, 128, 147,
     246, 239, 188, 136, 235, 26, 110, 172, 250, 102, 239, 38, 60, 177, 238, 169, 136, 0, 75, 147,
     16, 60, 251, 10, 238, 253, 42, 104, 110, 1, 250, 74, 88, 232, 163, 99, 156, 168, 161, 227,
     249, 174, 87, 226, 53, 184, 204, 135, 60, 35, 220, 98, 184, 210, 96, 22, 154, 250, 47, 117,
     171, 145, 106, 88, 217, 116, 145, 136, 53, 210, 94, 106, 67, 80, 133, 178, 186, 223, 214, 223,
     170, 195, 89, 165, 239, 187, 123, 204, 75, 89, 213, 56, 223, 154, 4, 48, 46, 16, 200, 188,
     28, 191, 26, 11, 58, 81, 32, 234, 23, 205, 167, 207, 173, 118, 95, 86, 35, 71, 77, 54,
     140, 204, 168, 175, 0, 7, 205, 159, 94, 76, 132, 159, 22, 122, 88, 11, 20, 170, 189, 239,
     174, 231, 238, 244, 124, 176, 252, 169, 118, 123, 225, 253, 166, 148, 25, 223, 185, 39, 233, 223,
     7, 52, 139, 25, 102, 145, 171, 174, 181, 128, 179, 45, 239, 88, 83, 139, 141, 35, 248, 119] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A 135-byte message: `rem = rate − 1`, the suffix `0x06` and the final
`0x80` land in the same byte (`0x86`). -/
theorem sha3_256_135_model : sha3_256 ((List.range 135).map UInt8.ofNat) =
    [253, 237, 143, 217, 214, 85, 28, 96, 30, 235, 59, 124, 107, 197, 229, 207, 216, 170, 209,
     208, 21, 183, 233, 170, 169, 201, 185, 71, 82, 49, 213, 226] := by
  decide +kernel

theorem SHA3_256_135 : SHA3_256 (bytesToBits ((List.range 135).map UInt8.ofNat)) = bytesToBits
    [253, 237, 143, 217, 214, 85, 28, 96, 30, 235, 59, 124, 107, 197, 229, 207, 216, 170, 209,
     208, 21, 183, 233, 170, 169, 201, 185, 71, 82, 49, 213, 226] := by
  rw [← sha3_256_135_model, sha3_256_eq]

/-! ## FIPS 180-4 -/

set_option maxRecDepth 100000 in
theorem sha256_abc_model : sha256 [97, 98, 99] =
    [186, 120, 22, 191, 143, 1, 207, 234, 65, 65, 64, 222, 93, 174, 34, 35, 176, 3, 97, 163,
     150, 23, 122, 156, 180, 16, 255, 97, 242, 0, 21, 173] := by
  decide +kernel

/-- `SHA-256("abc") = ba7816bf…f20015ad`. -/
theorem SHA256_abc : SHA256 (bytesToBitsBE [97, 98, 99]) = bytesToBitsBE
    [186, 120, 22, 191, 143, 1, 207, 234, 65, 65, 64, 222, 93, 174, 34, 35, 176, 3, 97, 163,
     150, 23, 122, 156, 180, 16, 255, 97, 242, 0, 21, 173] := by
  rw [← sha256_abc_model, sha256_eq]

/-- The 448-bit message `abcdbcdecdef…nopq` (FIPS 180-4 example; two blocks). -/
def msg448 : List UInt8 := [97, 98, 99, 100, 98, 99, 100, 101, 99, 100, 101, 102, 100, 101, 102,
  103, 101, 102, 103, 104, 102, 103, 104, 105, 103, 104, 105, 106, 104, 105, 106, 107, 105, 106,
  107, 108, 106, 107, 108, 109, 107, 108, 109, 110, 108, 109, 110, 111, 109, 110, 111, 112, 110,
  111, 112, 113]

set_option maxRecDepth 100000 in
theorem sha256_448_model : sha256 msg448 =
    [36, 141, 106, 97, 210, 6, 56, 184, 229, 192, 38, 147, 12, 62, 96, 57, 163, 60, 228, 89, 100,
     255, 33, 103, 246, 236, 237, 212, 25, 219, 6, 193] := by
  decide +kernel

theorem SHA256_448 : SHA256 (bytesToBitsBE msg448) = bytesToBitsBE
    [36, 141, 106, 97, 210, 6, 56, 184, 229, 192, 38, 147, 12, 62, 96, 57, 163, 60, 228, 89, 100,
     255, 33, 103, 246, 236, 237, 212, 25, 219, 6, 193] := by
  rw [← sha256_448_model, sha256_eq]

set_option maxRecDepth 100000 in
theorem sha512_abc_model : sha512 [97, 98, 99] =
    [221, 175, 53, 161, 147, 97, 122, 186, 204, 65, 115, 73, 174, 32, 65, 49, 18, 230, 250, 78,
     137, 169, 126, 162, 10, 158, 238, 230, 75, 85, 211, 154, 33, 146, 153, 42, 39, 79, 193, 168,
     54, 186, 60, 35, 163, 254, 235, 189, 69, 77, 68, 35, 100, 60, 232, 14, 42, 154, 201, 79,
     165, 76, 164, 159] := by
  decide +kernel

/-- `SHA-512("abc") = ddaf35a1…a54ca49f`. -/
theorem SHA512_abc : SHA512 (bytesToBitsBE [97, 98, 99]) = bytesToBitsBE
    [221, 175, 53, 161, 147, 97, 122, 186, 204, 65, 115, 73, 174, 32, 65, 49, 18, 230, 250, 78,
     137, 169, 126, 162, 10, 158, 238, 230, 75, 85, 211, 154, 33, 146, 153, 42, 39, 79, 193, 168,
     54, 186, 60, 35, 163, 254, 235, 189, 69, 77, 68, 35, 100, 60, 232, 14, 42, 154, 201, 79,
     165, 76, 164, 159] := by
  rw [← sha512_abc_model, sha512_eq _ (by norm_num)]

/-- The 896-bit message `abcdefghbcdefghi…nopqrstu` (FIPS 180-4 example; two blocks). -/
def msg896 : List UInt8 := (List.range 14).flatMap fun i => (List.range 8).map fun j =>
  UInt8.ofNat (97 + i + j)

set_option maxRecDepth 100000 in
theorem sha512_896_model : sha512 msg896 =
    [142, 149, 155, 117, 218, 227, 19, 218, 140, 244, 247, 40, 20, 252, 20, 63, 143, 119, 121,
     198, 235, 159, 127, 161, 114, 153, 174, 173, 182, 136, 144, 24, 80, 29, 40, 158, 73, 0, 247,
     228, 51, 27, 153, 222, 196, 181, 67, 58, 199, 211, 41, 238, 182, 221, 38, 84, 94, 150, 229,
     91, 135, 75, 233, 9] := by
  decide +kernel

theorem SHA512_896 : SHA512 (bytesToBitsBE msg896) = bytesToBitsBE
    [142, 149, 155, 117, 218, 227, 19, 218, 140, 244, 247, 40, 20, 252, 20, 63, 143, 119, 121,
     198, 235, 159, 127, 161, 114, 153, 174, 173, 182, 136, 144, 24, 80, 29, 40, 158, 73, 0, 247,
     228, 51, 27, 153, 222, 196, 181, 67, 58, 199, 211, 41, 238, 182, 221, 38, 84, 94, 150, 229,
     91, 135, 75, 233, 9] := by
  rw [← sha512_896_model, sha512_eq _ (by decide)]

/-! ## FIPS 198-1 HMAC, RFC 4231 test case 1 -/

/-- `"Hi There"`. -/
def hiThere : List UInt8 := [72, 105, 32, 84, 104, 101, 114, 101]

set_option maxRecDepth 100000 in
theorem hmacSha256_rfc4231_1_model : hmacSha256 (List.replicate 20 0x0b) hiThere =
    [176, 52, 76, 97, 216, 219, 56, 83, 92, 168, 175, 206, 175, 11, 241, 43, 136, 29, 194, 0,
     201, 131, 61, 167, 38, 233, 55, 108, 46, 50, 207, 247] := by
  decide +kernel

/-- RFC 4231 test case 1: `HMAC-SHA-256(0x0b × 20, "Hi There") = b0344c61…2e32cff7`. -/
theorem HMAC_SHA256_rfc4231_1 : FIPS198.HMAC SHA256Bytes 64 (List.replicate 20 0x0b) hiThere =
    [176, 52, 76, 97, 216, 219, 56, 83, 92, 168, 175, 206, 175, 11, 241, 43, 136, 29, 194, 0,
     201, 131, 61, 167, 38, 233, 55, 108, 46, 50, 207, 247] := by
  rw [← hmacSha256_eq, hmacSha256_rfc4231_1_model]

set_option maxRecDepth 100000 in
theorem hmacSha512_rfc4231_1_model : hmacSha512 (List.replicate 20 0x0b) hiThere =
    [135, 170, 124, 222, 165, 239, 97, 157, 79, 240, 180, 36, 26, 29, 108, 176, 35, 121, 244,
     226, 206, 78, 194, 120, 122, 208, 179, 5, 69, 225, 124, 222, 218, 168, 51, 183, 214, 184,
     167, 2, 3, 139, 39, 78, 174, 163, 244, 228, 190, 157, 145, 78, 235, 97, 241, 112, 46, 105,
     108, 32, 58, 18, 104, 84] := by
  decide +kernel

/-- RFC 4231 test case 1: `HMAC-SHA-512(0x0b × 20, "Hi There") = 87aa7cde…3a126854`. -/
theorem HMAC_SHA512_rfc4231_1 : FIPS198.HMAC SHA512Bytes 128 (List.replicate 20 0x0b) hiThere =
    [135, 170, 124, 222, 165, 239, 97, 157, 79, 240, 180, 36, 26, 29, 108, 176, 35, 121, 244,
     226, 206, 78, 194, 120, 122, 208, 179, 5, 69, 225, 124, 222, 218, 168, 51, 183, 214, 184,
     167, 2, 3, 139, 39, 78, 174, 163, 244, 228, 190, 157, 145, 78, 235, 97, 241, 112, 46, 105,
     108, 32, 58, 18, 104, 84] := by
  rw [← hmacSha512_eq _ _ (by simp) (by simp [hiThere]), hmacSha512_rfc4231_1_model]

end OcamlPq.Hash.KAT
