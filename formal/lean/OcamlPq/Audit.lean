import OcamlPq

/-!
# Axiom audit

Prints the axioms that the headline theorems of each area depend on. Every
line should list only Lean's standard axioms, `propext`, `Classical.choice`,
and `Quot.sound`; `Lean.ofReduceBool` would reveal a `native_decide` or
`bv_decide` proof, and `sorryAx` an incomplete one. `formal/check.sh` runs this
file and fails if any other axiom appears.
-/

-- ML-KEM arithmetic: field operations, compression, NTT.
#print axioms OcamlPq.MLKEM.fieldReduce_eq_emod
#print axioms OcamlPq.MLKEM.compress_eq_spec
#print axioms OcamlPq.MLKEM.decompress_eq_spec
#print axioms OcamlPq.MLKEM.compress_decompress_error
#print axioms OcamlPq.MLKEM.ntt_refines
#print axioms OcamlPq.MLKEM.inverseNtt_refines
#print axioms OcamlPq.MLKEM.nttMul_refines
#print axioms OcamlPq.MLKEM.fipsNtt_crt
#print axioms OcamlPq.MLKEM.fipsNttInv_multiplyNTTs
#print axioms OcamlPq.MLKEM.ocaml_ntt_mul_correct
#print axioms OcamlPq.MLKEM.ocaml_inverseNtt_ntt

-- ML-KEM sampling, K-PKE, and the KEM.
#print axioms OcamlPq.MLKEMAlg.sampleCbd_spec
#print axioms OcamlPq.MLKEMAlg.sampleNtt_spec
#print axioms OcamlPq.MLKEMAlg.ctEqual_spec
#print axioms OcamlPq.MLKEMAlg.selectSecret_spec
#print axioms OcamlPq.MLKEMAlg.pkeEncrypt_refines
#print axioms OcamlPq.MLKEMAlg.pkeDecrypt_refines
#print axioms OcamlPq.MLKEMAlg.keygenInternal_refines
#print axioms OcamlPq.MLKEMAlg.encapsulateInternal_refines
#print axioms OcamlPq.MLKEMAlg.decapsulate_refines
#print axioms OcamlPq.MLKEMAlg.decapsulate_select
#print axioms OcamlPq.MLKEMAlg.parseEk_ok_iff
#print axioms OcamlPq.MLKEMAlg.impl_mlkem_correct

-- ML-DSA arithmetic: modular arithmetic, NTT, rounding, hints, signer checks.
#print axioms OcamlPq.MLDSA.mulMod_eq
#print axioms OcamlPq.MLDSA.zetas_eq
#print axioms OcamlPq.MLDSA.inverseN_eq
#print axioms OcamlPq.MLDSA.ntt_refines
#print axioms OcamlPq.MLDSA.inverseNtt_pointwise
#print axioms OcamlPq.MLDSA.power2round_eq_spec
#print axioms OcamlPq.MLDSA.decompose_eq_spec
#print axioms OcamlPq.MLDSA.useHint_eq_spec
#print axioms OcamlPq.MLDSA.useHint_makeHint
#print axioms OcamlPq.MLDSA.makeHint_eq_spec
#print axioms OcamlPq.MLDSA.r0_reject_iff
#print axioms OcamlPq.MLDSA.highBits_of_not_reject
#print axioms OcamlPq.MLDSA.hint_eq_spec
#print axioms OcamlPq.MLDSA.signAttempt_eq_spec
#print axioms OcamlPq.MLDSA.verify_recovers_w1_of_accepted

-- ML-DSA sampling, key generation, signing loop, and interface.
#print axioms OcamlPq.MLDSAAlg.uniformPolynomial_returns_iff
#print axioms OcamlPq.MLDSAAlg.etaPolynomial_returns_iff
#print axioms OcamlPq.MLDSAAlg.challengePolynomial_returns_iff
#print axioms OcamlPq.MLDSAAlg.sampleInBall_output
#print axioms OcamlPq.MLDSAAlg.nonce_lt
#print axioms OcamlPq.MLDSAAlg.mask_inputs_injective
#print axioms OcamlPq.MLDSAAlg.attempt_eq_alg7
#print axioms OcamlPq.MLDSAAlg.loop_bound_821
#print axioms OcamlPq.MLDSAAlg.keypairFromSeed_eq
#print axioms OcamlPq.MLDSAAlg.generate_eq
#print axioms OcamlPq.MLDSAAlg.signMuWithRandomness_eq
#print axioms OcamlPq.MLDSAAlg.mldsaSign_eq
#print axioms OcamlPq.MLDSAAlg.verify_eq
#print axioms OcamlPq.MLDSAAlg.buildSigningKey_ok_iff

-- Byte encodings of ML-KEM and ML-DSA.
#print axioms OcamlPq.Encoding.Packer.packCodes_eq_spec
#print axioms OcamlPq.Encoding.Packer.unpackCodes_eq_spec
#print axioms OcamlPq.Encoding.Packer.unpackCodes_packCodes
#print axioms OcamlPq.Encoding.Packer.packCodes_unpackCodes
#print axioms OcamlPq.Encoding.Mlkem.decode12_eq_some_iff
#print axioms OcamlPq.Encoding.Mlkem.modulus_check_iff
#print axioms OcamlPq.Encoding.Mlkem.encodeCompressed_eq
#print axioms OcamlPq.Encoding.Mlkem.decodeCompressed_eq
#print axioms OcamlPq.Encoding.Mldsa.unpackEta_eq_some_iff
#print axioms OcamlPq.Encoding.Hint.decodeHintWith_eq
#print axioms OcamlPq.Encoding.Hint.decode_encode
#print axioms OcamlPq.Encoding.Hint.encode_decode
#print axioms OcamlPq.Encoding.Hint.weight_le_of_decode
#print axioms OcamlPq.Encoding.Mldsa.encodeSig_decodeSig

-- SLH-DSA.
#print axioms OcamlPq.SLHDSA.initChecks_all
#print axioms OcamlPq.SLHDSA.Base2b.messageToForsIndices_eq
#print axioms OcamlPq.SLHDSA.Base2b.messageToForsIndices_platform
#print axioms OcamlPq.SLHDSA.Base2b.chainLengths_eq
#print axioms OcamlPq.SLHDSA.Treehash.treehash_spec
#print axioms OcamlPq.SLHDSA.Treehash.computeRoot_treehash
#print axioms OcamlPq.SLHDSA.WOTS.fipsWots_correct
#print axioms OcamlPq.SLHDSA.FORS.forsSign_eq
#print axioms OcamlPq.SLHDSA.addressFull_eq
#print axioms OcamlPq.SLHDSA.addressCompressed_eq
#print axioms OcamlPq.SLHDSA.Hypertree.signLayers_htSign
#print axioms OcamlPq.SLHDSA.Hypertree.verifyLayers_htVerify
#print axioms OcamlPq.SLHDSA.Top.keypairFromSeed_eq
#print axioms OcamlPq.SLHDSA.Top.signFormatted_eq
#print axioms OcamlPq.SLHDSA.Top.verifyFormatted_eq
#print axioms OcamlPq.SLHDSA.Top.verify_sign

-- Hash primitives: Keccak-f[1600] and the sponge, SHA-2, HMAC, MGF1.
#print axioms OcamlPq.Hash.Keccak.permute_eq_KeccakF
#print axioms OcamlPq.Hash.Keccak.roundConstants_eq_RC
#print axioms OcamlPq.Hash.Keccak.rho_eq
#print axioms OcamlPq.Hash.Keccak.pi_position
#print axioms OcamlPq.Hash.Keccak.spongeWith_eq
#print axioms OcamlPq.Hash.Keccak.sha3_256_eq
#print axioms OcamlPq.Hash.Keccak.sha3_512_eq
#print axioms OcamlPq.Hash.Keccak.shake128_eq
#print axioms OcamlPq.Hash.Keccak.shake256_eq
#print axioms OcamlPq.Hash.Keccak.shake128_prefix
#print axioms OcamlPq.Hash.Keccak.shake256_prefix
#print axioms OcamlPq.Hash.Keccak.sponge_final_state
#print axioms OcamlPq.Hash.Keccak.fips202Shake128_neg
#print axioms OcamlPq.Hash.Sha2.sha256Constants_eq
#print axioms OcamlPq.Hash.Sha2.sha512Constants_eq
#print axioms OcamlPq.Hash.Sha2.sha256H0_eq
#print axioms OcamlPq.Hash.Sha2.sha512H0_eq
#print axioms OcamlPq.Hash.Sha2.sha256_eq
#print axioms OcamlPq.Hash.Sha2.sha512_eq
#print axioms OcamlPq.Hash.Sha2.hmacSha256_eq
#print axioms OcamlPq.Hash.Sha2.hmacSha512_eq
#print axioms OcamlPq.Hash.Sha2.mgf1Sha256_eq
#print axioms OcamlPq.Hash.Sha2.mgf1Sha512_eq
#print axioms OcamlPq.Hash.KAT.SHA3_256_empty
#print axioms OcamlPq.Hash.KAT.SHA256_abc
#print axioms OcamlPq.Hash.KAT.SHA512_abc

-- End to end: the concrete models of each engine, over the verified hash
-- models, equal the FIPS algorithms built from the FIPS building blocks.
#print axioms OcamlPq.EndToEnd.MLKEM.mlkem512_endToEnd
#print axioms OcamlPq.EndToEnd.MLKEM.mlkem768_endToEnd
#print axioms OcamlPq.EndToEnd.MLKEM.mlkem1024_endToEnd
#print axioms OcamlPq.EndToEnd.MLKEM.correct_e2e
#print axioms OcamlPq.EndToEnd.MLDSA.mldsa44_endToEnd
#print axioms OcamlPq.EndToEnd.MLDSA.mldsa65_endToEnd
#print axioms OcamlPq.EndToEnd.MLDSA.mldsa87_endToEnd
#print axioms OcamlPq.EndToEnd.MLDSA.signMu_e2e
#print axioms OcamlPq.EndToEnd.MLDSA.verify_e2e
#print axioms OcamlPq.EndToEnd.MLDSA.buildSigningKey_e2e
#print axioms OcamlPq.EndToEnd.MLDSA.sign_verify
#print axioms OcamlPq.EndToEnd.SLHDSA.keypairFromSeed_e2e
#print axioms OcamlPq.EndToEnd.SLHDSA.signFormatted_e2e
#print axioms OcamlPq.EndToEnd.SLHDSA.verifyFormatted_e2e
#print axioms OcamlPq.EndToEnd.SLHDSA.sign_e2e
#print axioms OcamlPq.EndToEnd.SLHDSA.verify_e2e
#print axioms OcamlPq.EndToEnd.SLHDSA.verify_sign_e2e
#print axioms OcamlPq.EndToEnd.SLHDSA.verify_sign_cross_platform
