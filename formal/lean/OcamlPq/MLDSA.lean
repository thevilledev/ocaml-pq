import OcamlPq.MLDSA.Arith
import OcamlPq.MLDSA.Tables
import OcamlPq.MLDSA.NTT
import OcamlPq.MLDSA.NTTClosed
import OcamlPq.MLDSA.NTTMath
import OcamlPq.MLDSA.NTTMul
import OcamlPq.MLDSA.NTTBound
import OcamlPq.MLDSA.Rounding
import OcamlPq.MLDSA.Sign
import OcamlPq.MLDSA.Flags
import OcamlPq.MLDSA.SignAttempt
import OcamlPq.MLDSA.Verify

/-!
# ML-DSA arithmetic (FIPS 204)

Formal models of the arithmetic in `mldsa/mldsa_engine.ml` and proofs that
they refine FIPS 204:

* `Arith`      — `norm`, `center`, `add_mod`, `sub_mod`, `mul_mod`, `pow_mod`;
* `Tables`     — `bit_reverse_8`, `zetas`, `inverse_n`;
* `NTT`        — `ntt`, `inverse_ntt`, `pointwise`, `matrix_vector_ntt`
                 refine Algorithms 41, 42, 45, 48;
* `NTTClosed`, `NTTMath`, `NTTMul` — `NTT⁻¹ ∘ NTT = id`, `NTT ∘ NTT⁻¹ = id`,
                 NTT multiplication in `ℤ_q[X]/(X^256+1)`;
* `NTTBound`   — the signer's `cs1`/`cs2` are the exact products, `‖·‖∞ ≤ τη`;
* `Rounding`   — `power2round`, `decompose`, `use_hint`, `make_hint` versus
                 Algorithms 35–40, and the UseHint/MakeHint lemma;
* `Sign`, `SignAttempt` — the signer's reference-implementation shortcuts
                 give the same decision and signature as Algorithm 7;
* `Flags`      — `norm_violation_flag`, `z = y + cs1`, `t1 lsl d`;
* `Verify`     — the verifier recovers the signer's `w1`.
-/
