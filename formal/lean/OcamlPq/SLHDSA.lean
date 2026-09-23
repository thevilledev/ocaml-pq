import OcamlPq.SLHDSA.Params
import OcamlPq.SLHDSA.Basic
import OcamlPq.SLHDSA.Base2b
import OcamlPq.SLHDSA.Address
import OcamlPq.SLHDSA.Treehash
import OcamlPq.SLHDSA.WOTS
import OcamlPq.SLHDSA.XMSS
import OcamlPq.SLHDSA.FORS
import OcamlPq.SLHDSA.Hash
import OcamlPq.SLHDSA.Hypertree
import OcamlPq.SLHDSA.Top
import OcamlPq.SLHDSA.Portability

/-!
# SLH-DSA (FIPS 205): refinement proofs for `slhdsa/slhdsa_engine.ml`

* `Params`      — the twelve parameter sets vs FIPS 205 Table 2, derived sizes,
                  module-initialisation checks.
* `Base2b`      — `message_to_fors_indices` = `base_2b` under `int` wrap-around
                  (every width `w ≥ a + 7`); WOTS+ digits and checksum.
* `Address`     — `address_full` / `address_compressed` = ADRS / ADRS_c; the
                  ADRS setters.
* `Treehash`    — `treehash` = `xmss_node`/`fors_node` + authentication paths,
                  for every height and index; `compute_root` = the root loops of
                  Algorithms 11/17; out-of-range leaf indices.
* `WOTS`, `XMSS`, `FORS` — Algorithms 5–11 and 14–17 and their correctness.
* `Hash`        — the SHA2/SHAKE instantiation of F, H, T_ℓ, PRF, PRF_msg, H_msg.
* `Hypertree`   — digest split, `ht_sign`, `ht_verify`, hypertree correctness.
* `Top`         — key generation, signing, verification (Algorithms 18–20, 22),
                  end-to-end correctness, signature layout.
* `Portability` — every other `int` intermediate is `Portable`.
-/
