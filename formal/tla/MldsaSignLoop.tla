----------------------------- MODULE MldsaSignLoop -----------------------------
(***************************************************************************)
(* ML-DSA signing rejection loop: attempt counter, mask nonces, rejection  *)
(* conditions and the iteration bound.                                     *)
(*                                                                         *)
(* OCaml modelled (mldsa/mldsa_engine.ml, sign_mu_with_randomness):        *)
(*   lines 728-800: `attempt iteration` with the bound 821                 *)
(*   (Signing_failed), kappa = iteration * l, mask nonces kappa + row      *)
(*   encoded by u16_le (lines 165-169), the rejection flag built from the  *)
(*   z / r0 / ct0 norm checks and hint_count > omega, and the call to      *)
(*   encode_signature only when the flag is 0.                             *)
(*                                                                         *)
(* Checked against FIPS 204 Algorithm 7 (ML-DSA.Sign_internal): kappa <- 0 *)
(* before the loop and kappa <- kappa + l at the end of every iteration,   *)
(* y <- ExpandMask(rho'', kappa) with IntegerToBytes(kappa + r, 2)         *)
(* (Algorithm 34), and the two rejection tests of lines 22-29.  FIPS runs  *)
(* in lock-step with the OCaml loop.                                       *)
(*                                                                         *)
(* Abstraction: the outcome of each attempt (whether ||z|| >= gamma1 -     *)
(* beta, ||r0|| >= gamma2 - beta, ||ct0|| >= gamma2, and the number of     *)
(* hints, represented by 0, omega or omega + 1) is chosen                  *)
(* nondeterministically, so every sequence of outcomes is explored with    *)
(* the real bound MaxAttempts = 821 and the real l and omega of ML-DSA-44, *)
(* -65 and -87.  The outcome of an attempt is a function of its nonces     *)
(* only; the lock-step invariant KappaAgrees makes OCaml and FIPS consume  *)
(* the same outcome.                                                       *)
(*                                                                         *)
(* Properties:                                                             *)
(*   KappaAgrees      - OCaml's kappa = iteration * l equals FIPS's kappa; *)
(*   NoncesInRange    - every nonce kappa + r < 2^16, so u16_le equals     *)
(*                      IntegerToBytes(kappa + r, 2) and is injective;     *)
(*   NoncesFresh      - nonces strictly increase, so no (rho'', nonce) is  *)
(*                      ever reused across attempts;                       *)
(*   EncodePrecond    - encode_signature only sees <= omega hints;         *)
(*   FailedIffAllReject - Signing_failed exactly when all 821 attempts     *)
(*                      were rejected;                                     *)
(*   ResultIsFIPS     - on success the returned attempt is the first       *)
(*                      attempt FIPS 204 accepts (same kappa);             *)
(*   StepBound        - at most MaxAttempts + 1 steps.                     *)
(***************************************************************************)
EXTENDS Naturals, Integers, TLC

CONSTANTS MaxAttempts, ParamSets

\* ML-DSA-44 / 65 / 87: (l, omega)
MldsaParams == { [name |-> "ML-DSA-44", l |-> 4, omega |-> 80],
                 [name |-> "ML-DSA-65", l |-> 5, omega |-> 55],
                 [name |-> "ML-DSA-87", l |-> 7, omega |-> 75] }

U16Le(x) == <<x % 256, (x \div 256) % 256>>          \* OCaml u16_le
IntegerToBytes2(x) == <<x % 256, (x \div 256) % 256>>  \* FIPS 204 Alg. 11, x < 2^16

VARIABLES
  P,             \* parameter set
  iteration,     \* OCaml `attempt iteration`
  fipsKappa,     \* FIPS 204 kappa
  fipsFirstAccept, \* kappa of the first attempt FIPS accepts (-1 = none yet)
  maxNonce,      \* largest mask nonce used so far (-1 = none)
  rejected,      \* number of rejected attempts
  lastNonces,    \* OCaml: u16_le encodings of the last attempt's mask nonces
  fipsNonces,    \* FIPS: IntegerToBytes(kappa + r, 2) of the last attempt
  pc,            \* "attempt" or "done"
  result,        \* "none", "ok", "failed"
  acceptedAt,    \* iteration of the returned signature
  encodedHints,  \* hint count handed to encode_signature (-1 = not called)
  steps

vars == <<P, iteration, fipsKappa, fipsFirstAccept, maxNonce, rejected, lastNonces,
          fipsNonces, pc, result, acceptedAt, encodedHints, steps>>

Init ==
  /\ P \in ParamSets
  /\ iteration = 0
  /\ fipsKappa = 0
  /\ fipsFirstAccept = -1
  /\ maxNonce = -1
  /\ rejected = 0
  /\ lastNonces = <<>>
  /\ fipsNonces = <<>>
  /\ pc = "attempt"
  /\ result = "none"
  /\ acceptedAt = -1
  /\ encodedHints = -1
  /\ steps = 0

\* let rec attempt iteration =
\*   if iteration >= 821 then Error Signing_failed else ...
Attempt ==
  /\ pc = "attempt"
  /\ IF iteration >= MaxAttempts
     THEN /\ result' = "failed" /\ pc' = "done"
          /\ UNCHANGED <<iteration, fipsKappa, fipsFirstAccept, maxNonce, rejected,
                         lastNonces, fipsNonces, acceptedAt, encodedHints>>
     ELSE \E zBad, r0Bad, ct0Bad \in BOOLEAN, hintCount \in {0, P.omega, P.omega + 1} :
          LET kappa == iteration * P.l
              nonces == [row \in 0 .. P.l - 1 |-> kappa + row]
              \* OCaml: rejection := z flag lor r0 flag lor ct0 flag lor too_many_hints
              tooManyHints == IF hintCount > P.omega THEN 1 ELSE 0
              rejection == (IF zBad THEN 1 ELSE 0) + (IF r0Bad THEN 1 ELSE 0)
                           + (IF ct0Bad THEN 1 ELSE 0) + tooManyHints
              \* FIPS 204 Alg. 7 lines 22-29
              fipsReject == (zBad \/ r0Bad) \/ (ct0Bad \/ hintCount > P.omega)
          IN /\ lastNonces' = [row \in 0 .. P.l - 1 |-> U16Le(nonces[row])]
             /\ fipsNonces' = [r \in 0 .. P.l - 1 |-> IntegerToBytes2(fipsKappa + r)]
             /\ maxNonce' = kappa + P.l - 1
             /\ fipsFirstAccept' = IF fipsFirstAccept = -1 /\ ~fipsReject
                                   THEN fipsKappa ELSE fipsFirstAccept
             /\ fipsKappa' = fipsKappa + P.l
             /\ IF rejection # 0
                THEN /\ iteration' = iteration + 1
                     /\ rejected' = rejected + 1
                     /\ UNCHANGED <<pc, result, acceptedAt, encodedHints>>
                ELSE /\ result' = "ok" /\ pc' = "done"
                     /\ acceptedAt' = iteration
                     /\ encodedHints' = hintCount
                     /\ UNCHANGED <<iteration, rejected>>
  /\ steps' = steps + 1
  /\ UNCHANGED P

Terminated == pc = "done" /\ UNCHANGED vars
Next == Attempt \/ Terminated
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
\* before each attempt, OCaml's kappa is FIPS's kappa
KappaAgrees == pc = "attempt" => iteration * P.l = fipsKappa

NoncesInRange ==
  /\ maxNonce < 2 ^ 16
  /\ lastNonces = fipsNonces

\* the nonces of the next attempt are all larger than every nonce used so far
NoncesFresh == pc = "attempt" => iteration * P.l > maxNonce

EncodePrecond == encodedHints # -1 => encodedHints <= P.omega

FailedIffAllReject ==
  /\ result = "failed" => (rejected = MaxAttempts /\ fipsFirstAccept = -1)
  /\ (pc = "done" /\ rejected = MaxAttempts) => result = "failed"

ResultIsFIPS ==
  result = "ok" => (fipsFirstAccept = acceptedAt * P.l /\ rejected = acceptedAt)

StepBound == steps <= MaxAttempts + 1

\* The arithmetic fact behind NoncesInRange for the real constants,
\* independent of the exploration: the last nonce of the last attempt fits.
ASSUME \A Q \in MldsaParams : (821 - 1) * Q.l + (Q.l - 1) < 2 ^ 16
=============================================================================
