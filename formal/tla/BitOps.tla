-------------------------------- MODULE BitOps --------------------------------
(***************************************************************************)
(* Helper module (no model of its own): OCaml bitwise operators on         *)
(* non-negative integers, used to transcribe OCaml expressions literally.  *)
(* TLC integers are 32-bit, so these are only applied to values < 2^31.    *)
(***************************************************************************)
EXTENDS Naturals

Lsl(x, k) == x * 2 ^ k          \* x lsl k    (no overflow in our uses)
Lsr(x, k) == x \div 2 ^ k       \* x lsr k    (x >= 0)

RECURSIVE Land(_, _), Lor(_, _), Lxor(_, _)
Land(a, b) == IF a = 0 \/ b = 0 THEN 0
              ELSE 2 * Land(a \div 2, b \div 2) + (a % 2) * (b % 2)
Lor(a, b)  == IF a = 0 THEN b ELSE IF b = 0 THEN a
              ELSE 2 * Lor(a \div 2, b \div 2) + (IF a % 2 = 1 \/ b % 2 = 1 THEN 1 ELSE 0)
Lxor(a, b) == IF a = 0 THEN b ELSE IF b = 0 THEN a
              ELSE 2 * Lxor(a \div 2, b \div 2) + ((a + b) % 2)
=============================================================================
