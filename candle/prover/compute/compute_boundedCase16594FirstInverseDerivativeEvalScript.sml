(*****************************************************************************
 * Exact evaluator probe for the first genuine case-16594 inverse derivative.
 *
 * This is deliberately one small production-environment calculation.  It
 * detects representation, lookup, and evaluator-cost failures before the
 * complete inverse-state bridge is attempted.
 *****************************************************************************)
Theory compute_boundedCase16594FirstInverseDerivativeEval
Ancestors
  compute_evalPure
  compute_boundedCase16594ObjectUnaryControlEval
Libs
  bossLib preamble

Definition bounded_case16594_first_inverse_reciprocal_cv_def:
  bounded_case16594_first_inverse_reciprocal_cv =
    Pair
      (Pair (Pair (Num 583091134019) (Num 0)) (Num 549755813887))
      (Pair (Pair (Num 291561029025) (Num 0)) (Num 274877906943))
End

Definition bounded_case16594_first_inverse_derivative_cv_def:
  bounded_case16594_first_inverse_derivative_cv =
    Pair
      (Pair
        (Pair (Num 0) (Num 85007833646116892450625))
        (Num 75557863725914323419135))
      (Pair
        (Pair (Num 0) (Num 339995270571563419092361))
        (Num 302231454903657293676543))
End

Theorem bounded_case16594_first_inverse_derivative_pure_eval:
  compute_eval_pure 32 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_inverse_derivative»
        [from_cv bounded_case16594_first_inverse_reciprocal_cv]) =
    SOME (from_cv bounded_case16594_first_inverse_derivative_cv)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_first_inverse_derivative_eval:
  32 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_inverse_derivative»
        [from_cv bounded_case16594_first_inverse_reciprocal_cv])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_first_inverse_derivative_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `32`
  >> asm_rewrite_tac
       [bounded_case16594_first_inverse_derivative_pure_eval]
QED

val _ = export_theory ();
