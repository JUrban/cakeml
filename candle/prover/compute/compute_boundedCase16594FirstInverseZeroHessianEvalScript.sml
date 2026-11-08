(*****************************************************************************
 * Exact unary-Hessian propagation for the first genuine inverse state.
 *****************************************************************************)
Theory compute_boundedCase16594FirstInverseZeroHessianEval
Ancestors
  compute_boundedCase16594FirstInverseZeroScaleEval
Libs
  bossLib preamble

val first_inverse_zero_hessian_diagnostic =
  EVAL
    ``compute_eval_pure 512 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_unary_hessian6»
          [from_cv bounded_case16594_first_inverse_derivative_cv;
           from_cv bounded_case16594_first_inverse_second_cv;
           from_cv bounded_case16594_zero_gradient6_cv;
           from_cv bounded_case16594_zero_hessian21_cv])``;

Definition bounded_case16594_first_inverse_hessian_entry_cv_def:
  bounded_case16594_first_inverse_hessian_entry_cv =
    Pair
      (Pair (Pair (Num 0) (Num 0))
        (Num
          2085924839766513752338888384931203236916703635113918720651407820138886450957656787131798913023))
      (Pair (Pair (Num 0) (Num 0))
        (Num
          130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432063))
End

Definition bounded_case16594_first_inverse_hessian_cv_def:
  bounded_case16594_first_inverse_hessian_cv =
    bounded_case16594_cv_repeat 21
      bounded_case16594_first_inverse_hessian_entry_cv
End

Theorem bounded_case16594_first_inverse_zero_hessian_pure_eval:
  compute_eval_pure 512 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_unary_hessian6»
        [from_cv bounded_case16594_first_inverse_derivative_cv;
         from_cv bounded_case16594_first_inverse_second_cv;
         from_cv bounded_case16594_zero_gradient6_cv;
         from_cv bounded_case16594_zero_hessian21_cv]) =
    SOME (from_cv bounded_case16594_first_inverse_hessian_cv)
Proof
  CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC first_inverse_zero_hessian_diagnostic
QED

Theorem bounded_case16594_first_inverse_zero_hessian_eval:
  512 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_unary_hessian6»
        [from_cv bounded_case16594_first_inverse_derivative_cv;
         from_cv bounded_case16594_first_inverse_second_cv;
         from_cv bounded_case16594_zero_gradient6_cv;
         from_cv bounded_case16594_zero_hessian21_cv])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_first_inverse_hessian_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `512`
  >> asm_rewrite_tac
       [bounded_case16594_first_inverse_zero_hessian_pure_eval]
QED

val _ = export_theory ();
