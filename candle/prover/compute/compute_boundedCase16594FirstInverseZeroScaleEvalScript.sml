(*****************************************************************************
 * Zero-gradient scaling for the first genuine case-16594 inverse state.
 *****************************************************************************)
Theory compute_boundedCase16594FirstInverseZeroScaleEval
Ancestors
  compute_boundedCase16594FirstInverseSecondEval
Libs
  bossLib preamble

Definition bounded_case16594_zero_q_cv_def:
  bounded_case16594_zero_q_cv =
    Pair (Pair (Num 0) (Num 0)) (Num 0)
End

Definition bounded_case16594_zero_interval_cv_def:
  bounded_case16594_zero_interval_cv =
    Pair bounded_case16594_zero_q_cv bounded_case16594_zero_q_cv
End

Definition bounded_case16594_cv_repeat_def:
  bounded_case16594_cv_repeat 0 value = Num 0 /\
  bounded_case16594_cv_repeat (SUC count) value =
    Pair value (bounded_case16594_cv_repeat count value)
End

Definition bounded_case16594_zero_gradient6_cv_def:
  bounded_case16594_zero_gradient6_cv =
    bounded_case16594_cv_repeat 6 bounded_case16594_zero_interval_cv
End

Definition bounded_case16594_zero_hessian21_cv_def:
  bounded_case16594_zero_hessian21_cv =
    bounded_case16594_cv_repeat 21 bounded_case16594_zero_interval_cv
End

Definition bounded_case16594_first_inverse_center_gradient_entry_cv_def:
  bounded_case16594_first_inverse_center_gradient_entry_cv =
    Pair
      (Pair (Pair (Num 0) (Num 0))
        (Num 75557863725914323419135))
      (Pair (Pair (Num 0) (Num 0))
        (Num 302231454903657293676543))
End

Definition bounded_case16594_first_inverse_center_gradient_cv_def:
  bounded_case16594_first_inverse_center_gradient_cv =
    bounded_case16594_cv_repeat 6
      bounded_case16594_first_inverse_center_gradient_entry_cv
End

Theorem bounded_case16594_first_inverse_zero_scale_pure_eval:
  compute_eval_pure 256 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_scale»
        [from_cv bounded_case16594_first_inverse_derivative_cv;
         from_cv bounded_case16594_zero_gradient6_cv]) =
    SOME (from_cv bounded_case16594_first_inverse_center_gradient_cv)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_first_inverse_zero_scale_eval:
  256 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_scale»
        [from_cv bounded_case16594_first_inverse_derivative_cv;
         from_cv bounded_case16594_zero_gradient6_cv])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_first_inverse_center_gradient_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `256`
  >> asm_rewrite_tac [bounded_case16594_first_inverse_zero_scale_pure_eval]
QED

val _ = export_theory ();
