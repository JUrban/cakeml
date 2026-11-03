(*****************************************************************************
 * Exact linear error term for the first genuine case-16594 inverse state.
 *****************************************************************************)
Theory compute_boundedCase16594FirstInverseLinearErrorEval
Ancestors
  compute_boundedCase16594FirstInverseZeroHessianEval
Libs
  bossLib preamble

Definition bounded_case16594_first_inverse_radii_cv_def:
  bounded_case16594_first_inverse_radii_cv =
    Pair
      (Pair (Pair (Num 161518258122) (Num 0)) (Num 999999999999))
      (Pair
        (Pair (Pair (Num 161518258122) (Num 0)) (Num 999999999999))
        (Pair
          (Pair (Pair (Num 161518258122) (Num 0)) (Num 999999999999))
          (Pair
            (Pair (Pair (Num 323036516242) (Num 0)) (Num 999999999999))
            (Pair
              (Pair (Pair (Num 211308954991) (Num 0)) (Num 999999999999))
              (Pair
                (Pair (Pair (Num 323036516242) (Num 0))
                  (Num 999999999999))
                (Num 0))))))
End

val first_inverse_linear_error_diagnostic =
  EVAL
    ``compute_eval_pure 512 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_dot_abs_upper»
          [from_cv bounded_case16594_first_inverse_radii_cv;
           from_cv bounded_case16594_first_inverse_center_gradient_cv])``;

Definition bounded_case16594_first_inverse_linear_error_cv_def:
  bounded_case16594_first_inverse_linear_error_cv =
    Pair (Pair (Num 0) (Num 0))
      (Num
        762145642166990290864647761179972242614403843424065222377723867096038022172794340849684107193235344521442121855812163792833978437326241529855999999999999999999999999999999999999999999999999999999999999999999999999)
End

Theorem bounded_case16594_first_inverse_linear_error_pure_eval:
  compute_eval_pure 512 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dot_abs_upper»
        [from_cv bounded_case16594_first_inverse_radii_cv;
         from_cv bounded_case16594_first_inverse_center_gradient_cv]) =
    SOME (from_cv bounded_case16594_first_inverse_linear_error_cv)
Proof
  CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC first_inverse_linear_error_diagnostic
QED

Theorem bounded_case16594_first_inverse_linear_error_eval:
  512 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dot_abs_upper»
        [from_cv bounded_case16594_first_inverse_radii_cv;
         from_cv bounded_case16594_first_inverse_center_gradient_cv])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_first_inverse_linear_error_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `512`
  >> asm_rewrite_tac [bounded_case16594_first_inverse_linear_error_pure_eval]
QED

val _ = export_theory ();
