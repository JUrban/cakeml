(*****************************************************************************
 * Registered evaluator seam for the historical raw Taylor product.
 *
 * The product source deliberately retains its center, gradient, and Hessian
 * as unrounded object integers until [fs_result_complete_raw].  This file
 * first authenticates that literal source decomposition.  Subsequent object
 * refinements can discharge the three component contracts independently,
 * without replaying the complete checker expression.
 *****************************************************************************)
Theory compute_registeredCase10173ResultMulEval
Ancestors
  compute_registeredCase10173ResultCompleteRawEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_result_mul_domain_body_def:
  registered_case10173_fs_result_mul_domain_body =
    App «candle_cv_bool_and»
      [App «candle_cv_fs_result_domain» [Var «left»];
       App «candle_cv_fs_result_domain» [Var «right»]]
End

Definition registered_case10173_fs_result_mul_center_body_def:
  registered_case10173_fs_result_mul_center_body =
    App «candle_cv_fs_first_make»
      [App «candle_cv_fs_raw_interval_mul»
         [App «candle_cv_fs_first_value»
            [App «candle_cv_fs_result_center» [Var «left»]];
          App «candle_cv_fs_first_value»
            [App «candle_cv_fs_result_center» [Var «right»]]];
       App «candle_cv_fs_raw_interval_list_add»
         [App «candle_cv_fs_raw_interval_list_scale»
            [App «candle_cv_fs_first_value»
               [App «candle_cv_fs_result_center» [Var «right»]];
             App «candle_cv_fs_first_gradient»
               [App «candle_cv_fs_result_center» [Var «left»]]];
          App «candle_cv_fs_raw_interval_list_scale»
            [App «candle_cv_fs_first_value»
               [App «candle_cv_fs_result_center» [Var «left»]];
             App «candle_cv_fs_first_gradient»
               [App «candle_cv_fs_result_center» [Var «right»]]]]]
End

Definition registered_case10173_fs_result_mul_hessian_body_def:
  registered_case10173_fs_result_mul_hessian_body =
    App «candle_cv_fs_raw_interval_matrix_add»
      [App «candle_cv_fs_raw_interval_matrix_add»
         [App «candle_cv_fs_raw_interval_matrix_scale»
            [App «candle_cv_fs_result_value_bound» [Var «right»];
             App «candle_cv_fs_result_hessian» [Var «left»]];
          App «candle_cv_fs_raw_interval_outer»
            [App «candle_cv_fs_result_gradient_bounds» [Var «left»];
             App «candle_cv_fs_result_gradient_bounds» [Var «right»]]];
       App «candle_cv_fs_raw_interval_matrix_add»
         [App «candle_cv_fs_raw_interval_outer»
            [App «candle_cv_fs_result_gradient_bounds» [Var «right»];
             App «candle_cv_fs_result_gradient_bounds» [Var «left»]];
          App «candle_cv_fs_raw_interval_matrix_scale»
            [App «candle_cv_fs_result_value_bound» [Var «left»];
             App «candle_cv_fs_result_hessian» [Var «right»]]]]
End

Definition registered_case10173_fs_result_mul_body_def:
  registered_case10173_fs_result_mul_body =
    App «candle_cv_fs_result_complete_raw»
      [Var «radii»;
       registered_case10173_fs_result_mul_domain_body;
       registered_case10173_fs_result_mul_center_body;
       registered_case10173_fs_result_mul_hessian_body]
End

Theorem registered_case10173_fs_result_mul_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_mul» =
    SOME
      ([«radii»;«left»;«right»],
       registered_case10173_fs_result_mul_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_mul_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_mul»
        [from_cv radii;from_cv left;from_cv right])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);(«left»,from_cv left);
         («right»,from_cv right)]
        registered_case10173_fs_result_mul_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_fs_result_mul_lookup]
QED

Theorem registered_case10173_fs_result_mul_eval_from_components:
  1 < clock /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (subst [(«radii»,from_cv radii);(«left»,from_cv left);
              («right»,from_cv right)]
        registered_case10173_fs_result_mul_domain_body) (refs:hol_refs) =
    (M_success (from_cv result_domain),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (subst [(«radii»,from_cv radii);(«left»,from_cv left);
              («right»,from_cv right)]
        registered_case10173_fs_result_mul_center_body) refs =
    (M_success (from_cv raw_center),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (subst [(«radii»,from_cv radii);(«left»,from_cv left);
              («right»,from_cv right)]
        registered_case10173_fs_result_mul_hessian_body) refs =
    (M_success (from_cv raw_hessian),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_complete_raw»
        [from_cv radii;from_cv result_domain;
         from_cv raw_center;from_cv raw_hessian]) refs =
    (M_success (from_cv result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_mul»
        [from_cv radii;from_cv left;from_cv right]) refs =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> rw [registered_case10173_fs_result_mul_unfold]
  >> simp
       [registered_case10173_fs_result_mul_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_complete_raw»
            [from_cv radii;from_cv result_domain;
             from_cv raw_center;from_cv raw_hessian]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            registered_case10173_fs_result_mul_domain_body_def,
            registered_case10173_fs_result_mul_center_body_def,
            registered_case10173_fs_result_mul_hessian_body_def]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
