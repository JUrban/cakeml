(*****************************************************************************
 * Reusable evaluator bindings for the generic historical production guard.
 *****************************************************************************)
Theory compute_registeredCase10173ProductionGuardBindingEval
Ancestors
  compute_registeredCase10173ProductionGuardCompositionEval
  compute_registeredCase10173CenterEnvironmentStructuralEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_hist_center_environment_binding_eval:
  registered_case10173_q_center_environment_positive boxes =
      SOME center_boxes /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME center_environment /\
  100 +
      8 * (registered_case10173_center_list_length boxes + 1) +
      11 * (LENGTH center_environment + 1) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_of_q»
        [App «candle_cv_q_center_environment_list» [from_cv boxes]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv_list center_environment)),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_list_of_q»
            [from_cv center_boxes]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac
      >- intLib.ARITH_TAC
      >> irule
           compute_registeredCase10173CenterEnvironmentStructuralEvalTheory.registered_case10173_q_center_environment_positive_eval_structural
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_interval_list_of_q_object_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_hist_u126_value_binding_eval:
  bounded_historical_u126_decimal [x0;x1;x2;x3;x4;x5] =
      SOME (value,gradient) /\
  120 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (Uop Fst
        (App «candle_cv_fs_hist_u126»
          [from_cv
            (bounded_interval64_object_cv_list [x0;x1;x2;x3;x4;x5])]))
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv value)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanPointEvalTheory.registered_case10173_compute_eval_uop_fst_argument_result
  >> qexists_tac `bounded_interval64_object_cv_list gradient`
  >> irule
       compute_registeredCase10173HistoricalUGeneralEvalTheory.registered_case10173_historical_u126_typed_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_hist_u135_value_binding_eval:
  bounded_historical_u135_decimal [x0;x1;x2;x3;x4;x5] =
      SOME (value,gradient) /\
  120 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (Uop Fst
        (App «candle_cv_fs_hist_u135»
          [from_cv
            (bounded_interval64_object_cv_list [x0;x1;x2;x3;x4;x5])]))
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv value)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanPointEvalTheory.registered_case10173_compute_eval_uop_fst_argument_result
  >> qexists_tac `bounded_interval64_object_cv_list gradient`
  >> irule
       compute_registeredCase10173HistoricalUGeneralEvalTheory.registered_case10173_historical_u135_typed_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_hist_delta_x4_second_value_binding_eval:
  bounded_historical_delta_x4_second_decimal environment =
      SOME (value,gradient,hessian) /\
  bounded_hessian64_rows hessian = SOME rows /\
  60 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_value»
        [App «candle_cv_fs_hist_delta_x4_second»
          [from_cv (bounded_interval64_object_cv_list environment)]])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv value)),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_second_value»
            [from_cv
              (Pair (bounded_interval64_object_cv value)
                (Pair (bounded_interval64_object_cv_list gradient)
                  (bounded_interval64_object_cv_matrix rows)))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac
      >- intLib.ARITH_TAC
      >> irule
           compute_registeredCase10173HistoricalDeltaX4SecondEvalTheory.registered_case10173_fs_hist_delta_x4_second_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalSqrtSecondEvalTheory.registered_case10173_fs_hist_second_value_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_hist_quotient_binding_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      delta_expression (refs:hol_refs) =
      (M_success (from_cv (bounded_interval64_object_cv delta_x4)),refs) /\
  bounded_interval64_mul_decimal root_delta root_four_x0 = SOME product /\
  bounded_interval64_positive_inv_certificate_decimal product reciprocal /\
  bounded_interval64_mul_decimal
    (bounded_interval64_neg delta_x4) reciprocal = SOME quotient /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_quotient»
        [delta_expression;
         from_cv (bounded_interval64_object_cv root_delta);
         from_cv (bounded_interval64_object_cv root_four_x0)]) refs =
    (M_success (from_cv (bounded_interval64_object_cv quotient)),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_quotient»
            [from_cv (bounded_interval64_object_cv delta_x4);
             from_cv (bounded_interval64_object_cv root_delta);
             from_cv (bounded_interval64_object_cv root_four_x0)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173ProductionGuardAuthenticatedEvalTheory.registered_case10173_hist_quotient_typed_eval
  >> simp []
  >> qexists_tac `reciprocal`
  >> simp []
QED

val _ = export_theory ();
