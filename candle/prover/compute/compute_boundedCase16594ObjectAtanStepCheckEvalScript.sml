(*****************************************************************************
 * Complete successful guard for the first genuine case-16594 atan step.
 * Every production certificate is checked on the actual authenticated data;
 * only the runtime source center and value-bound representations vary.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAtanStepCheckEval
Ancestors
  compute_boundedCase16594ObjectAtanAlgebraicCertificateEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_atan_step_check_expression_def:
  bounded_case16594_object_atan_step_check_expression
      runtime_center runtime_value_bound =
    App «candle_cv_bool_and»
      [App «candle_cv_q_interval_atn_outer_certificate»
        [from_cv runtime_center;
         from_cv bounded_case16594_object_cell0_atan_center_input_cv;
         from_cv bounded_case16594_object_cell0_atan_center_result_cv];
       App «candle_cv_bool_and»
        [App «candle_cv_q_interval_square_outer_certificate»
          [from_cv runtime_center;
           from_cv bounded_case16594_object_cell0_atan_center_input_cv;
           from_cv bounded_case16594_object_cell0_atan_center_square_cv];
         App «candle_cv_bool_and»
          [App «candle_cv_q_interval_inv_certificate»
            [App «candle_cv_q_packed_object_atn_denominator»
              [from_cv
                bounded_case16594_object_cell0_atan_center_square_cv];
             from_cv
               bounded_case16594_object_cell0_atan_center_derivative_cv];
           App «candle_cv_bool_and»
            [App «candle_cv_q_interval_square_outer_certificate»
              [from_cv runtime_value_bound;
               from_cv bounded_case16594_object_cell0_atan_box_input_cv;
               from_cv bounded_case16594_object_cell0_atan_box_square_cv];
             App «candle_cv_bool_and»
              [App «candle_cv_q_interval_inv_certificate»
                [App «candle_cv_q_packed_object_atn_denominator»
                  [from_cv
                    bounded_case16594_object_cell0_atan_box_square_cv];
                 from_cv
                   bounded_case16594_object_cell0_atan_box_derivative_cv];
               App «candle_cv_q_interval_square_outer_certificate»
                [from_cv
                   bounded_case16594_object_cell0_atan_box_derivative_cv;
                 from_cv
                   bounded_case16594_object_cell0_atan_box_derivative_cv;
                 from_cv
                   bounded_case16594_object_cell0_atan_box_derivative_square_cv]]]]]]
End

Theorem bounded_case16594_object_atan_step_check_eval:
  bounded_object_q_interval_encoded runtime_center /\
  bounded_object_q_interval_cv_equiv runtime_center
    (bounded_object_q_taylor_center
      bounded_case16594_object_source8_result) /\
  bounded_object_q_interval_encoded runtime_value_bound /\
  bounded_object_q_interval_cv_equiv runtime_value_bound
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source8_result) /\
  4097 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (bounded_case16594_object_atan_step_check_expression
        runtime_center runtime_value_bound) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> rewrite_tac [bounded_case16594_object_atan_step_check_expression_def]
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectAtanOuterCertificateEvalTheory.bounded_case16594_object_runtime_atan_center_outer_certificate_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectAtanAlgebraicCertificateEvalTheory.bounded_case16594_object_runtime_atan_center_square_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectAtanAlgebraicCertificateEvalTheory.bounded_case16594_object_atan_center_inverse_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectAtanAlgebraicCertificateEvalTheory.bounded_case16594_object_runtime_atan_box_square_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectAtanAlgebraicCertificateEvalTheory.bounded_case16594_object_atan_box_inverse_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectAtanAlgebraicCertificateEvalTheory.bounded_case16594_object_atan_derivative_square_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
