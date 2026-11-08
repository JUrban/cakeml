(*****************************************************************************
 * Complete production evaluation of the first genuine atan instruction.
 * This composes all eight authenticated list bindings, the complete genuine
 * certificate guard, and the already-proved atan state constructor.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAtanStepCompleteEval
Ancestors
  compute_boundedCase16594ObjectAtanStepEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_atan_certificate_outputs_encoded:
  bounded_object_q_interval_encoded
      bounded_case16594_object_cell0_atan_center_result_cv /\
  bounded_object_q_interval_encoded
      bounded_case16594_object_cell0_atan_center_derivative_cv /\
  bounded_object_q_interval_encoded
      bounded_case16594_object_cell0_atan_box_derivative_cv /\
  bounded_object_q_interval_encoded
      bounded_case16594_object_cell0_atan_box_derivative_square_cv
Proof
  rw
    [compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_result_cv_def,
     compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_derivative_cv_def,
     compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_derivative_cv_def,
     compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_derivative_square_cv_def,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> EVAL_TAC
  >> simp []
QED

Definition bounded_case16594_object_atan_step_state_check_expression_def:
  bounded_case16594_object_atan_step_state_check_expression item =
    App «candle_cv_bool_and»
      [App «candle_cv_q_interval_atn_outer_certificate»
        [App «candle_cv_q_packed_object_state_center_value» [from_cv item];
         from_cv bounded_case16594_object_cell0_atan_center_input_cv;
         from_cv bounded_case16594_object_cell0_atan_center_result_cv];
       App «candle_cv_bool_and»
        [App «candle_cv_q_interval_square_outer_certificate»
          [App «candle_cv_q_packed_object_state_center_value» [from_cv item];
           from_cv bounded_case16594_object_cell0_atan_center_input_cv;
           from_cv bounded_case16594_object_cell0_atan_center_square_cv];
         App «candle_cv_bool_and»
          [App «candle_cv_q_interval_inv_certificate»
            [App «candle_cv_q_packed_object_atn_denominator»
              [from_cv bounded_case16594_object_cell0_atan_center_square_cv];
             from_cv bounded_case16594_object_cell0_atan_center_derivative_cv];
           App «candle_cv_bool_and»
            [App «candle_cv_q_interval_square_outer_certificate»
              [App «candle_cv_q_packed_object_state_value_bound»
                [from_cv item];
               from_cv bounded_case16594_object_cell0_atan_box_input_cv;
               from_cv bounded_case16594_object_cell0_atan_box_square_cv];
             App «candle_cv_bool_and»
              [App «candle_cv_q_interval_inv_certificate»
                [App «candle_cv_q_packed_object_atn_denominator»
                  [from_cv bounded_case16594_object_cell0_atan_box_square_cv];
                 from_cv bounded_case16594_object_cell0_atan_box_derivative_cv];
               App «candle_cv_q_interval_square_outer_certificate»
                [from_cv bounded_case16594_object_cell0_atan_box_derivative_cv;
                 from_cv bounded_case16594_object_cell0_atan_box_derivative_cv;
                 from_cv
                   bounded_case16594_object_cell0_atan_box_derivative_square_cv]]]]]]
End

Theorem bounded_case16594_object_atan_center_outer_state_eval:
  bounded_object_q_interval_encoded runtime_center /\
  bounded_object_q_interval_cv_equiv runtime_center
    (bounded_object_q_taylor_center
      bounded_case16594_object_source8_result) /\
  4097 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_atn_outer_certificate»
        [App «candle_cv_q_packed_object_state_center_value»
          [from_cv
            (bounded_case16594_object_state_cv domain_cv runtime_center
              center_gradient runtime_value_bound gradient_bounds hessian)];
         from_cv bounded_case16594_object_cell0_atan_center_input_cv;
         from_cv bounded_case16594_object_cell0_atan_center_result_cv])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_atn_outer_certificate»
            [from_cv runtime_center;
             from_cv bounded_case16594_object_cell0_atan_center_input_cv;
             from_cv bounded_case16594_object_cell0_atan_center_result_cv]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_app3_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_value_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectAtanOuterCertificateEvalTheory.bounded_case16594_object_runtime_atan_center_outer_certificate_eval
  >> simp [] >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_atan_center_square_state_eval:
  bounded_object_q_interval_encoded runtime_center /\
  bounded_object_q_interval_cv_equiv runtime_center
    (bounded_object_q_taylor_center
      bounded_case16594_object_source8_result) /\
  4098 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_square_outer_certificate»
        [App «candle_cv_q_packed_object_state_center_value»
          [from_cv
            (bounded_case16594_object_state_cv domain_cv runtime_center
              center_gradient runtime_value_bound gradient_bounds hessian)];
         from_cv bounded_case16594_object_cell0_atan_center_input_cv;
         from_cv bounded_case16594_object_cell0_atan_center_square_cv])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_square_outer_certificate»
            [from_cv runtime_center;
             from_cv bounded_case16594_object_cell0_atan_center_input_cv;
             from_cv bounded_case16594_object_cell0_atan_center_square_cv]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_app3_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_value_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectAtanAlgebraicCertificateEvalTheory.bounded_case16594_object_runtime_atan_center_square_eval
  >> simp [] >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_atan_box_square_state_eval:
  bounded_object_q_interval_encoded runtime_value_bound /\
  bounded_object_q_interval_cv_equiv runtime_value_bound
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source8_result) /\
  4098 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_square_outer_certificate»
        [App «candle_cv_q_packed_object_state_value_bound»
          [from_cv
            (bounded_case16594_object_state_cv domain_cv runtime_center
              center_gradient runtime_value_bound gradient_bounds hessian)];
         from_cv bounded_case16594_object_cell0_atan_box_input_cv;
         from_cv bounded_case16594_object_cell0_atan_box_square_cv])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_square_outer_certificate»
            [from_cv runtime_value_bound;
             from_cv bounded_case16594_object_cell0_atan_box_input_cv;
             from_cv bounded_case16594_object_cell0_atan_box_square_cv]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_app3_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_value_bound_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectAtanAlgebraicCertificateEvalTheory.bounded_case16594_object_runtime_atan_box_square_eval
  >> simp [] >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_atan_step_state_check_eval:
  bounded_object_q_interval_encoded runtime_center /\
  bounded_object_q_interval_cv_equiv runtime_center
    (bounded_object_q_taylor_center
      bounded_case16594_object_source8_result) /\
  bounded_object_q_interval_encoded runtime_value_bound /\
  bounded_object_q_interval_cv_equiv runtime_value_bound
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source8_result) /\
  4099 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (bounded_case16594_object_atan_step_state_check_expression
        (bounded_case16594_object_state_cv domain_cv runtime_center
          center_gradient runtime_value_bound gradient_bounds hessian))
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> rewrite_tac
       [bounded_case16594_object_atan_step_state_check_expression_def]
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac >- (irule bounded_case16594_object_atan_center_outer_state_eval
                   >> simp [] >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac >- (irule bounded_case16594_object_atan_center_square_state_eval
                   >> simp [] >> intLib.ARITH_TAC)
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
  >> conj_tac >- (irule bounded_case16594_object_atan_box_square_state_eval
                   >> simp [] >> intLib.ARITH_TAC)
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

Theorem bounded_case16594_object_atan_step_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_object_q_interval_encoded runtime_center /\
  bounded_object_q_interval_cv_equiv runtime_center
    (bounded_object_q_taylor_center
      bounded_case16594_object_source8_result) /\
  bounded_object_q_interval_encoded runtime_value_bound /\
  bounded_object_q_interval_cv_equiv runtime_value_bound
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source8_result) /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded gradient_bounds /\
  LENGTH gradient_bounds = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  16384 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_atn_step»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv
           (bounded_object_q_cv_list
             ([bounded_case16594_object_cell0_atan_center_input_cv;
               bounded_case16594_object_cell0_atan_box_input_cv;
               bounded_case16594_object_cell0_atan_center_result_cv;
               bounded_case16594_object_cell0_atan_center_square_cv;
               bounded_case16594_object_cell0_atan_center_derivative_cv;
               bounded_case16594_object_cell0_atan_box_square_cv;
               bounded_case16594_object_cell0_atan_box_derivative_cv;
               bounded_case16594_object_cell0_atan_box_derivative_square_cv] ++
              certificate_rest));
         from_cv
           (Pair
             (bounded_case16594_object_state_cv domain_cv runtime_center
               (bounded_object_q_cv_list center_gradient)
               runtime_value_bound
               (bounded_object_q_cv_list gradient_bounds)
               (bounded_object_q_cv_list packed_hessian))
             stack_rest)]) (refs:hol_refs) =
    (M_success
      (Pair (Num 1)
        (Pair
          (Pair
            (from_cv
              (bounded_case16594_object_state_unary_cv radii domain_cv
                bounded_case16594_object_cell0_atan_center_result_cv
                bounded_case16594_object_cell0_atan_center_derivative_cv
                bounded_case16594_object_cell0_atan_box_derivative_cv
                (bounded_object_q_atan_second_cv runtime_value_bound
                  bounded_case16594_object_cell0_atan_box_derivative_square_cv)
                center_gradient gradient_bounds packed_hessian))
            (from_cv stack_rest))
          (from_cv (bounded_object_q_cv_list certificate_rest)))),refs)
Proof
  strip_tac
  >> rw
       [compute_boundedCase16594ObjectAtanStepEvalTheory.bounded_case16594_object_atan_step_unfold]
  >> simp
       [compute_boundedCase16594ObjectAtanStepEvalTheory.bounded_case16594_object_atan_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_if_ispair_from_cv_pair]
  >> irule
       compute_boundedPackedObjectFinishEvalTheory.bounded_packed_compute_eval_if_true_result
  >> conj_tac
  >- simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule
       compute_boundedPackedObjectFinishEvalTheory.bounded_packed_compute_eval_if_true_result
  >> conj_tac
  >- (irule
        (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_has_eval)
      >> conj_tac >- intLib.ARITH_TAC
      >> simp [])
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_case16594_object_state_cv domain_cv runtime_center
          (bounded_object_q_cv_list center_gradient) runtime_value_bound
          (bounded_object_q_cv_list gradient_bounds)
          (bounded_object_q_cv_list packed_hessian)`
  >> conj_tac
  >- simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_object_cell0_atan_center_input_cv`
  >> conj_tac
  >- (irule
        (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          (Q.INST
            [`position` |-> `0`,
             `values` |->
               `bounded_case16594_object_cell0_atan_center_input_cv::
                  bounded_case16594_object_cell0_atan_box_input_cv::
                  bounded_case16594_object_cell0_atan_center_result_cv::
                  bounded_case16594_object_cell0_atan_center_square_cv::
                  bounded_case16594_object_cell0_atan_center_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_square_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_square_cv::
                  certificate_rest`]
            compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_nth_eval))
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_object_cell0_atan_box_input_cv`
  >> conj_tac
  >- (irule
        (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          (Q.INST
            [`position` |-> `1`,
             `values` |->
               `bounded_case16594_object_cell0_atan_center_input_cv::
                  bounded_case16594_object_cell0_atan_box_input_cv::
                  bounded_case16594_object_cell0_atan_center_result_cv::
                  bounded_case16594_object_cell0_atan_center_square_cv::
                  bounded_case16594_object_cell0_atan_center_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_square_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_square_cv::
                  certificate_rest`]
            compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_nth_eval))
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_object_cell0_atan_center_result_cv`
  >> conj_tac
  >- (irule
        (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          (Q.INST
            [`position` |-> `2`,
             `values` |->
               `bounded_case16594_object_cell0_atan_center_input_cv::
                  bounded_case16594_object_cell0_atan_box_input_cv::
                  bounded_case16594_object_cell0_atan_center_result_cv::
                  bounded_case16594_object_cell0_atan_center_square_cv::
                  bounded_case16594_object_cell0_atan_center_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_square_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_square_cv::
                  certificate_rest`]
            compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_nth_eval))
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_object_cell0_atan_center_square_cv`
  >> conj_tac
  >- (irule
        (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          (Q.INST
            [`position` |-> `3`,
             `values` |->
               `bounded_case16594_object_cell0_atan_center_input_cv::
                  bounded_case16594_object_cell0_atan_box_input_cv::
                  bounded_case16594_object_cell0_atan_center_result_cv::
                  bounded_case16594_object_cell0_atan_center_square_cv::
                  bounded_case16594_object_cell0_atan_center_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_square_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_square_cv::
                  certificate_rest`]
            compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_nth_eval))
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_object_cell0_atan_center_derivative_cv`
  >> conj_tac
  >- (irule
        (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          (Q.INST
            [`position` |-> `4`,
             `values` |->
               `bounded_case16594_object_cell0_atan_center_input_cv::
                  bounded_case16594_object_cell0_atan_box_input_cv::
                  bounded_case16594_object_cell0_atan_center_result_cv::
                  bounded_case16594_object_cell0_atan_center_square_cv::
                  bounded_case16594_object_cell0_atan_center_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_square_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_square_cv::
                  certificate_rest`]
            compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_nth_eval))
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_object_cell0_atan_box_square_cv`
  >> conj_tac
  >- (irule
        (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          (Q.INST
            [`position` |-> `5`,
             `values` |->
               `bounded_case16594_object_cell0_atan_center_input_cv::
                  bounded_case16594_object_cell0_atan_box_input_cv::
                  bounded_case16594_object_cell0_atan_center_result_cv::
                  bounded_case16594_object_cell0_atan_center_square_cv::
                  bounded_case16594_object_cell0_atan_center_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_square_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_square_cv::
                  certificate_rest`]
            compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_nth_eval))
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_object_cell0_atan_box_derivative_cv`
  >> conj_tac
  >- (irule
        (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          (Q.INST
            [`position` |-> `6`,
             `values` |->
               `bounded_case16594_object_cell0_atan_center_input_cv::
                  bounded_case16594_object_cell0_atan_box_input_cv::
                  bounded_case16594_object_cell0_atan_center_result_cv::
                  bounded_case16594_object_cell0_atan_center_square_cv::
                  bounded_case16594_object_cell0_atan_center_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_square_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_square_cv::
                  certificate_rest`]
            compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_nth_eval))
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_case16594_object_cell0_atan_box_derivative_square_cv`
  >> conj_tac
  >- (irule
        (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          (Q.INST
            [`position` |-> `7`,
             `values` |->
               `bounded_case16594_object_cell0_atan_center_input_cv::
                  bounded_case16594_object_cell0_atan_box_input_cv::
                  bounded_case16594_object_cell0_atan_center_result_cv::
                  bounded_case16594_object_cell0_atan_center_square_cv::
                  bounded_case16594_object_cell0_atan_center_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_square_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_cv::
                  bounded_case16594_object_cell0_atan_box_derivative_square_cv::
                  certificate_rest`]
            compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_nth_eval))
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_object_q_cv_list certificate_rest`
  >> conj_tac
  >- (mp_tac
        (Q.SPECL
          [`8`,
           `bounded_case16594_object_cell0_atan_center_input_cv::
              bounded_case16594_object_cell0_atan_box_input_cv::
              bounded_case16594_object_cell0_atan_center_result_cv::
              bounded_case16594_object_cell0_atan_center_square_cv::
              bounded_case16594_object_cell0_atan_center_derivative_cv::
              bounded_case16594_object_cell0_atan_box_square_cv::
              bounded_case16594_object_cell0_atan_box_derivative_cv::
              bounded_case16594_object_cell0_atan_box_derivative_square_cv::
              certificate_rest`,
           `clock - 10`,`refs`]
          compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_drop_eval)
      >> simp [compute_execTheory.from_cv_def]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedPackedObjectFinishEvalTheory.bounded_packed_compute_eval_if_true_result
  >> conj_tac
  >- (rewrite_tac
        [GSYM
          bounded_case16594_object_atan_step_state_check_expression_def]
      >> irule
           bounded_case16594_object_atan_step_state_check_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- simp
       [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectAtanStateEvalTheory.bounded_case16594_object_state_atan_eval
          >> simp
               [bounded_case16594_object_atan_certificate_outputs_encoded,
                compute_boundedCase16594ObjectNegEvalTheory.bounded_object_q_interval_encoded_packed]
          >> intLib.ARITH_TAC)
      >> simp
           [Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.compute_eval_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_snd_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

val _ = export_theory ();
