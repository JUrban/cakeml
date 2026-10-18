(*****************************************************************************
 * Authenticated evaluator semantics for the generic historical root record.
 *
 * The registered wrapper recomputes its four root inputs.  In particular,
 * its center delta uses the literal source-shaped arithmetic, not the
 * separately rounded production delta.  The strengthened packet checker now
 * authenticates that source result explicitly; this theory connects the
 * resulting word certificates to the registered object evaluator.
 *****************************************************************************)
Theory compute_registeredCase10173RootRecordAuthenticatedEval
Ancestors
  compute_boundedCase10173PackedDecimalBatch
  compute_registeredCase10173HistoricalSourceDeltaGeneralEval
  compute_registeredCase10173HistoricalDeltaSecondEval
  compute_registeredCase10173RootRecordEval
  compute_registeredCase10173CenterEnvironmentEval
  compute_registeredCase10173QConversionEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_raw_scale_four_endpoint_exact:
  bounded_signed64_normalized value /\
  bounded_signed64_add value value = SOME twice /\
  bounded_signed64_add twice twice = SOME target ==>
  bounded_object_fs_raw_scale 4 (bounded_signed64_object_cv value) =
    SOME (bounded_signed64_object_cv target)
Proof
  rpt strip_tac
  >> Cases_on `value`
  >> rename1 `BoundedSigned64 negative magnitude`
  >> Cases_on `negative`
  >> simp
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_scale_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> imp_res_tac
       compute_boundedSignedEndpointAddTheory.bounded_signed64_add_value
  >> Cases_on `target`
  >> rename1 `BoundedSigned64 target_negative target_magnitude`
  >> Cases_on `target_negative`
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
        integerTheory.INT_OF_NUM_EQ]
  >> TRY
       (irule (iffLR integerTheory.INT_OF_NUM_EQ)
        >> simp [integerTheory.INT_OF_NUM_MUL]
        >> intLib.ARITH_TAC)
  >> TRY
       (`0 < w2n target_magnitude` by
          simp
            [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,
             wordsTheory.w2n_eq_0]
        >> intLib.ARITH_TAC)
  >> TRY
       (`0 < w2n magnitude` by
          simp
            [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,
             wordsTheory.w2n_eq_0]
        >> intLib.ARITH_TAC)
QED

Theorem registered_case10173_interval_scale_four_object_typed_exact:
  bounded_interval64_scale4 input = SOME output ==>
  registered_case10173_fs_interval_raw_scale_object 4
      (bounded_interval64_object_cv input) =
    SOME (bounded_interval64_object_cv output)
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> rw
       [compute_boundedDeltaTaylorTheory.bounded_interval64_scale4_def]
  >> every_case_tac
  >> gvs []
  >> Cases_on `x`
  >> fs
       [compute_boundedIntervalAddTheory.bounded_interval64_add_def,
        compute_boundedIntervalAddTheory.bounded_interval64_add_unchecked_def]
  >> every_case_tac
  >> gvs []
  >> fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_interval_raw_scale_object_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def]
  >> imp_res_tac registered_case10173_raw_scale_four_endpoint_exact
  >> gvs []
QED

Theorem registered_case10173_positive_root_certificate_object_eval:
  bounded_interval64_positive_sqrt_certificate_decimal input root /\
  40 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_root_certificate»
        [from_cv (bounded_interval64_object_cv input);
         from_cv (bounded_interval64_object_cv root)])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  rpt strip_tac
  >> imp_res_tac
       compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_sqrt_certificate_decimal_object_exact
  >> Cases_on `input`
  >> Cases_on `root`
  >> Cases_on `b`
  >> Cases_on `b0`
  >> Cases_on `b'`
  >> Cases_on `b0'`
  >> rename1
       `bounded_interval64_positive_sqrt_certificate_decimal
          (BoundedInterval64
            (BoundedSigned64 input_lower_negative input_lower_magnitude)
            (BoundedSigned64 input_upper_negative input_upper_magnitude))
          (BoundedInterval64
            (BoundedSigned64 root_lower_negative root_lower_magnitude)
            (BoundedSigned64 root_upper_negative root_upper_magnitude))`
  >> imp_res_tac
       compute_boundedCertificateDecimalTheory.bounded_interval64_sqrt_certificate_decimal_nonnegative
  >> Cases_on `input_lower_negative`
  >> Cases_on `input_upper_negative`
  >> Cases_on `root_lower_negative`
  >> Cases_on `root_upper_negative`
  >> gvs
       [compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_sqrt_certificate_decimal_def,
        compute_boundedCertificateDecimalTheory.bounded_interval64_sqrt_certificate_decimal_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
        compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_positive_root_certificate_eval)
  >> simp []
QED

Theorem registered_case10173_interval_scale_four_object_eval:
  bounded_interval64_scale4 input = SOME output /\
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_scale»
        [Num 4;from_cv (bounded_interval64_object_cv input)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv output)),refs)
Proof
  rpt strip_tac
  >> imp_res_tac registered_case10173_interval_scale_four_object_typed_exact
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_object_eval)
  >> simp []
QED

Theorem registered_case10173_interval_scale_four_head_eval:
  bounded_interval64_scale4 x0 = SOME four_x0 /\
  5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_scale»
        [Num 4;
         App «candle_cv_fs_interval_lookup»
           [Num 0;
            from_cv
              (bounded_interval64_object_cv_list
                [x0;x1;x2;x3;x4;x5])]])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv four_x0)),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_scale»
            [Num 4;from_cv (bounded_interval64_object_cv x0)]) refs`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`result1:cv` |-> `Num 4`,
             `result2:cv` |-> `bounded_interval64_object_cv x0`]
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results))
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> PURE_REWRITE_TAC
           [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
            compute_execTheory.from_cv_def]
      >> irule
           (SIMP_RULE std_ss
             [compute_execTheory.from_cv_def,
              compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
             (Q.INST
               [`index` |-> `0`,
                `values` |->
                  `[bounded_interval64_object_cv x0;
                    bounded_interval64_object_cv x1;
                    bounded_interval64_object_cv x2;
                    bounded_interval64_object_cv x3;
                    bounded_interval64_object_cv x4;
                    bounded_interval64_object_cv x5]`,
                `result:cv` |-> `bounded_interval64_object_cv x0`]
               compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval))
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule registered_case10173_interval_scale_four_object_eval
  >> simp []
QED

Theorem registered_case10173_hist_delta_second_value_typed_eval:
  bounded_historical_delta_second_decimal environment =
      SOME (value,gradient,hessian) /\
  bounded_hessian64_rows hessian = SOME rows /\
  180 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_value»
        [App «candle_cv_fs_hist_delta_second»
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
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_registeredCase10173HistoricalDeltaSecondEvalTheory.registered_case10173_fs_hist_delta_second_typed_eval
      >> simp [])
  >> irule
       compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_hist_second_value_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_hist_root_inputs_typed_eval:
  registered_case10173_q_center_environment_positive boxes =
      SOME center_boxes /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME [cx0;cx1;cx2;cx3;cx4;cx5] /\
  bounded_object_positive_q_interval64_decimal_list boxes =
      SOME [bx0;bx1;bx2;bx3;bx4;bx5] /\
  bounded_source_delta64_value_decimal [cx0;cx1;cx2;cx3;cx4;cx5] =
      SOME center_delta /\
  bounded_interval64_scale4 cx0 = SOME center_four_x0 /\
  bounded_historical_delta_second_decimal [bx0;bx1;bx2;bx3;bx4;bx5] =
      SOME (box_delta,box_gradient,box_hessian) /\
  bounded_hessian64_rows box_hessian = SOME box_hessian_rows /\
  bounded_interval64_scale4 bx0 = SOME box_four_x0 /\
  1000 + 8 * (cv_size boxes + 1) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_root_inputs» [from_cv boxes])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (bounded_interval64_object_cv center_delta)
          (Pair (bounded_interval64_object_cv center_four_x0)
            (Pair (bounded_interval64_object_cv box_delta)
              (Pair (bounded_interval64_object_cv box_four_x0)
                (Num 0)))))),refs)
Proof
  rpt strip_tac
  >> rw
       [compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_root_inputs_unfold]
  >> simp
       [compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_root_inputs_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv center_boxes`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_center_environment_positive_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv_list
            [cx0;cx1;cx2;cx3;cx4;cx5])`
  >> conj_tac
  >- (irule
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_interval_list_of_q_object_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv_list
            [bx0;bx1;bx2;bx3;bx4;bx5])`
  >> conj_tac
  >- (irule
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_interval_list_of_q_object_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result:cv` |-> `bounded_interval64_object_cv center_delta`,
            `right_result:cv` |->
              `Pair (bounded_interval64_object_cv center_four_x0)
                (Pair (bounded_interval64_object_cv box_delta)
                  (Pair (bounded_interval64_object_cv box_four_x0)
                    (Num 0)))`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalSourceDeltaGeneralEvalTheory.registered_case10173_source_delta64_value_decimal_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result:cv` |->
              `bounded_interval64_object_cv center_four_x0`,
            `right_result:cv` |->
              `Pair (bounded_interval64_object_cv box_delta)
                (Pair (bounded_interval64_object_cv box_four_x0)
                  (Num 0))`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (irule registered_case10173_interval_scale_four_head_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result:cv` |-> `bounded_interval64_object_cv box_delta`,
            `right_result:cv` |->
              `Pair (bounded_interval64_object_cv box_four_x0) (Num 0)`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (irule registered_case10173_hist_delta_second_value_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result:cv` |->
              `bounded_interval64_object_cv box_four_x0`,
            `right_result:cv` |-> `Num 0`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (irule registered_case10173_interval_scale_four_head_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_execTheory.from_cv_def,
        compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
