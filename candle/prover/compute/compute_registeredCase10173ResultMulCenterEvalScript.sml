(*****************************************************************************
 * Object refinement for the center jet of the historical Taylor product.
 *
 * This follows the literal source staging: project the two input center jets,
 * form the unrounded center product, scale both gradients, add those raw
 * lists, and assemble the unrounded first-order result.  Rounding remains at
 * the later [fs_result_complete_raw] boundary.
 *****************************************************************************)
Theory compute_registeredCase10173ResultMulCenterEval
Ancestors
  compute_registeredCase10173ResultMulEval
Libs
  bossLib preamble intLib

Definition registered_case10173_mul_result_object_cv_def:
  registered_case10173_mul_result_object_cv center_value center_gradient
      value_bound gradient_bounds hessian_rows =
    Pair (Num 1)
      (Pair
        (Pair (bounded_interval64_object_cv center_value)
          (bounded_interval64_object_cv_list center_gradient))
        (Pair (bounded_interval64_object_cv value_bound)
          (Pair (bounded_interval64_object_cv_list gradient_bounds)
            (bounded_interval64_object_cv_matrix hessian_rows))))
End

Theorem registered_case10173_mul_result_domain_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_domain»
        [from_cv
          (registered_case10173_mul_result_object_cv
            center_value64 center_gradient64 value_bound64 gradient_bounds64
            hessian_rows)]) (refs:hol_refs) =
    (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> PURE_REWRITE_TAC [registered_case10173_mul_result_object_cv_def]
  >> irule
       (Q.INST
         [`result_domain:cv` |-> `(Num 1:cv)`,
          `center:cv` |->
            `Pair (bounded_interval64_object_cv center_value64)
              (bounded_interval64_object_cv_list center_gradient64)`,
          `value_bound:cv` |->
            `bounded_interval64_object_cv value_bound64`,
          `gradient_bounds:cv` |->
            `bounded_interval64_object_cv_list gradient_bounds64`,
          `hessian:cv` |->
            `bounded_interval64_object_cv_matrix hessian_rows`]
         compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_domain_eval)
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_mul_result_center_value_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_value»
        [App «candle_cv_fs_result_center»
          [from_cv
            (registered_case10173_mul_result_object_cv
              center_value64 center_gradient64 value_bound64 gradient_bounds64
              hessian_rows)]]) (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv center_value64)),refs)
Proof
  strip_tac
  >> PURE_REWRITE_TAC [registered_case10173_mul_result_object_cv_def]
  >> irule
       (Q.INST
         [`result_domain:cv` |-> `(Num 1:cv)`,
          `center_value:cv` |->
            `bounded_interval64_object_cv center_value64`,
          `center_gradient:cv` |->
            `bounded_interval64_object_cv_list center_gradient64`,
          `value_bound:cv` |->
            `bounded_interval64_object_cv value_bound64`,
          `gradient_bounds:cv` |->
            `bounded_interval64_object_cv_list gradient_bounds64`,
          `hessian:cv` |->
            `bounded_interval64_object_cv_matrix hessian_rows`]
         compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_center_value_eval)
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_mul_result_center_gradient_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_gradient»
        [App «candle_cv_fs_result_center»
          [from_cv
            (registered_case10173_mul_result_object_cv
              center_value64 center_gradient64 value_bound64 gradient_bounds64
              hessian_rows)]]) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_list center_gradient64)),refs)
Proof
  strip_tac
  >> PURE_REWRITE_TAC [registered_case10173_mul_result_object_cv_def]
  >> irule
       (Q.INST
         [`result_domain:cv` |-> `(Num 1:cv)`,
          `center_value:cv` |->
            `bounded_interval64_object_cv center_value64`,
          `center_gradient:cv` |->
            `bounded_interval64_object_cv_list center_gradient64`,
          `value_bound:cv` |->
            `bounded_interval64_object_cv value_bound64`,
          `gradient_bounds:cv` |->
            `bounded_interval64_object_cv_list gradient_bounds64`,
          `hessian:cv` |->
            `bounded_interval64_object_cv_matrix hessian_rows`]
         compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_center_gradient_eval)
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_mul_true_domain_object_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);
         («left»,from_cv
           (registered_case10173_mul_result_object_cv
             left_center_value left_center_gradient left_value_bound
             left_gradient_bounds left_hessian_rows));
         («right»,from_cv
           (registered_case10173_mul_result_object_cv
             right_center_value right_center_gradient right_value_bound
             right_gradient_bounds right_hessian_rows))]
        registered_case10173_fs_result_mul_domain_body) (refs:hol_refs) =
    (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> simp
       [registered_case10173_fs_result_mul_domain_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173RawWrapperEvalTheory.registered_case10173_bool_and_true_one_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (PURE_REWRITE_TAC [GSYM compute_execTheory.from_cv_def]
      >> irule registered_case10173_mul_result_domain_eval
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [GSYM compute_execTheory.from_cv_def]
  >> irule registered_case10173_mul_result_domain_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_result_mul_center_value_object_eval:
  bounded_object_fs_raw_interval_mul
      (bounded_interval64_object_cv left_center_value)
      (bounded_interval64_object_cv right_center_value) =
    SOME (Pair raw_center_lower raw_center_upper) /\
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_mul»
        [App «candle_cv_fs_first_value»
           [App «candle_cv_fs_result_center»
             [from_cv
               (registered_case10173_mul_result_object_cv
                 left_center_value left_center_gradient left_value_bound
                 left_gradient_bounds left_hessian_rows)]];
         App «candle_cv_fs_first_value»
           [App «candle_cv_fs_result_center»
             [from_cv
               (registered_case10173_mul_result_object_cv
                 right_center_value right_center_gradient right_value_bound
                 right_gradient_bounds right_hessian_rows)]]]) (refs:hol_refs) =
    (M_success (from_cv (Pair raw_center_lower raw_center_upper)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_mul»
            [from_cv (bounded_interval64_object_cv left_center_value);
             from_cv (bounded_interval64_object_cv right_center_value)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule registered_case10173_mul_result_center_value_eval
          >> intLib.ARITH_TAC)
      >> irule registered_case10173_mul_result_center_value_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_raw_interval_mul_eval
  >> simp []
QED

Theorem registered_case10173_fs_result_mul_gradient_scale_object_eval:
  registered_case10173_fs_raw_interval_list_scale_object
      (bounded_interval64_object_cv scalar_center_value)
      (MAP bounded_interval64_object_cv vector_center_gradient) =
    SOME raw_gradient /\
  LENGTH vector_center_gradient + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_list_scale»
        [App «candle_cv_fs_first_value»
           [App «candle_cv_fs_result_center»
             [from_cv
               (registered_case10173_mul_result_object_cv
                 scalar_center_value scalar_center_gradient
                 scalar_value_bound scalar_gradient_bounds
                 scalar_hessian_rows)]];
         App «candle_cv_fs_first_gradient»
           [App «candle_cv_fs_result_center»
             [from_cv
               (registered_case10173_mul_result_object_cv
                 vector_center_value vector_center_gradient
                 vector_value_bound vector_gradient_bounds
                 vector_hessian_rows)]]]) (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_list raw_gradient)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_list_scale»
            [from_cv (bounded_interval64_object_cv scalar_center_value);
             from_cv
               (bounded_interval64_object_cv_list
                 vector_center_gradient)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule registered_case10173_mul_result_center_value_eval
          >> intLib.ARITH_TAC)
      >> irule registered_case10173_mul_result_center_gradient_eval
      >> intLib.ARITH_TAC)
  >> rw
       [GSYM compute_registeredCase10173HistoricalListScaleRefinementTheory.registered_case10173_cv_list_map_bounded_interval64_object_cv]
  >> irule
       compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_result_mul_center_gradient_object_eval:
  registered_case10173_fs_raw_interval_list_scale_object
      (bounded_interval64_object_cv right_center_value)
      (MAP bounded_interval64_object_cv left_center_gradient) =
    SOME raw_left_gradient /\
  registered_case10173_fs_raw_interval_list_scale_object
      (bounded_interval64_object_cv left_center_value)
      (MAP bounded_interval64_object_cv right_center_gradient) =
    SOME raw_right_gradient /\
  registered_case10173_fs_raw_interval_list_add_object
      raw_left_gradient raw_right_gradient = SOME raw_center_gradient /\
  LENGTH left_center_gradient + 6 < clock /\
  LENGTH right_center_gradient + 6 < clock /\
  LENGTH raw_left_gradient + 6 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_list_add»
        [App «candle_cv_fs_raw_interval_list_scale»
           [App «candle_cv_fs_first_value»
              [App «candle_cv_fs_result_center»
                [from_cv
                  (registered_case10173_mul_result_object_cv
                    right_center_value right_center_gradient
                    right_value_bound right_gradient_bounds
                    right_hessian_rows)]];
            App «candle_cv_fs_first_gradient»
              [App «candle_cv_fs_result_center»
                [from_cv
                  (registered_case10173_mul_result_object_cv
                    left_center_value left_center_gradient
                    left_value_bound left_gradient_bounds
                    left_hessian_rows)]]];
         App «candle_cv_fs_raw_interval_list_scale»
           [App «candle_cv_fs_first_value»
              [App «candle_cv_fs_result_center»
                [from_cv
                  (registered_case10173_mul_result_object_cv
                    left_center_value left_center_gradient
                    left_value_bound left_gradient_bounds
                    left_hessian_rows)]];
            App «candle_cv_fs_first_gradient»
              [App «candle_cv_fs_result_center»
                [from_cv
                  (registered_case10173_mul_result_object_cv
                    right_center_value right_center_gradient
                    right_value_bound right_gradient_bounds
                    right_hessian_rows)]]]]) (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_list raw_center_gradient)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_list_add»
            [from_cv (registered_case10173_cv_list raw_left_gradient);
             from_cv
               (registered_case10173_cv_list raw_right_gradient)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >> irule registered_case10173_fs_result_mul_gradient_scale_object_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalRawListAddEvalTheory.registered_case10173_fs_raw_interval_list_add_object_eval
  >> simp []
QED

Theorem registered_case10173_fs_result_mul_center_object_eval:
  bounded_object_fs_raw_interval_mul
      (bounded_interval64_object_cv left_center_value)
      (bounded_interval64_object_cv right_center_value) =
    SOME (Pair raw_center_lower raw_center_upper) /\
  registered_case10173_fs_raw_interval_list_scale_object
      (bounded_interval64_object_cv right_center_value)
      (MAP bounded_interval64_object_cv left_center_gradient) =
    SOME raw_left_gradient /\
  registered_case10173_fs_raw_interval_list_scale_object
      (bounded_interval64_object_cv left_center_value)
      (MAP bounded_interval64_object_cv right_center_gradient) =
    SOME raw_right_gradient /\
  registered_case10173_fs_raw_interval_list_add_object
      raw_left_gradient raw_right_gradient = SOME raw_center_gradient /\
  LENGTH left_center_gradient + 7 < clock /\
  LENGTH right_center_gradient + 7 < clock /\
  LENGTH raw_left_gradient + 7 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);
         («left»,from_cv
           (registered_case10173_mul_result_object_cv
             left_center_value left_center_gradient left_value_bound
             left_gradient_bounds left_hessian_rows));
         («right»,from_cv
           (registered_case10173_mul_result_object_cv
             right_center_value right_center_gradient right_value_bound
             right_gradient_bounds right_hessian_rows))]
        registered_case10173_fs_result_mul_center_body) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Pair raw_center_lower raw_center_upper)
          (registered_case10173_cv_list raw_center_gradient))),refs)
Proof
  strip_tac
  >> simp
       [registered_case10173_fs_result_mul_center_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_first_make»
            [from_cv (Pair raw_center_lower raw_center_upper);
             from_cv
               (registered_case10173_cv_list raw_center_gradient)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule registered_case10173_fs_result_mul_center_value_object_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> irule registered_case10173_fs_result_mul_center_gradient_object_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [GSYM compute_execTheory.from_cv_def]
  >> irule
       compute_registeredCase10173HistoricalBasicEvalTheory.registered_case10173_fs_first_make_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
