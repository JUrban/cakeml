(*****************************************************************************
 * Packet-parametric fixed Taylor result handoff.
 *
 * This composes the structural accessors and recursive fixed-to-rational
 * conversions into the exact result consumed by the legacy certified finish.
 *****************************************************************************)
Theory compute_registeredCase10173FixedResultHandoffEval
Ancestors
  compute_registeredCase10173FixedResultConstructorsEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fixed_q_taylor_object_cv_def:
  registered_case10173_fixed_q_taylor_object_cv
      (BoundedTaylor64 result_domain center_value center_gradient
        value_bound gradient_bounds hessian) rows =
    Pair (bounded_bool_object_cv result_domain)
      (Pair
        (Pair (registered_case10173_fixed_q_interval_cv center_value)
          (registered_case10173_fixed_q_interval_list_cv center_gradient))
        (Pair (registered_case10173_fixed_q_interval_cv value_bound)
          (Pair
            (registered_case10173_fixed_q_interval_list_cv gradient_bounds)
            (registered_case10173_fixed_q_interval_matrix_cv rows))))
End

Definition registered_case10173_fs_result_to_q_body_def:
  registered_case10173_fs_result_to_q_body =
    App «candle_cv_q_dim_taylor_model_result_make»
      [App «candle_cv_fs_result_domain» [Var «result»];
       App «candle_cv_q_dim_first_jet_make»
         [App «candle_cv_fs_interval_to_q»
            [App «candle_cv_fs_first_value»
              [App «candle_cv_fs_result_center» [Var «result»]]];
          App «candle_cv_fs_interval_list_to_q»
            [App «candle_cv_fs_first_gradient»
              [App «candle_cv_fs_result_center» [Var «result»]]]];
       App «candle_cv_fs_interval_to_q»
         [App «candle_cv_fs_result_value_bound» [Var «result»]];
       App «candle_cv_fs_interval_list_to_q»
         [App «candle_cv_fs_result_gradient_bounds» [Var «result»]];
       App «candle_cv_fs_interval_matrix_to_q»
         [App «candle_cv_fs_result_hessian» [Var «result»]]]
End

Theorem registered_case10173_fs_result_to_q_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_to_q» =
    SOME ([«result»],registered_case10173_fs_result_to_q_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_to_q_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_to_q» [from_cv result])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«result»,from_cv result)]
        registered_case10173_fs_result_to_q_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_result_to_q_lookup]
QED

Theorem registered_case10173_fs_result_value_bound_normalized_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_value_bound»
        [Pair (from_cv encoded_domain)
          (Pair (from_cv encoded_center)
            (Pair (from_cv encoded_value_bound)
              (Pair (from_cv encoded_gradient_bounds)
                (from_cv encoded_hessian))))])
      (refs:hol_refs) =
    (M_success (from_cv encoded_value_bound),refs)
Proof
  ACCEPT_TAC
    (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
      (Q.INST
        [`result_domain` |-> `encoded_domain`,
         `center` |-> `encoded_center`,
         `value_bound` |-> `encoded_value_bound`,
         `gradient_bounds` |-> `encoded_gradient_bounds`,
         `hessian` |-> `encoded_hessian`]
        compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_value_bound_eval))
QED

Theorem registered_case10173_fs_result_gradient_bounds_normalized_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_gradient_bounds»
        [Pair (from_cv encoded_domain)
          (Pair (from_cv encoded_center)
            (Pair (from_cv encoded_value_bound)
              (Pair (from_cv encoded_gradient_bounds)
                (from_cv encoded_hessian))))])
      (refs:hol_refs) =
    (M_success (from_cv encoded_gradient_bounds),refs)
Proof
  ACCEPT_TAC
    (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
      (Q.INST
        [`result_domain` |-> `encoded_domain`,
         `center` |-> `encoded_center`,
         `value_bound` |-> `encoded_value_bound`,
         `gradient_bounds` |-> `encoded_gradient_bounds`,
         `hessian` |-> `encoded_hessian`]
        compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_gradient_bounds_eval))
QED

Theorem registered_case10173_fs_result_value_bound_taylor_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_value_bound»
        [from_cv
          (bounded_taylor64_rows_object_cv
            (BoundedTaylor64 result_domain center_value center_gradient
              value_bound gradient_bounds hessian) rows)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv value_bound)),refs)
Proof
  simp
    [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_taylor64_rows_object_cv_def]
  >> ACCEPT_TAC
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`encoded_domain` |-> `bounded_bool_object_cv result_domain`,
            `encoded_center` |->
              `Pair (bounded_interval64_object_cv center_value)
                (bounded_interval64_object_cv_list center_gradient)`,
            `encoded_value_bound` |->
              `bounded_interval64_object_cv value_bound`,
            `encoded_gradient_bounds` |->
              `bounded_interval64_object_cv_list gradient_bounds`,
            `encoded_hessian` |-> `bounded_interval64_object_cv_matrix rows`]
           registered_case10173_fs_result_value_bound_normalized_eval))
QED

Theorem registered_case10173_fs_result_gradient_bounds_taylor_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_gradient_bounds»
        [from_cv
          (bounded_taylor64_rows_object_cv
            (BoundedTaylor64 result_domain center_value center_gradient
              value_bound gradient_bounds hessian) rows)])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_list gradient_bounds)),refs)
Proof
  simp
    [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_taylor64_rows_object_cv_def]
  >> ACCEPT_TAC
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`encoded_domain` |-> `bounded_bool_object_cv result_domain`,
            `encoded_center` |->
              `Pair (bounded_interval64_object_cv center_value)
                (bounded_interval64_object_cv_list center_gradient)`,
            `encoded_value_bound` |->
              `bounded_interval64_object_cv value_bound`,
            `encoded_gradient_bounds` |->
              `bounded_interval64_object_cv_list gradient_bounds`,
            `encoded_hessian` |-> `bounded_interval64_object_cv_matrix rows`]
           registered_case10173_fs_result_gradient_bounds_normalized_eval))
QED

Theorem registered_case10173_fs_result_hessian_taylor_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_hessian»
        [from_cv
          (bounded_taylor64_rows_object_cv
            (BoundedTaylor64 result_domain center_value center_gradient
              value_bound gradient_bounds hessian) rows)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv_matrix rows)),refs)
Proof
  strip_tac
  >> PURE_ONCE_REWRITE_TAC
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_taylor64_rows_object_cv_def]
  >> irule
       compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_hessian_eval
  >> simp []
QED

Theorem registered_case10173_fs_result_domain_taylor_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_domain»
        [from_cv
          (bounded_taylor64_rows_object_cv
            (BoundedTaylor64 result_domain center_value center_gradient
              value_bound gradient_bounds hessian) rows)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_bool_object_cv result_domain)),refs)
Proof
  strip_tac
  >> PURE_ONCE_REWRITE_TAC
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_taylor64_rows_object_cv_def]
  >> irule
       compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_domain_eval
  >> simp []
QED

Theorem registered_case10173_fs_result_center_value_to_q_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_to_q»
        [App «candle_cv_fs_first_value»
          [App «candle_cv_fs_result_center»
            [from_cv
              (bounded_taylor64_rows_object_cv
                (BoundedTaylor64 result_domain center_value center_gradient
                  value_bound gradient_bounds hessian) rows)]]])
      (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_fixed_q_interval_cv center_value)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_first_value»
          [App «candle_cv_fs_result_center»
            [from_cv
              (bounded_taylor64_rows_object_cv
                (BoundedTaylor64 result_domain center_value center_gradient
                  value_bound gradient_bounds hessian) rows)]]) refs =
      (M_success (from_cv (bounded_interval64_object_cv center_value)),refs)` by
       (simp
          [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_taylor64_rows_object_cv_def]
        >> irule
             compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_center_value_normalized_eval
        >> intLib.ARITH_TAC)
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_to_q»
          [App «candle_cv_fs_first_value»
            [App «candle_cv_fs_result_center»
              [from_cv
                (bounded_taylor64_rows_object_cv
                  (BoundedTaylor64 result_domain center_value center_gradient
                    value_bound gradient_bounds hessian) rows)]]]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_to_q»
          [from_cv (bounded_interval64_object_cv center_value)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp [])
  >> rw []
  >> irule
       compute_registeredCase10173FixedResultToQEvalTheory.registered_case10173_fs_interval_to_q_typed_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_result_center_gradient_to_q_eval:
  LENGTH center_gradient + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_to_q»
        [App «candle_cv_fs_first_gradient»
          [App «candle_cv_fs_result_center»
            [from_cv
              (bounded_taylor64_rows_object_cv
                (BoundedTaylor64 result_domain center_value center_gradient
                  value_bound gradient_bounds hessian) rows)]]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_fixed_q_interval_list_cv center_gradient)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_first_gradient»
          [App «candle_cv_fs_result_center»
            [from_cv
              (bounded_taylor64_rows_object_cv
                (BoundedTaylor64 result_domain center_value center_gradient
                  value_bound gradient_bounds hessian) rows)]]) refs =
      (M_success
        (from_cv (bounded_interval64_object_cv_list center_gradient)),refs)` by
       (simp
          [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_taylor64_rows_object_cv_def]
        >> irule
             compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_center_gradient_normalized_eval
        >> intLib.ARITH_TAC)
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_to_q»
          [App «candle_cv_fs_first_gradient»
            [App «candle_cv_fs_result_center»
              [from_cv
                (bounded_taylor64_rows_object_cv
                  (BoundedTaylor64 result_domain center_value center_gradient
                    value_bound gradient_bounds hessian) rows)]]]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_to_q»
          [from_cv (bounded_interval64_object_cv_list center_gradient)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp [])
  >> rw []
  >> irule
       compute_registeredCase10173FixedResultToQEvalTheory.registered_case10173_fs_interval_list_to_q_typed_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_result_value_bound_to_q_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_to_q»
        [App «candle_cv_fs_result_value_bound»
          [from_cv
            (bounded_taylor64_rows_object_cv
              (BoundedTaylor64 result_domain center_value center_gradient
                value_bound gradient_bounds hessian) rows)]])
      (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_fixed_q_interval_cv value_bound)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_result_value_bound»
          [from_cv
            (bounded_taylor64_rows_object_cv
              (BoundedTaylor64 result_domain center_value center_gradient
                value_bound gradient_bounds hessian) rows)]) refs =
      (M_success (from_cv (bounded_interval64_object_cv value_bound)),refs)` by
       (irule registered_case10173_fs_result_value_bound_taylor_eval
        >> intLib.ARITH_TAC)
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_to_q»
          [App «candle_cv_fs_result_value_bound»
            [from_cv
              (bounded_taylor64_rows_object_cv
                (BoundedTaylor64 result_domain center_value center_gradient
                  value_bound gradient_bounds hessian) rows)]]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_to_q»
          [from_cv (bounded_interval64_object_cv value_bound)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp [])
  >> rw []
  >> irule
       compute_registeredCase10173FixedResultToQEvalTheory.registered_case10173_fs_interval_to_q_typed_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_result_gradient_bounds_to_q_eval:
  LENGTH gradient_bounds + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_to_q»
        [App «candle_cv_fs_result_gradient_bounds»
          [from_cv
            (bounded_taylor64_rows_object_cv
              (BoundedTaylor64 result_domain center_value center_gradient
                value_bound gradient_bounds hessian) rows)]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_fixed_q_interval_list_cv gradient_bounds)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_result_gradient_bounds»
          [from_cv
            (bounded_taylor64_rows_object_cv
              (BoundedTaylor64 result_domain center_value center_gradient
                value_bound gradient_bounds hessian) rows)]) refs =
      (M_success
        (from_cv (bounded_interval64_object_cv_list gradient_bounds)),refs)` by
       (irule registered_case10173_fs_result_gradient_bounds_taylor_eval
        >> intLib.ARITH_TAC)
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_to_q»
          [App «candle_cv_fs_result_gradient_bounds»
            [from_cv
              (bounded_taylor64_rows_object_cv
                (BoundedTaylor64 result_domain center_value center_gradient
                  value_bound gradient_bounds hessian) rows)]]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_to_q»
          [from_cv (bounded_interval64_object_cv_list gradient_bounds)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp [])
  >> rw []
  >> irule
       compute_registeredCase10173FixedResultToQEvalTheory.registered_case10173_fs_interval_list_to_q_typed_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_result_hessian_to_q_eval:
  SUM (MAP LENGTH rows) + LENGTH rows + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_matrix_to_q»
        [App «candle_cv_fs_result_hessian»
          [from_cv
            (bounded_taylor64_rows_object_cv
              (BoundedTaylor64 result_domain center_value center_gradient
                value_bound gradient_bounds hessian) rows)]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_fixed_q_interval_matrix_cv rows)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_result_hessian»
          [from_cv
            (bounded_taylor64_rows_object_cv
              (BoundedTaylor64 result_domain center_value center_gradient
                value_bound gradient_bounds hessian) rows)]) refs =
      (M_success (from_cv (bounded_interval64_object_cv_matrix rows)),refs)` by
       (irule registered_case10173_fs_result_hessian_taylor_eval
        >> intLib.ARITH_TAC)
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_matrix_to_q»
          [App «candle_cv_fs_result_hessian»
            [from_cv
              (bounded_taylor64_rows_object_cv
                (BoundedTaylor64 result_domain center_value center_gradient
                  value_bound gradient_bounds hessian) rows)]]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_matrix_to_q»
          [from_cv (bounded_interval64_object_cv_matrix rows)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp [])
  >> rw []
  >> irule
       compute_registeredCase10173FixedResultToQEvalTheory.registered_case10173_fs_interval_matrix_to_q_typed_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_result_center_first_to_q_eval:
  LENGTH center_gradient + 6 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_first_jet_make»
        [App «candle_cv_fs_interval_to_q»
           [App «candle_cv_fs_first_value»
             [App «candle_cv_fs_result_center»
               [from_cv
                 (bounded_taylor64_rows_object_cv
                   (BoundedTaylor64 result_domain center_value
                     center_gradient value_bound gradient_bounds hessian)
                   rows)]]];
         App «candle_cv_fs_interval_list_to_q»
           [App «candle_cv_fs_first_gradient»
             [App «candle_cv_fs_result_center»
               [from_cv
                 (bounded_taylor64_rows_object_cv
                   (BoundedTaylor64 result_domain center_value
                     center_gradient value_bound gradient_bounds hessian)
                   rows)]]]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (registered_case10173_fixed_q_interval_cv center_value)
          (registered_case10173_fixed_q_interval_list_cv center_gradient))),
     refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_dim_first_jet_make»
            [from_cv (registered_case10173_fixed_q_interval_cv center_value);
             from_cv
               (registered_case10173_fixed_q_interval_list_cv
                 center_gradient)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule registered_case10173_fs_result_center_value_to_q_eval
          >> intLib.ARITH_TAC)
      >> irule registered_case10173_fs_result_center_gradient_to_q_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173FixedResultConstructorsEvalTheory.registered_case10173_q_first_jet_make_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_result_to_q_body_subst:
  subst
      [(«result»,
        from_cv
          (bounded_taylor64_rows_object_cv
            (BoundedTaylor64 result_domain center_value center_gradient
              value_bound gradient_bounds hessian) rows))]
      registered_case10173_fs_result_to_q_body =
    App «candle_cv_q_dim_taylor_model_result_make»
      [App «candle_cv_fs_result_domain»
         [from_cv
           (bounded_taylor64_rows_object_cv
             (BoundedTaylor64 result_domain center_value center_gradient
               value_bound gradient_bounds hessian) rows)];
       App «candle_cv_q_dim_first_jet_make»
         [App «candle_cv_fs_interval_to_q»
            [App «candle_cv_fs_first_value»
              [App «candle_cv_fs_result_center»
                [from_cv
                  (bounded_taylor64_rows_object_cv
                    (BoundedTaylor64 result_domain center_value
                      center_gradient value_bound gradient_bounds hessian)
                    rows)]]];
          App «candle_cv_fs_interval_list_to_q»
            [App «candle_cv_fs_first_gradient»
              [App «candle_cv_fs_result_center»
                [from_cv
                  (bounded_taylor64_rows_object_cv
                    (BoundedTaylor64 result_domain center_value
                      center_gradient value_bound gradient_bounds hessian)
                    rows)]]]];
       App «candle_cv_fs_interval_to_q»
         [App «candle_cv_fs_result_value_bound»
           [from_cv
             (bounded_taylor64_rows_object_cv
               (BoundedTaylor64 result_domain center_value center_gradient
                 value_bound gradient_bounds hessian) rows)]];
       App «candle_cv_fs_interval_list_to_q»
         [App «candle_cv_fs_result_gradient_bounds»
           [from_cv
             (bounded_taylor64_rows_object_cv
               (BoundedTaylor64 result_domain center_value center_gradient
                 value_bound gradient_bounds hessian) rows)]];
       App «candle_cv_fs_interval_matrix_to_q»
         [App «candle_cv_fs_result_hessian»
           [from_cv
             (bounded_taylor64_rows_object_cv
               (BoundedTaylor64 result_domain center_value center_gradient
                 value_bound gradient_bounds hessian) rows)]]]
Proof
  simp
    [registered_case10173_fs_result_to_q_body_def,
     compute_evalTheory.subst_def]
QED

Theorem registered_case10173_fs_result_to_q_typed_eval:
  LENGTH center_gradient + 7 < clock /\
  LENGTH gradient_bounds + 6 < clock /\
  SUM (MAP LENGTH rows) + LENGTH rows + 6 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_to_q»
        [from_cv
          (bounded_taylor64_rows_object_cv
            (BoundedTaylor64 result_domain center_value center_gradient
              value_bound gradient_bounds hessian) rows)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_fixed_q_taylor_object_cv
          (BoundedTaylor64 result_domain center_value center_gradient
            value_bound gradient_bounds hessian) rows)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_result_to_q_unfold]
  >> simp_tac std_ss [registered_case10173_fs_result_to_q_body_subst]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_dim_taylor_model_result_make»
          [App «candle_cv_fs_result_domain»
             [from_cv
               (bounded_taylor64_rows_object_cv
                 (BoundedTaylor64 result_domain center_value center_gradient
                   value_bound gradient_bounds hessian) rows)];
           App «candle_cv_q_dim_first_jet_make»
             [App «candle_cv_fs_interval_to_q»
                [App «candle_cv_fs_first_value»
                  [App «candle_cv_fs_result_center»
                    [from_cv
                      (bounded_taylor64_rows_object_cv
                        (BoundedTaylor64 result_domain center_value
                          center_gradient value_bound gradient_bounds hessian)
                        rows)]]];
              App «candle_cv_fs_interval_list_to_q»
                [App «candle_cv_fs_first_gradient»
                  [App «candle_cv_fs_result_center»
                    [from_cv
                      (bounded_taylor64_rows_object_cv
                        (BoundedTaylor64 result_domain center_value
                          center_gradient value_bound gradient_bounds hessian)
                        rows)]]]];
           App «candle_cv_fs_interval_to_q»
             [App «candle_cv_fs_result_value_bound»
               [from_cv
                 (bounded_taylor64_rows_object_cv
                   (BoundedTaylor64 result_domain center_value
                     center_gradient value_bound gradient_bounds hessian)
                   rows)]];
           App «candle_cv_fs_interval_list_to_q»
             [App «candle_cv_fs_result_gradient_bounds»
               [from_cv
                 (bounded_taylor64_rows_object_cv
                   (BoundedTaylor64 result_domain center_value
                     center_gradient value_bound gradient_bounds hessian)
                   rows)]];
           App «candle_cv_fs_interval_matrix_to_q»
             [App «candle_cv_fs_result_hessian»
               [from_cv
                 (bounded_taylor64_rows_object_cv
                   (BoundedTaylor64 result_domain center_value
                     center_gradient value_bound gradient_bounds hessian)
                   rows)]]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_dim_taylor_model_result_make»
          [from_cv (bounded_bool_object_cv result_domain);
           from_cv
             (Pair (registered_case10173_fixed_q_interval_cv center_value)
               (registered_case10173_fixed_q_interval_list_cv
                 center_gradient));
           from_cv (registered_case10173_fixed_q_interval_cv value_bound);
           from_cv
             (registered_case10173_fixed_q_interval_list_cv gradient_bounds);
           from_cv (registered_case10173_fixed_q_interval_matrix_cv rows)])
        refs` by
       (irule
          compute_registeredCase10173TaylorCompletionEvalTheory.registered_case10173_compute_eval_app5_argument_results
        >> conj_tac >- intLib.ARITH_TAC
        >> conj_tac
        >- (irule registered_case10173_fs_result_domain_taylor_eval
            >> intLib.ARITH_TAC)
        >> conj_tac
        >- (irule registered_case10173_fs_result_center_first_to_q_eval
            >> intLib.ARITH_TAC)
        >> conj_tac
        >- (irule registered_case10173_fs_result_value_bound_to_q_eval
            >> intLib.ARITH_TAC)
        >> conj_tac
        >- (irule registered_case10173_fs_result_gradient_bounds_to_q_eval
            >> intLib.ARITH_TAC)
        >> irule registered_case10173_fs_result_hessian_to_q_eval
        >> intLib.ARITH_TAC)
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_dim_taylor_model_result_make»
            [from_cv (bounded_bool_object_cv result_domain);
             from_cv
               (Pair (registered_case10173_fixed_q_interval_cv center_value)
                 (registered_case10173_fixed_q_interval_list_cv
                   center_gradient));
             from_cv (registered_case10173_fixed_q_interval_cv value_bound);
             from_cv
               (registered_case10173_fixed_q_interval_list_cv
                 gradient_bounds);
             from_cv
               (registered_case10173_fixed_q_interval_matrix_cv rows)]) refs`
  >> conj_tac >- asm_rewrite_tac []
  >> PURE_ONCE_REWRITE_TAC
       [registered_case10173_fixed_q_taylor_object_cv_def]
  >> irule
       compute_registeredCase10173FixedResultConstructorsEvalTheory.registered_case10173_q_result_make_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
