(*****************************************************************************
 * Packet-parametric conversion of an ordinary fixed Taylor item to the
 * rational result consumed by the certified finish.
 *****************************************************************************)
Theory compute_registeredCase10173FixedItemToQEval
Ancestors
  compute_registeredCase10173FixedResultHandoffEval
  compute_registeredCase10173OrdinaryItemEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fsa_item_to_q_body_def:
  registered_case10173_fsa_item_to_q_body =
    If (App «candle_cv_fsa_item_is_fixed» [Var «item»])
      (App «candle_cv_fs_result_to_q»
        [App «candle_cv_fsa_item_payload» [Var «item»]])
      (App «candle_cv_fsa_item_payload» [Var «item»])
End

Theorem registered_case10173_fsa_item_to_q_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsa_item_to_q» =
    SOME ([«item»],registered_case10173_fsa_item_to_q_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsa_item_to_q_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_to_q» [from_cv item])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«item»,from_cv item)]
        registered_case10173_fsa_item_to_q_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fsa_item_to_q_lookup]
QED

Theorem registered_case10173_fsa_item_to_q_fixed_body_subst:
  subst
      [(«item»,
        from_cv
          (Pair (Num 1)
            (bounded_taylor64_rows_object_cv
              (BoundedTaylor64 result_domain center_value center_gradient
                value_bound gradient_bounds hessian) rows)))]
      registered_case10173_fsa_item_to_q_body =
    If
      (App «candle_cv_fsa_item_is_fixed»
        [from_cv
          (Pair (Num 1)
            (bounded_taylor64_rows_object_cv
              (BoundedTaylor64 result_domain center_value center_gradient
                value_bound gradient_bounds hessian) rows))])
      (App «candle_cv_fs_result_to_q»
        [App «candle_cv_fsa_item_payload»
          [from_cv
            (Pair (Num 1)
              (bounded_taylor64_rows_object_cv
                (BoundedTaylor64 result_domain center_value center_gradient
                  value_bound gradient_bounds hessian) rows))]])
      (App «candle_cv_fsa_item_payload»
        [from_cv
          (Pair (Num 1)
            (bounded_taylor64_rows_object_cv
              (BoundedTaylor64 result_domain center_value center_gradient
                value_bound gradient_bounds hessian) rows))])
Proof
  simp
    [registered_case10173_fsa_item_to_q_body_def,
     compute_evalTheory.subst_def]
QED

Theorem registered_case10173_fsa_item_to_q_fixed_taylor_eval:
  LENGTH center_gradient + 8 < clock /\
  LENGTH gradient_bounds + 7 < clock /\
  SUM (MAP LENGTH rows) + LENGTH rows + 7 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_to_q»
        [from_cv
          (Pair (Num 1)
            (bounded_taylor64_rows_object_cv
              (BoundedTaylor64 result_domain center_value center_gradient
                value_bound gradient_bounds hessian) rows))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_fixed_q_taylor_object_cv
          (BoundedTaylor64 result_domain center_value center_gradient
            value_bound gradient_bounds hessian) rows)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«item»,
              from_cv
                (Pair (Num 1)
                  (bounded_taylor64_rows_object_cv
                    (BoundedTaylor64 result_domain center_value
                      center_gradient value_bound gradient_bounds hessian)
                    rows)))]
            registered_case10173_fsa_item_to_q_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fsa_item_to_q_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [registered_case10173_fsa_item_to_q_fixed_body_subst]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_to_q»
            [App «candle_cv_fsa_item_payload»
              [from_cv
                (Pair (Num 1)
                  (bounded_taylor64_rows_object_cv
                    (BoundedTaylor64 result_domain center_value
                      center_gradient value_bound gradient_bounds hessian)
                    rows))]]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success
      >> qexists_tac `0`
      >> simp
           [compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_is_fixed_fixed_eval]
      >> intLib.ARITH_TAC)
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_to_q»
            [from_cv
              (bounded_taylor64_rows_object_cv
                (BoundedTaylor64 result_domain center_value center_gradient
                  value_bound gradient_bounds hessian) rows)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_payload_fixed_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173FixedResultHandoffEvalTheory.registered_case10173_fs_result_to_q_typed_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
