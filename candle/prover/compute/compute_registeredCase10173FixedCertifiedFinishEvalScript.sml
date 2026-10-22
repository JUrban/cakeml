(*****************************************************************************
 * Certified-finish handoff for a packet-parametric fixed Taylor result.
 * Box validation remains an explicit premise at this layer; the source-box
 * relation discharges it in the authenticated job composition.
 *****************************************************************************)
Theory compute_registeredCase10173FixedCertifiedFinishEval
Ancestors
  compute_registeredCase10173FixedItemToQEval
  compute_registeredCase10173PositiveIntervalEval
Libs
  bossLib preamble intLib wordsLib

Definition registered_case10173_q_whole_box_finish_body_def:
  registered_case10173_q_whole_box_finish_body =
    Pair
      (If (Var «inputs_valid»)
        (If (Var «box_valid»)
          (If
            (App «candle_cv_q_le»
              [App «candle_cv_q_zero» [];Var «upper»])
            (Num 0) (Num 1))
          (Num 0))
        (Num 0))
      (Var «upper»)
End

Theorem registered_case10173_q_whole_box_finish_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_dim_whole_box_finish» =
    SOME
      ([«inputs_valid»;«box_valid»;«upper»],
       registered_case10173_q_whole_box_finish_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_result_domain_fixed_taylor_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_result_domain»
        [from_cv
          (registered_case10173_fixed_q_taylor_object_cv
            (BoundedTaylor64 result_domain center_value center_gradient
              value_bound gradient_bounds hessian) rows)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_bool_object_cv result_domain)),refs)
Proof
  strip_tac
  >> PURE_ONCE_REWRITE_TAC
       [compute_registeredCase10173FixedResultHandoffEvalTheory.registered_case10173_fixed_q_taylor_object_cv_def]
  >> irule
       compute_registeredCase10173CertifiedFinishEvalTheory.registered_case10173_q_result_domain_eval
  >> simp []
QED

Theorem registered_case10173_q_certified_upper_fixed_taylor_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_certified_upper»
        [from_cv
          (registered_case10173_fixed_q_taylor_object_cv
            (BoundedTaylor64 result_domain center_value center_gradient
              (BoundedInterval64 value_lower value_upper)
              gradient_bounds hessian) rows)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_fixed_q_endpoint_cv value_upper)),refs)
Proof
  strip_tac
  >> PURE_REWRITE_TAC
       [compute_registeredCase10173FixedResultHandoffEvalTheory.registered_case10173_fixed_q_taylor_object_cv_def,
        compute_registeredCase10173FixedResultToQEvalTheory.registered_case10173_fixed_q_interval_cv_def]
  >> irule
       compute_registeredCase10173CertifiedFinishEvalTheory.registered_case10173_q_certified_upper_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_q_whole_box_finish_negative_fixed_eval:
  bounded_signed64_strict_negative upper /\ 4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_whole_box_finish»
        [Num 1;Num 1;
         from_cv (registered_case10173_fixed_q_endpoint_cv upper)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (registered_case10173_fixed_q_endpoint_cv upper))),refs)
Proof
  Cases_on `upper`
  >> simp
       [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def]
  >> strip_tac
  >> Cases_on `clock`
  >- fs []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_whole_box_finish_lookup,
        registered_case10173_q_whole_box_finish_body_def,
        compute_registeredCase10173PositiveIntervalEvalTheory.registered_case10173_q_zero_lookup,
        compute_registeredCase10173PositiveIntervalEvalTheory.registered_case10173_q_zero_body_def,
        compute_registeredCase10173SqrtCertificateEvalTheory.registered_case10173_q_le_lookup,
        compute_registeredCase10173SqrtCertificateEvalTheory.registered_case10173_q_le_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_body_def,
        compute_registeredCase10173FixedResultToQEvalTheory.registered_case10173_fixed_q_endpoint_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        wordsTheory.w2n_eq_0]
QED

Theorem registered_case10173_q_certified_finish_fixed_taylor_eval:
  bounded_signed64_strict_negative value_upper /\
  6 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_box_valid_list» [from_cv boxes])
      (refs:hol_refs) = (M_success (Num 1),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_certified_finish»
        [from_cv boxes;
         from_cv
           (registered_case10173_fixed_q_taylor_object_cv
             (BoundedTaylor64 T center_value center_gradient
               (BoundedInterval64 value_lower value_upper)
               gradient_bounds hessian) rows)]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (registered_case10173_fixed_q_endpoint_cv value_upper))),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedFinishEvalTheory.registered_case10173_q_certified_finish_eval_from_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `Num 1`
  >> qexists_tac `bounded_bool_object_cv T`
  >> qexists_tac `registered_case10173_fixed_q_endpoint_cv value_upper`
  >> conj_tac
  >- (simp
        [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_q_whole_box_finish_negative_fixed_eval)
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule registered_case10173_q_certified_upper_fixed_taylor_eval
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule registered_case10173_q_result_domain_fixed_taylor_eval
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
  >> simp [compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
