(*****************************************************************************
 * Registered evaluator semantics for the small final Taylor acceptance
 * boundary.  The large historical program may supply an arbitrary result;
 * this layer extracts its domain and upper bound and performs only the box
 * validity and strict-negativity finish.
 *****************************************************************************)
Theory compute_registeredCase10173CertifiedFinishEval
Ancestors
  compute_registeredCase10173CertifiedCheckEval
Libs
  bossLib preamble

Definition registered_case10173_q_result_domain_body_def:
  registered_case10173_q_result_domain_body = Uop Fst (Var «result»)
End

Definition registered_case10173_q_result_value_bound_body_def:
  registered_case10173_q_result_value_bound_body =
    Uop Fst (Uop Snd (Uop Snd (Var «result»)))
End

Definition registered_case10173_q_certified_upper_body_def:
  registered_case10173_q_certified_upper_body =
    Uop Snd
      (App «candle_cv_q_dim_taylor_model_result_value_bound»
        [Var «result»])
End

Definition registered_case10173_q_certified_finish_body_def:
  registered_case10173_q_certified_finish_body =
    App «candle_cv_q_dim_whole_box_finish»
      [App «candle_cv_q_dim_taylor_model_result_domain» [Var «result»];
       App «candle_cv_q_box_valid_list» [Var «boxes»];
       App «candle_cv_q_dim_taylor_model_certified_upper» [Var «result»]]
End

Theorem registered_case10173_q_result_domain_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_dim_taylor_model_result_domain» =
    SOME ([«result»],registered_case10173_q_result_domain_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_result_value_bound_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_dim_taylor_model_result_value_bound» =
    SOME ([«result»],registered_case10173_q_result_value_bound_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_certified_upper_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_dim_taylor_model_certified_upper» =
    SOME ([«result»],registered_case10173_q_certified_upper_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_certified_finish_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_dim_taylor_model_certified_finish» =
    SOME
      ([«boxes»;«result»],
       registered_case10173_q_certified_finish_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_result_domain_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_result_domain»
        [from_cv result]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«result»,from_cv result)]
        registered_case10173_q_result_domain_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_q_result_domain_lookup]
QED

Theorem registered_case10173_q_result_domain_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_result_domain»
        [from_cv (Pair (result_domain:cv) (rest:cv))]) (refs:hol_refs) =
    (M_success (from_cv result_domain),refs)
Proof
  strip_tac
  >> simp
       [registered_case10173_q_result_domain_unfold,
        registered_case10173_q_result_domain_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_certified_upper_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_certified_upper»
        [from_cv
          (Pair (result_domain:cv)
            (Pair (center:cv)
              (Pair (Pair (lower:cv) (upper:cv)) (remaining:cv))))])
      (refs:hol_refs) =
    (M_success (from_cv upper),refs)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1,
        registered_case10173_q_certified_upper_lookup,
        registered_case10173_q_certified_upper_body_def,
        registered_case10173_q_result_value_bound_lookup,
        registered_case10173_q_result_value_bound_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_certified_finish_eval_from_results:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_result_domain»
        [from_cv result]) (refs:hol_refs) =
      (M_success (from_cv result_domain),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_box_valid_list» [from_cv boxes]) refs =
      (M_success (from_cv box_valid),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_certified_upper»
        [from_cv result]) refs =
      (M_success (from_cv upper),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_whole_box_finish»
          [from_cv result_domain;from_cv box_valid;from_cv upper]) refs =
      (M_success (from_cv verdict),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_certified_finish»
        [from_cv boxes;from_cv result]) refs =
    (M_success (from_cv verdict),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_dim_taylor_model_certified_finish»
          [from_cv boxes;from_cv result]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (subst [(«boxes»,from_cv boxes);(«result»,from_cv result)]
          registered_case10173_q_certified_finish_body) refs` by
       (irule
          compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
        >> simp [registered_case10173_q_certified_finish_lookup])
  >> pop_assum SUBST1_TAC
  >> simp
       [registered_case10173_q_certified_finish_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_dim_whole_box_finish»
          [App «candle_cv_q_dim_taylor_model_result_domain»
             [from_cv result];
           App «candle_cv_q_box_valid_list» [from_cv boxes];
           App «candle_cv_q_dim_taylor_model_certified_upper»
             [from_cv result]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_dim_whole_box_finish»
          [from_cv result_domain;from_cv box_valid;from_cv upper]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
        >> simp [])
  >> fs []
QED

val _ = export_theory ();
