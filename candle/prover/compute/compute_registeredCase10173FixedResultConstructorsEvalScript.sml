(*****************************************************************************
 * Registered constructors used by fixed-result to rational conversion.
 * Kept above the result composition proof so edits to that proof do not
 * rebuild the recursive list and matrix refinements.
 *****************************************************************************)
Theory compute_registeredCase10173FixedResultConstructorsEval
Ancestors
  compute_registeredCase10173FixedResultToQEval
Libs
  bossLib preamble

Definition registered_case10173_q_first_jet_make_body_def:
  registered_case10173_q_first_jet_make_body =
    Pair (Var «f») (Var «gradient»)
End

Definition registered_case10173_q_result_make_body_def:
  registered_case10173_q_result_make_body =
    Pair (Var «domain»)
      (Pair (Var «center_first»)
        (Pair (Var «value_bound»)
          (Pair (Var «gradient_bounds») (Var «hessian»))))
End

Theorem registered_case10173_q_first_jet_make_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_dim_first_jet_make» =
    SOME
      ([«f»;«gradient»],registered_case10173_q_first_jet_make_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_result_make_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_dim_taylor_model_result_make» =
    SOME
      ([«domain»;«center_first»;«value_bound»;
        «gradient_bounds»;«hessian»],
       registered_case10173_q_result_make_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_first_jet_make_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_first_jet_make»
        [from_cv f;from_cv gradient]) (refs:hol_refs) =
    (M_success (from_cv (Pair f gradient)),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_first_jet_make_lookup,
        registered_case10173_q_first_jet_make_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_result_make_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_result_make»
        [from_cv result_domain;from_cv center_first;from_cv value_bound;
         from_cv gradient_bounds;from_cv hessian]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair result_domain
          (Pair center_first
            (Pair value_bound (Pair gradient_bounds hessian))))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_result_make_lookup,
        registered_case10173_q_result_make_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
