(*****************************************************************************
 * Small registered historical constructors and constants shared by the
 * specialized center and box evaluators.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalBasicEval
Ancestors
  compute_registeredCase10173HistoricalListScaleRefinement
Libs
  bossLib preamble

Definition registered_case10173_fs_first_make_body_def:
  registered_case10173_fs_first_make_body =
    Pair (Var «value») (Var «gradient»)
End

Definition registered_case10173_q_pi_half_interval_body_def:
  registered_case10173_q_pi_half_interval_body =
    (Pair
      (Pair (Pair (Num 1686629713) (Num 0)) (Num 1073741823))
      (Pair (Pair (Num 6746518853) (Num 0)) (Num 4294967295)) :
      compute_exp)
End

Definition registered_case10173_q_pi_half_interval_cv_def:
  registered_case10173_q_pi_half_interval_cv =
    (Pair
      (Pair (Pair (Num 1686629713) (Num 0)) (Num 1073741823))
      (Pair (Pair (Num 6746518853) (Num 0)) (Num 4294967295)) : cv)
End

Theorem registered_case10173_fs_first_make_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_first_make» =
    SOME ([«value»;«gradient»],registered_case10173_fs_first_make_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_pi_half_interval_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_pi_half_interval» =
    SOME ([],registered_case10173_q_pi_half_interval_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_first_make_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_make»
        [from_cv value;from_cv gradient]) (refs:hol_refs) =
    (M_success (from_cv (Pair value gradient)),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_first_make_lookup,
        registered_case10173_fs_first_make_body_def,
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

Theorem registered_case10173_q_pi_half_interval_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_pi_half_interval» []) (refs:hol_refs) =
    (M_success (from_cv registered_case10173_q_pi_half_interval_cv),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_pi_half_interval_lookup,
        registered_case10173_q_pi_half_interval_body_def,
        registered_case10173_q_pi_half_interval_cv_def,
        compute_execTheory.from_cv_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_pi_half_interval_object:
  bounded_object_positive_q_interval64_decimal
      registered_case10173_q_pi_half_interval_cv =
    SOME bounded_historical_pi_half_decimal
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_pi_half_interval_eval:
  10 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_of_q»
        [App «candle_cv_q_pi_half_interval» []]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv bounded_historical_pi_half_decimal)),
      refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_of_q»
          [App «candle_cv_q_pi_half_interval» []]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_of_q»
          [from_cv registered_case10173_q_pi_half_interval_cv]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp [registered_case10173_q_pi_half_interval_eval])
  >> rw []
  >> irule
       compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_interval_of_q_object_eval
  >> simp [registered_case10173_q_pi_half_interval_object]
QED

val _ = export_theory ();
