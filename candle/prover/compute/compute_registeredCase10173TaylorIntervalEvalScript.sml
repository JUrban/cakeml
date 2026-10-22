(*****************************************************************************
 * Registered evaluator refinement for interval absolute upper bounds.
 *
 * This is the final non-recursive boundary used by Taylor dot products: take
 * absolute values of both endpoints and retain their signed-pair maximum.
 *****************************************************************************)
Theory compute_registeredCase10173TaylorIntervalEval
Ancestors
  compute_registeredCase10173TaylorOrderEval
Libs
  bossLib preamble

Definition registered_case10173_fs_interval_abs_upper_body_def:
  registered_case10173_fs_interval_abs_upper_body =
    App «candle_cv_fs_raw_max»
      [App «candle_cv_fs_raw_abs» [Uop Fst (Var «i»)];
       App «candle_cv_fs_raw_abs» [Uop Snd (Var «i»)]]
End

Theorem registered_case10173_fs_interval_abs_upper_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_abs_upper» =
    SOME ([«i»],registered_case10173_fs_interval_abs_upper_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_abs_upper_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_abs_upper» [from_cv interval])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«i»,from_cv interval)]
        registered_case10173_fs_interval_abs_upper_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_interval_abs_upper_lookup]
QED

Theorem registered_case10173_fs_interval_abs_upper_eval:
  bounded_object_fs_interval_abs_upper interval = SOME result /\
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_abs_upper» [from_cv interval])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `interval`
  >> fs
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_interval_abs_upper_def]
  >> Cases_on `bounded_object_fs_raw_abs c`
  >> fs
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_interval_abs_upper_def]
  >> Cases_on `bounded_object_fs_raw_abs c0`
  >> fs
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_interval_abs_upper_def]
  >> Cases_on `bounded_object_fs_raw_max x x'`
  >> fs
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_interval_abs_upper_def]
  >> strip_tac
  >> gvs []
  >> simp
       [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`interval` |-> `(Pair c c0:cv)`]
            registered_case10173_fs_interval_abs_upper_unfold))]
  >> simp
       [registered_case10173_fs_interval_abs_upper_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_abs»
          [Uop Fst (Pair (from_cv c) (from_cv c0))]) refs =
      (M_success (from_cv x),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_abs»
             [Uop Fst (Pair (from_cv c) (from_cv c0))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_abs» [from_cv c]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
        >> fs [registered_case10173_fs_raw_abs_eval])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_abs»
          [Uop Snd (Pair (from_cv c) (from_cv c0))]) refs =
      (M_success (from_cv x'),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_abs»
             [Uop Snd (Pair (from_cv c) (from_cv c0))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_abs» [from_cv c0]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
        >> fs [registered_case10173_fs_raw_abs_eval])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_max»
          [App «candle_cv_fs_raw_abs»
             [Uop Fst (Pair (from_cv c) (from_cv c0))];
           App «candle_cv_fs_raw_abs»
             [Uop Snd (Pair (from_cv c) (from_cv c0))]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_max» [from_cv x;from_cv x']) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> fs []
        >> intLib.ARITH_TAC)
  >> fs [registered_case10173_fs_raw_max_eval]
QED

Theorem registered_case10173_fs_interval_abs_upper_object_cv_eval:
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_abs_upper»
        [from_cv (bounded_interval64_object_cv interval)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_word64_object_cv
          (bounded_interval64_abs_upper interval))),refs)
Proof
  strip_tac
  >> irule registered_case10173_fs_interval_abs_upper_eval
  >> simp
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_interval_abs_upper_exact]
QED

val _ = export_theory ();
