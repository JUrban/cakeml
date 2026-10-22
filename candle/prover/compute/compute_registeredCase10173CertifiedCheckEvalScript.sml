(*****************************************************************************
 * Registered evaluator control seam for the final historical certified
 * numerical check.
 *
 * The production refinement must not obtain this verdict by replaying the
 * whole generic evaluator.  These theorems isolate the two reusable facts it
 * must instead supply: the historical program result and the final certified
 * finish result.
 *****************************************************************************)
Theory compute_registeredCase10173CertifiedCheckEval
Ancestors
  compute_registeredCase10173ProductionGuardValue
Libs
  bossLib preamble

Definition registered_case10173_hist_certified_check_body_def:
  registered_case10173_hist_certified_check_body =
    App «candle_cv_q_dim_taylor_model_certified_finish»
      [Var «boxes»;
       App «candle_cv_case10173_hist_program»
         [Var «center_program»;Var «box_program»;
          Var «boxes»;Var «roots»]]
End

Theorem registered_case10173_hist_certified_check_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_case10173_hist_certified_check» =
    SOME
      ([«center_program»;«box_program»;«boxes»;«roots»],
       registered_case10173_hist_certified_check_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_compute_eval_literal_app4:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME ([first_name;second_name;third_name;fourth_name],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv first_argument;from_cv second_argument;
         from_cv third_argument;from_cv fourth_argument])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(first_name,from_cv first_argument);
         (second_name,from_cv second_argument);
         (third_name,from_cv third_argument);
         (fourth_name,from_cv fourth_argument)] body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_hist_certified_check_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_certified_check»
        [from_cv center_program;from_cv box_program;
         from_cv boxes;from_cv roots]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«center_program»,from_cv center_program);
         («box_program»,from_cv box_program);
         («boxes»,from_cv boxes);(«roots»,from_cv roots)]
        registered_case10173_hist_certified_check_body) refs
Proof
  strip_tac
  >> irule registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_hist_certified_check_lookup]
QED

Theorem registered_case10173_hist_certified_check_eval_from_results:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program»
        [from_cv center_program;from_cv box_program;
         from_cv boxes;from_cv roots]) (refs:hol_refs) =
      (M_success (from_cv program_result),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_certified_finish»
        [from_cv boxes;from_cv program_result]) refs =
      (M_success (from_cv verdict),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_certified_check»
        [from_cv center_program;from_cv box_program;
         from_cv boxes;from_cv roots]) refs =
    (M_success (from_cv verdict),refs)
Proof
  strip_tac
  >> simp [registered_case10173_hist_certified_check_unfold]
  >> simp
       [registered_case10173_hist_certified_check_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_dim_taylor_model_certified_finish»
          [from_cv boxes;
           App «candle_cv_case10173_hist_program»
             [from_cv center_program;from_cv box_program;
              from_cv boxes;from_cv roots]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_dim_taylor_model_certified_finish»
          [from_cv boxes;from_cv program_result]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> fs []
QED

Theorem registered_case10173_hist_certified_check_fst_accept:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program»
        [from_cv center_program;from_cv box_program;
         from_cv boxes;from_cv roots]) (refs:hol_refs) =
      (M_success (from_cv program_result),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_certified_finish»
        [from_cv boxes;from_cv program_result]) refs =
      (M_success (from_cv (Pair (Num 1) detail)),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (Uop Fst
        (App «candle_cv_case10173_hist_certified_check»
          [from_cv center_program;from_cv box_program;
           from_cv boxes;from_cv roots])) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> mp_tac
       (Q.INST [`verdict` |-> `Pair (Num 1) detail`]
         registered_case10173_hist_certified_check_eval_from_results)
  >> impl_tac >- simp []
  >> strip_tac
  >> fs
       [compute_execTheory.from_cv_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
