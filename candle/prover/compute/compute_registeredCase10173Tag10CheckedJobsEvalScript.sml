Theory compute_registeredCase10173Tag10CheckedJobsEval
Ancestors
  compute_registeredCase10173RawWrapperEval
  compute_registeredCase10173HistoricalChunk16Tag10Data
Libs
  bossLib preamble

Definition registered_case10173_tag10_hist_checked_jobs_check_body_def:
  registered_case10173_tag10_hist_checked_jobs_check_body =
    If (Uop Ispair (Var «jobs»))
      (If (Uop Ispair (Var «roots»))
        (If
          (App «candle_cv_case10173_hist_root_record_check»
            [Uop Snd (Uop Snd (Uop Fst (Var «jobs»)));
             Uop Fst (Var «roots»)])
          (If
            (App «candle_cv_case10173_hist_production_guard»
              [Uop Snd (Uop Snd (Uop Fst (Var «jobs»)));
               Uop Fst (Var «roots»)])
            (If
              (App «candle_cv_analytic_program_sqrt_data_exact»
                [Uop Fst (Uop Fst (Var «jobs»));
                 Var «source_program»])
              (Let «box_patched»
                (App «candle_cv_analytic_program_patch_sqrt»
                  [Uop Fst (Uop Fst (Var «jobs»));
                   Var «source_program»])
                (If
                  (App «candle_cv_analytic_program_sqrt_data_exact»
                    [Uop Fst (Uop Snd (Uop Fst (Var «jobs»)));
                     Var «source_program»])
                  (Let «center_patched»
                    (App «candle_cv_analytic_program_patch_sqrt»
                      [Uop Fst (Uop Snd (Uop Fst (Var «jobs»)));
                       Var «source_program»])
                    (If
                      (Uop Fst
                        (App «candle_cv_case10173_hist_certified_check»
                          [Uop Snd (Var «center_patched»);
                           Uop Snd (Var «box_patched»);
                           Uop Snd (Uop Snd (Uop Fst (Var «jobs»)));
                           Uop Fst (Var «roots»)]))
                      (App «candle_cv_case10173_hist_checked_jobs_check»
                        [Var «source_program»;
                         Uop Snd (Var «jobs»);
                         Uop Snd (Var «roots»)])
                      (Num 0)))
                  (Num 0)))
              (Num 0))
            (Num 0))
          (Num 0))
        (Num 0))
      (If (Uop Ispair (Var «roots»)) (Num 0) (Num 1))
End

Theorem registered_case10173_tag10_hist_checked_jobs_check_lookup:
  ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs
      «candle_cv_case10173_hist_checked_jobs_check» =
    SOME
      ([«source_program»;«jobs»;«roots»],
       registered_case10173_tag10_hist_checked_jobs_check_body)
Proof
  EVAL_TAC
QED

Definition registered_case10173_tag10_hist_checked_job_head_eval_ok_def:
  registered_case10173_tag10_hist_checked_job_head_eval_ok clock source_program
      box_sqrt_data center_sqrt_data boxes root_record
      box_remainder box_program center_remainder center_program
      (refs:hol_refs) <=>
    compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_root_record_check»
        [from_cv boxes;from_cv root_record]) refs =
      (M_success (Num 1),refs) /\
    compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_production_guard»
        [from_cv boxes;from_cv root_record]) refs =
      (M_success (Num 1),refs) /\
    compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_analytic_program_sqrt_data_exact»
        [from_cv box_sqrt_data;from_cv source_program]) refs =
      (M_success (Num 1),refs) /\
    compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_analytic_program_patch_sqrt»
        [from_cv box_sqrt_data;from_cv source_program]) refs =
      (M_success
        (from_cv (Pair box_remainder box_program)),refs) /\
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_analytic_program_sqrt_data_exact»
        [from_cv center_sqrt_data;from_cv source_program]) refs =
      (M_success (Num 1),refs) /\
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_analytic_program_patch_sqrt»
        [from_cv center_sqrt_data;from_cv source_program]) refs =
      (M_success
        (from_cv (Pair center_remainder center_program)),refs) /\
    compute_eval (clock - 2)
      registered_case10173_historical_chunk16_tag10_ceqs
      (Uop Fst
        (App «candle_cv_case10173_hist_certified_check»
          [from_cv center_program;from_cv box_program;
           from_cv boxes;from_cv root_record])) refs =
      (M_success (Num 1),refs)
End

Theorem registered_case10173_tag10_hist_checked_jobs_check_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_checked_jobs_check»
        [from_cv source_program;from_cv jobs;from_cv roots])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (subst
        [(«source_program»,from_cv source_program);
         («jobs»,from_cv jobs);
         («roots»,from_cv roots)]
        registered_case10173_tag10_hist_checked_jobs_check_body) refs
Proof
  Cases_on `clock`
  >- simp []
  >> strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_tag10_hist_checked_jobs_check_lookup,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_hist_checked_jobs_check_nil_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_checked_jobs_check»
        [from_cv source_program;from_cv (Num jobs_nil);
         from_cv (Num roots_nil)])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp [registered_case10173_tag10_hist_checked_jobs_check_unfold]
  >> simp
       [registered_case10173_tag10_hist_checked_jobs_check_body_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_if_success:
  compute_eval clock ceqs condition (refs:hol_refs) =
      (M_success (Num (SUC n)),refs) ==>
  compute_eval clock ceqs
      (If condition yes_branch no_branch) refs =
    compute_eval clock ceqs yes_branch refs
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_let_success:
  0 < clock /\
  compute_eval clock ceqs binding (refs:hol_refs) =
      (M_success value,refs) ==>
  compute_eval clock ceqs (Let name binding body) refs =
    compute_eval (clock - 1) ceqs
      (subst [(name,value)] body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_let_success_result:
  0 < clock /\
  compute_eval clock ceqs binding (refs:hol_refs) =
      (M_success value,refs) /\
  compute_eval (clock - 1) ceqs
      (subst [(name,value)] body) refs = result ==>
  compute_eval clock ceqs (Let name binding body) refs = result
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_app2_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) ==>
  compute_eval clock ceqs
      (App function_name [argument1;argument2]) refs =
    compute_eval clock ceqs
      (App function_name [from_cv result1;from_cv result2]) refs
Proof
  Cases_on `clock`
  >> simp []
  >> strip_tac
  >> Cases_on `ALOOKUP ceqs function_name`
  >- simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `x`
  >> Cases_on `LENGTH q = 2`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_app3_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) /\
  compute_eval clock ceqs argument3 refs =
      (M_success (from_cv result3),refs) ==>
  compute_eval clock ceqs
      (App function_name [argument1;argument2;argument3]) refs =
    compute_eval clock ceqs
      (App function_name
        [from_cv result1;from_cv result2;from_cv result3]) refs
Proof
  Cases_on `clock`
  >> simp []
  >> strip_tac
  >> Cases_on `ALOOKUP ceqs function_name`
  >- simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `x`
  >> Cases_on `LENGTH q = 3`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_app4_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) /\
  compute_eval clock ceqs argument3 refs =
      (M_success (from_cv result3),refs) /\
  compute_eval clock ceqs argument4 refs =
      (M_success (from_cv result4),refs) ==>
  compute_eval clock ceqs
      (App function_name [argument1;argument2;argument3;argument4]) refs =
    compute_eval clock ceqs
      (App function_name
        [from_cv result1;from_cv result2;from_cv result3;
         from_cv result4]) refs
Proof
  Cases_on `clock`
  >> simp []
  >> strip_tac
  >> Cases_on `ALOOKUP ceqs function_name`
  >- simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `x`
  >> Cases_on `LENGTH q = 4`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_uop_argument_cong:
  compute_eval clock ceqs argument (refs:hol_refs) =
      compute_eval clock ceqs normalized refs ==>
  compute_eval clock ceqs (Uop operator argument) refs =
    compute_eval clock ceqs (Uop operator normalized) refs
Proof
  strip_tac
  >> simp_tac std_ss
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def]
  >> fs []
QED

Theorem registered_case10173_tag10_hist_checked_jobs_check_cons_eval:
  3 < clock /\
  registered_case10173_tag10_hist_checked_job_head_eval_ok (clock - 1)
    source_program box_sqrt_data center_sqrt_data boxes root_record
    box_remainder box_program center_remainder center_program refs /\
  compute_eval (clock - 3)
      registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_checked_jobs_check»
        [from_cv source_program;from_cv jobs;from_cv roots]) refs =
    (M_success (Num 1),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_checked_jobs_check»
        [from_cv source_program;
         from_cv
           (Pair
             (Pair box_sqrt_data (Pair center_sqrt_data boxes)) jobs);
         from_cv (Pair root_record roots)]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp [registered_case10173_tag10_hist_checked_jobs_check_unfold]
  >> simp
       [registered_case10173_tag10_hist_checked_jobs_check_body_def,
        compute_evalTheory.subst_def]
  >> fs [registered_case10173_tag10_hist_checked_job_head_eval_ok_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (Uop Ispair
          (Pair
            (Pair (from_cv box_sqrt_data)
              (Pair (from_cv center_sqrt_data) (from_cv boxes)))
            (from_cv jobs))) refs =
      (M_success (Num 1),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_ispair_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> simp [compute_eval_if_success]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (Uop Ispair
          (Pair (from_cv root_record) (from_cv roots))) refs =
      (M_success (Num 1),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_ispair_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> simp [compute_eval_if_success]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_root_record_check»
          [Uop Snd
            (Uop Snd
              (Uop Fst
                (Pair
                  (Pair (from_cv box_sqrt_data)
                    (Pair (from_cv center_sqrt_data) (from_cv boxes)))
                  (from_cv jobs))));
           Uop Fst (Pair (from_cv root_record) (from_cv roots))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_root_record_check»
          [from_cv boxes;from_cv root_record]) refs` by
       (irule compute_eval_app2_argument_results
        >> fs
             [compute_evalTheory.compute_eval_def,
              compute_execProofTheory.compute_eval_from_cv,
              compute_evalTheory.do_uop_def,
              compute_evalTheory.do_fst_def,
              compute_evalTheory.do_snd_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def])
  >> simp [compute_eval_if_success]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_production_guard»
          [Uop Snd
            (Uop Snd
              (Uop Fst
                (Pair
                  (Pair (from_cv box_sqrt_data)
                    (Pair (from_cv center_sqrt_data) (from_cv boxes)))
                  (from_cv jobs))));
           Uop Fst (Pair (from_cv root_record) (from_cv roots))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_production_guard»
          [from_cv boxes;from_cv root_record]) refs` by
       (irule compute_eval_app2_argument_results
        >> fs
             [compute_evalTheory.compute_eval_def,
              compute_execProofTheory.compute_eval_from_cv,
              compute_evalTheory.do_uop_def,
              compute_evalTheory.do_fst_def,
              compute_evalTheory.do_snd_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def])
  >> simp [compute_eval_if_success]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_analytic_program_sqrt_data_exact»
          [Uop Fst
            (Uop Fst
              (Pair
                (Pair (from_cv box_sqrt_data)
                  (Pair (from_cv center_sqrt_data) (from_cv boxes)))
                (from_cv jobs)));
           from_cv source_program]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_analytic_program_sqrt_data_exact»
          [from_cv box_sqrt_data;from_cv source_program]) refs` by
       (irule compute_eval_app2_argument_results
        >> fs
             [compute_evalTheory.compute_eval_def,
              compute_execProofTheory.compute_eval_from_cv,
              compute_evalTheory.do_uop_def,
              compute_evalTheory.do_fst_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def])
  >> simp [compute_eval_if_success]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_analytic_program_patch_sqrt»
          [Uop Fst
            (Uop Fst
              (Pair
                (Pair (from_cv box_sqrt_data)
                  (Pair (from_cv center_sqrt_data) (from_cv boxes)))
                (from_cv jobs)));
           from_cv source_program]) refs =
      (M_success (from_cv (Pair box_remainder box_program)),refs)` by
       (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_tag10_ceqs
          (App «candle_cv_analytic_program_patch_sqrt»
            [Uop Fst
              (Uop Fst
                (Pair
                  (Pair (from_cv box_sqrt_data)
                    (Pair (from_cv center_sqrt_data) (from_cv boxes)))
                  (from_cv jobs)));
             from_cv source_program]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_tag10_ceqs
          (App «candle_cv_analytic_program_patch_sqrt»
            [from_cv box_sqrt_data;from_cv source_program]) refs` by
          (irule compute_eval_app2_argument_results
           >> fs
                [compute_evalTheory.compute_eval_def,
                 compute_execProofTheory.compute_eval_from_cv,
                 compute_evalTheory.do_uop_def,
                 compute_evalTheory.do_fst_def,
                 ml_monadBaseTheory.st_ex_bind_def,
                 ml_monadBaseTheory.st_ex_return_def])
        >> fs [])
  >> irule compute_eval_let_success_result
  >> conj_tac >- fs []
  >> qexists_tac `from_cv (Pair box_remainder box_program)`
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> `compute_eval (clock - 2)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_analytic_program_sqrt_data_exact»
          [Uop Fst
            (Uop Snd
              (Uop Fst
                (Pair
                  (Pair (from_cv box_sqrt_data)
                    (Pair (from_cv center_sqrt_data) (from_cv boxes)))
                  (from_cv jobs))));
           from_cv source_program]) refs =
      compute_eval (clock - 2)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_analytic_program_sqrt_data_exact»
          [from_cv center_sqrt_data;from_cv source_program]) refs` by
       (irule compute_eval_app2_argument_results
        >> fs
             [compute_evalTheory.compute_eval_def,
              compute_execProofTheory.compute_eval_from_cv,
              compute_evalTheory.do_uop_def,
              compute_evalTheory.do_fst_def,
              compute_evalTheory.do_snd_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def])
  >> simp [compute_eval_if_success]
  >> `compute_eval (clock - 2)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_analytic_program_patch_sqrt»
          [Uop Fst
            (Uop Snd
              (Uop Fst
                (Pair
                  (Pair (from_cv box_sqrt_data)
                    (Pair (from_cv center_sqrt_data) (from_cv boxes)))
                  (from_cv jobs))));
           from_cv source_program]) refs =
      (M_success
        (from_cv (Pair center_remainder center_program)),refs)` by
       (`compute_eval (clock - 2)
          registered_case10173_historical_chunk16_tag10_ceqs
          (App «candle_cv_analytic_program_patch_sqrt»
            [Uop Fst
              (Uop Snd
                (Uop Fst
                  (Pair
                    (Pair (from_cv box_sqrt_data)
                      (Pair (from_cv center_sqrt_data) (from_cv boxes)))
                    (from_cv jobs))));
             from_cv source_program]) refs =
        compute_eval (clock - 2)
          registered_case10173_historical_chunk16_tag10_ceqs
          (App «candle_cv_analytic_program_patch_sqrt»
            [from_cv center_sqrt_data;from_cv source_program]) refs` by
          (irule compute_eval_app2_argument_results
           >> fs
                [compute_evalTheory.compute_eval_def,
                 compute_execProofTheory.compute_eval_from_cv,
                 compute_evalTheory.do_uop_def,
                 compute_evalTheory.do_fst_def,
                 compute_evalTheory.do_snd_def,
                 ml_monadBaseTheory.st_ex_bind_def,
                 ml_monadBaseTheory.st_ex_return_def])
        >> fs [])
  >> irule compute_eval_let_success_result
  >> conj_tac >- fs []
  >> qexists_tac `from_cv (Pair center_remainder center_program)`
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> `compute_eval (clock - 3)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_certified_check»
          [Uop Snd
            (Pair (from_cv center_remainder) (from_cv center_program));
           Uop Snd
            (Pair (from_cv box_remainder) (from_cv box_program));
           Uop Snd
            (Uop Snd
              (Uop Fst
                (Pair
                  (Pair (from_cv box_sqrt_data)
                    (Pair (from_cv center_sqrt_data) (from_cv boxes)))
                  (from_cv jobs))));
           Uop Fst (Pair (from_cv root_record) (from_cv roots))]) refs =
      compute_eval (clock - 3)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_certified_check»
          [from_cv center_program;from_cv box_program;
           from_cv boxes;from_cv root_record]) refs` by
       (irule compute_eval_app4_argument_results
        >> fs
             [compute_evalTheory.compute_eval_def,
              compute_execProofTheory.compute_eval_from_cv,
              compute_evalTheory.do_uop_def,
              compute_evalTheory.do_fst_def,
              compute_evalTheory.do_snd_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def])
  >> `compute_eval (clock - 3)
        registered_case10173_historical_chunk16_tag10_ceqs
        (Uop Fst
          (App «candle_cv_case10173_hist_certified_check»
            [Uop Snd
              (Pair (from_cv center_remainder)
                (from_cv center_program));
             Uop Snd
              (Pair (from_cv box_remainder) (from_cv box_program));
             Uop Snd
              (Uop Snd
                (Uop Fst
                  (Pair
                    (Pair (from_cv box_sqrt_data)
                      (Pair (from_cv center_sqrt_data) (from_cv boxes)))
                    (from_cv jobs))));
             Uop Fst (Pair (from_cv root_record) (from_cv roots))])) refs =
      compute_eval (clock - 3)
        registered_case10173_historical_chunk16_tag10_ceqs
        (Uop Fst
          (App «candle_cv_case10173_hist_certified_check»
            [from_cv center_program;from_cv box_program;
             from_cv boxes;from_cv root_record])) refs` by
       (irule compute_eval_uop_argument_cong >> fs [])
  >> `compute_eval (clock - 3)
        registered_case10173_historical_chunk16_tag10_ceqs
        (Uop Fst
          (App «candle_cv_case10173_hist_certified_check»
            [Uop Snd
              (Pair (from_cv center_remainder)
                (from_cv center_program));
             Uop Snd
              (Pair (from_cv box_remainder) (from_cv box_program));
             Uop Snd
              (Uop Snd
                (Uop Fst
                  (Pair
                    (Pair (from_cv box_sqrt_data)
                      (Pair (from_cv center_sqrt_data) (from_cv boxes)))
                    (from_cv jobs))));
             Uop Fst (Pair (from_cv root_record) (from_cv roots))])) refs =
      (M_success (Num 1),refs)` by fs []
  >> simp [compute_eval_if_success]
  >> `compute_eval (clock - 3)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_checked_jobs_check»
          [from_cv source_program;
           Uop Snd
            (Pair
              (Pair (from_cv box_sqrt_data)
                (Pair (from_cv center_sqrt_data) (from_cv boxes)))
              (from_cv jobs));
           Uop Snd (Pair (from_cv root_record) (from_cv roots))]) refs =
      compute_eval (clock - 3)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_checked_jobs_check»
          [from_cv source_program;from_cv jobs;from_cv roots]) refs` by
       (irule compute_eval_app3_argument_results
        >> fs
             [compute_evalTheory.compute_eval_def,
              compute_execProofTheory.compute_eval_from_cv,
              compute_evalTheory.do_uop_def,
              compute_evalTheory.do_snd_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def])
  >> fs []
QED

val _ = export_theory ();
