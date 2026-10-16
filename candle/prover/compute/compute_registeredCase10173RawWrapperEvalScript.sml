(*****************************************************************************
 * Registered-evaluator semantics for the historical raw-jobs wrapper.
 *
 * Authentication fixes the rational canonicality conjunct.  This theory
 * proves that the exact registered wrapper consequently has the same result
 * as its checked-jobs call, leaving only that numerical recursion as the
 * fast-evaluator refinement obligation.
 *****************************************************************************)
Theory compute_registeredCase10173RawWrapperEval
Ancestors
  compute_registeredCase10173CanonicalListEval
Libs
  bossLib preamble

Definition registered_case10173_bool_and_body_def:
  registered_case10173_bool_and_body =
    If (Var «a») (Var «b») (Num 0)
End

Definition registered_case10173_hist_checked_raw_jobs_check_body_def:
  registered_case10173_hist_checked_raw_jobs_check_body =
    App «candle_cv_bool_and»
      [Binop Eq
        (App «candle_cv_fso_variable_jobs_canonical»
          [Var «encoded_jobs»])
        (Var «encoded_jobs»);
       App «candle_cv_case10173_hist_checked_jobs_check»
        [Var «source_program»;Var «encoded_jobs»;Var «roots»]]
End

Theorem registered_case10173_bool_and_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_bool_and» =
    SOME ([«a»;«b»],registered_case10173_bool_and_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_checked_raw_jobs_check_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_case10173_hist_checked_raw_jobs_check» =
    SOME
      ([«source_program»;«encoded_jobs»;«roots»],
       registered_case10173_hist_checked_raw_jobs_check_body)
Proof
  EVAL_TAC
QED

Theorem compute_eval_binop_eq_same_result:
  compute_eval clock ceqs left (refs:hol_refs) =
      (M_success value,refs) /\
  compute_eval clock ceqs right refs = (M_success value,refs) ==>
  compute_eval clock ceqs (Binop Eq left right) refs =
    (M_success (Num 1),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_bool_and_true_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      first_expression (refs:hol_refs) = (M_success (Num 1),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      second_expression refs =
        (M_success (from_cv second_result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_bool_and»
        [first_expression;second_expression]) refs =
    (M_success (from_cv second_result),refs)
Proof
  Cases_on `clock`
  >- simp []
  >> strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_bool_and_lookup,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.subst_def,
        registered_case10173_bool_and_body_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_bool_and_true_one_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      first_expression (refs:hol_refs) = (M_success (Num 1),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      second_expression refs = (M_success (Num 1),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_bool_and»
        [first_expression;second_expression]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`second_result` |-> `Num 1`]
         registered_case10173_bool_and_true_eval)
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_hist_checked_raw_jobs_check_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_checked_raw_jobs_check»
        [from_cv source_program;from_cv encoded_jobs;from_cv roots])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«source_program»,from_cv source_program);
         («encoded_jobs»,from_cv encoded_jobs);
         («roots»,from_cv roots)]
        registered_case10173_hist_checked_raw_jobs_check_body) refs
Proof
  Cases_on `clock`
  >- simp []
  >> strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_hist_checked_raw_jobs_check_lookup,
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

Theorem registered_case10173_hist_checked_raw_jobs_check_authenticated:
  bounded_packed_chars_case10173_decimal_authenticated_full_check bytes
      encoded_jobs roots /\
  cv_size encoded_jobs + 7 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_checked_jobs_check»
        [from_cv source_program;from_cv encoded_jobs;from_cv roots])
      (refs:hol_refs) = (M_success (Num 1),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_checked_raw_jobs_check»
        [from_cv source_program;from_cv encoded_jobs;from_cv roots]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp [registered_case10173_hist_checked_raw_jobs_check_unfold]
  >> simp
       [registered_case10173_hist_checked_raw_jobs_check_body_def,
        compute_evalTheory.subst_def]
  >> irule registered_case10173_bool_and_true_one_eval
  >> simp []
  >> irule compute_eval_binop_eq_same_result
  >> simp [compute_execProofTheory.compute_eval_from_cv]
  >> irule registered_case10173_fso_variable_jobs_canonical_eval_authenticated
  >> simp []
  >> metis_tac []
QED

val _ = export_theory ();
