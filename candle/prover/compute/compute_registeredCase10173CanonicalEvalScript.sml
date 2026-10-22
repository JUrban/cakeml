(*****************************************************************************
 * Symbolic evaluator semantics for the historical raw-job canonicalizer.
 *
 * These lemmas connect the actual registered equation bundle, rather than a
 * copied functional model, to the logical canonicalizer already implied by
 * the authenticated strengthened-decimal stream.
 *****************************************************************************)
Theory compute_registeredCase10173CanonicalEval
Ancestors
  compute_registeredCase10173HistoricalChunk16Data
  compute_boundedCase10173ObjectJobCanonical
  compute_execProof
Libs
  bossLib preamble

Definition registered_case10173_lc_num_canonical_body_def:
  registered_case10173_lc_num_canonical_body =
    If (Uop Ispair (Var «encoded»)) (Num 0) (Var «encoded»)
End

Definition registered_case10173_lc_z_canonical_body_def:
  registered_case10173_lc_z_canonical_body =
    If (Uop Ispair (Var «encoded»))
      (Pair
        (App «candle_cv_lc_num_canonical»
          [Uop Fst (Var «encoded»)])
        (App «candle_cv_lc_num_canonical»
          [Uop Snd (Var «encoded»)]))
      (Pair (Num 0) (Num 0))
End

Definition registered_case10173_q_canonical_body_def:
  registered_case10173_q_canonical_body =
    If (Uop Ispair (Var «encoded»))
      (Pair
        (App «candle_cv_lc_z_canonical»
          [Uop Fst (Var «encoded»)])
        (App «candle_cv_lc_num_canonical»
          [Uop Snd (Var «encoded»)]))
      (Pair (Pair (Num 0) (Num 0)) (Num 0))
End

Definition registered_case10173_q_interval_canonical_body_def:
  registered_case10173_q_interval_canonical_body =
    If (Uop Ispair (Var «encoded»))
      (Pair
        (App «candle_cv_q_canonical»
          [Uop Fst (Var «encoded»)])
        (App «candle_cv_q_canonical»
          [Uop Snd (Var «encoded»)]))
      (Pair (Pair (Pair (Num 0) (Num 0)) (Num 0))
        (Pair (Pair (Num 0) (Num 0)) (Num 0)))
End

Definition registered_case10173_q_interval_list_canonical_body_def:
  registered_case10173_q_interval_list_canonical_body =
    If (Uop Ispair (Var «encoded»))
      (Pair
        (App «candle_cv_q_interval_canonical»
          [Uop Fst (Var «encoded»)])
        (App «candle_cv_q_interval_list_canonical»
          [Uop Snd (Var «encoded»)]))
      (Num 0)
End

Definition registered_case10173_fso_variable_job_canonical_body_def:
  registered_case10173_fso_variable_job_canonical_body =
    Pair
      (App «candle_cv_q_interval_list_canonical»
        [Uop Fst (Var «encoded»)])
      (Pair
        (App «candle_cv_q_interval_list_canonical»
          [Uop Fst (Uop Snd (Var «encoded»))])
        (App «candle_cv_q_interval_list_canonical»
          [Uop Snd (Uop Snd (Var «encoded»))]))
End

Definition registered_case10173_fso_variable_jobs_canonical_body_def:
  registered_case10173_fso_variable_jobs_canonical_body =
    If (Uop Ispair (Var «encoded»))
      (Pair
        (App «candle_cv_fso_variable_job_canonical»
          [Uop Fst (Var «encoded»)])
        (App «candle_cv_fso_variable_jobs_canonical»
          [Uop Snd (Var «encoded»)]))
      (Num 0)
End

Theorem registered_case10173_lc_num_canonical_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_lc_num_canonical» =
    SOME ([«encoded»],registered_case10173_lc_num_canonical_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_lc_z_canonical_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_lc_z_canonical» =
    SOME ([«encoded»],registered_case10173_lc_z_canonical_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_canonical_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_canonical» =
    SOME ([«encoded»],registered_case10173_q_canonical_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_interval_canonical_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_interval_canonical» =
    SOME ([«encoded»],registered_case10173_q_interval_canonical_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_interval_list_canonical_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_interval_list_canonical» =
    SOME ([«encoded»],registered_case10173_q_interval_list_canonical_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fso_variable_job_canonical_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fso_variable_job_canonical» =
    SOME ([«encoded»],registered_case10173_fso_variable_job_canonical_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fso_variable_jobs_canonical_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fso_variable_jobs_canonical» =
    SOME ([«encoded»],registered_case10173_fso_variable_jobs_canonical_body)
Proof
  EVAL_TAC
QED

Theorem compute_eval_literal_app1:
  0 < clock /\
  ALOOKUP ceqs function_name = SOME ([argument_name],body) ==>
  compute_eval clock ceqs
      (App function_name [from_cv argument]) (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst [(argument_name,from_cv argument)] body) refs
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
QED

Theorem compute_eval_if_ispair_from_cv:
  compute_eval clock ceqs
      (If (Uop Ispair (from_cv argument)) pair_branch number_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs
      (case argument of
       | Pair _ _ => pair_branch
       | Num _ => number_branch) refs
Proof
  Cases_on `argument`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_pair_from_results:
  compute_eval clock ceqs left (refs:hol_refs) =
      (M_success (from_cv left_result),refs) /\
  compute_eval clock ceqs right refs =
      (M_success (from_cv right_result),refs) ==>
  compute_eval clock ceqs (Pair left right) refs =
    (M_success (from_cv (Pair left_result right_result)),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_app1_argument_result:
  0 < clock /\
  compute_eval clock ceqs argument (refs:hol_refs) =
      (M_success (from_cv argument_result),refs) ==>
  compute_eval clock ceqs (App function_name [argument]) refs =
    compute_eval clock ceqs
      (App function_name [from_cv argument_result]) refs
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
  >> Cases_on `LENGTH q = 1`
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

Theorem compute_eval_uop_fst_from_cv_pair:
  compute_eval clock ceqs
      (Uop Fst (from_cv (Pair left right))) (refs:hol_refs) =
    (M_success (from_cv left),refs)
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_fst_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_uop_snd_from_cv_pair:
  compute_eval clock ceqs
      (Uop Snd (from_cv (Pair left right))) (refs:hol_refs) =
    (M_success (from_cv right),refs)
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_uop_fst_from_cv_components:
  compute_eval clock ceqs
      (Uop Fst (Pair (from_cv left) (from_cv right)))
      (refs:hol_refs) =
    (M_success (from_cv left),refs)
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_fst_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_uop_snd_from_cv_components:
  compute_eval clock ceqs
      (Uop Snd (Pair (from_cv left) (from_cv right)))
      (refs:hol_refs) =
    (M_success (from_cv right),refs)
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_lc_num_canonical_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_lc_num_canonical» [from_cv encoded])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_lc_num_canonical encoded)),refs)
Proof
  Cases_on `clock`
  >> simp []
  >> Cases_on `encoded`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_lc_num_canonical_lookup,
        registered_case10173_lc_num_canonical_body_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        compute_execTheory.from_cv_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        bounded_object_lc_num_canonical_def]
QED

Theorem registered_case10173_lc_num_canonical_fst_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_lc_num_canonical»
        [Uop Fst (Pair (from_cv left) (from_cv right))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_lc_num_canonical left)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_lc_num_canonical»
          [Uop Fst (Pair (from_cv left) (from_cv right))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_lc_num_canonical» [from_cv left]) refs` by
       (irule compute_eval_app1_argument_result
        >> simp [compute_eval_uop_fst_from_cv_components])
  >> simp [registered_case10173_lc_num_canonical_eval]
QED

Theorem registered_case10173_lc_num_canonical_snd_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_lc_num_canonical»
        [Uop Snd (Pair (from_cv left) (from_cv right))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_lc_num_canonical right)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_lc_num_canonical»
          [Uop Snd (Pair (from_cv left) (from_cv right))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_lc_num_canonical» [from_cv right]) refs` by
       (irule compute_eval_app1_argument_result
        >> simp [compute_eval_uop_snd_from_cv_components])
  >> simp [registered_case10173_lc_num_canonical_eval]
QED

Theorem registered_case10173_lc_z_canonical_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_lc_z_canonical» [from_cv encoded])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«encoded»,from_cv encoded)]
        registered_case10173_lc_z_canonical_body) refs
Proof
  strip_tac
  >> irule compute_eval_literal_app1
  >> simp [registered_case10173_lc_z_canonical_lookup]
QED

Theorem registered_case10173_lc_z_canonical_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_lc_z_canonical» [from_cv encoded])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_lc_z_canonical encoded)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_lc_z_canonical_unfold]
  >> simp
       [registered_case10173_lc_z_canonical_body_def,
        compute_evalTheory.subst_def]
  >> Cases_on `encoded`
  >- simp
       [compute_eval_if_ispair_from_cv,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        bounded_object_lc_z_canonical_def]
  >> simp
       [compute_eval_if_ispair_from_cv,
        compute_execProofTheory.compute_eval_from_cv,
        bounded_object_lc_z_canonical_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        registered_case10173_lc_num_canonical_fst_eval,
        registered_case10173_lc_num_canonical_snd_eval]
QED

Theorem registered_case10173_lc_z_canonical_fst_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_lc_z_canonical»
        [Uop Fst (Pair (from_cv left) (from_cv right))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_lc_z_canonical left)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_lc_z_canonical»
          [Uop Fst (Pair (from_cv left) (from_cv right))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_lc_z_canonical» [from_cv left]) refs` by
       (irule compute_eval_app1_argument_result
        >> simp [compute_eval_uop_fst_from_cv_components])
  >> simp [registered_case10173_lc_z_canonical_eval]
QED

Theorem registered_case10173_lc_z_canonical_snd_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_lc_z_canonical»
        [Uop Snd (Pair (from_cv left) (from_cv right))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_lc_z_canonical right)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_lc_z_canonical»
          [Uop Snd (Pair (from_cv left) (from_cv right))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_lc_z_canonical» [from_cv right]) refs` by
       (irule compute_eval_app1_argument_result
        >> simp [compute_eval_uop_snd_from_cv_components])
  >> simp [registered_case10173_lc_z_canonical_eval]
QED

Theorem registered_case10173_q_canonical_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_canonical» [from_cv encoded])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«encoded»,from_cv encoded)]
        registered_case10173_q_canonical_body) refs
Proof
  strip_tac
  >> irule compute_eval_literal_app1
  >> simp [registered_case10173_q_canonical_lookup]
QED

Theorem registered_case10173_q_canonical_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_canonical» [from_cv encoded])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_canonical encoded)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_q_canonical_unfold]
  >> simp
       [registered_case10173_q_canonical_body_def,
        compute_evalTheory.subst_def]
  >> Cases_on `encoded`
  >- simp
       [compute_eval_if_ispair_from_cv,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        bounded_object_q_canonical_def]
  >> simp
       [compute_eval_if_ispair_from_cv,
        compute_execProofTheory.compute_eval_from_cv,
        bounded_object_q_canonical_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        registered_case10173_lc_z_canonical_fst_eval,
        registered_case10173_lc_num_canonical_snd_eval]
QED

Theorem registered_case10173_q_canonical_fst_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_canonical»
        [Uop Fst (Pair (from_cv left) (from_cv right))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_canonical left)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_canonical»
          [Uop Fst (Pair (from_cv left) (from_cv right))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_canonical» [from_cv left]) refs` by
       (irule compute_eval_app1_argument_result
        >> simp [compute_eval_uop_fst_from_cv_components])
  >> simp [registered_case10173_q_canonical_eval]
QED

Theorem registered_case10173_q_canonical_snd_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_canonical»
        [Uop Snd (Pair (from_cv left) (from_cv right))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_canonical right)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_canonical»
          [Uop Snd (Pair (from_cv left) (from_cv right))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_canonical» [from_cv right]) refs` by
       (irule compute_eval_app1_argument_result
        >> simp [compute_eval_uop_snd_from_cv_components])
  >> simp [registered_case10173_q_canonical_eval]
QED

Theorem registered_case10173_q_interval_canonical_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_canonical» [from_cv encoded])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«encoded»,from_cv encoded)]
        registered_case10173_q_interval_canonical_body) refs
Proof
  strip_tac
  >> irule compute_eval_literal_app1
  >> simp [registered_case10173_q_interval_canonical_lookup]
QED

Theorem registered_case10173_q_interval_canonical_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_canonical» [from_cv encoded])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_canonical encoded)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_q_interval_canonical_unfold]
  >> simp
       [registered_case10173_q_interval_canonical_body_def,
        compute_evalTheory.subst_def]
  >> Cases_on `encoded`
  >- simp
       [compute_eval_if_ispair_from_cv,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        bounded_object_q_interval_canonical_def]
  >> simp
       [compute_eval_if_ispair_from_cv,
        compute_execProofTheory.compute_eval_from_cv,
        bounded_object_q_interval_canonical_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        registered_case10173_q_canonical_fst_eval,
        registered_case10173_q_canonical_snd_eval]
QED

val _ = export_theory ();
