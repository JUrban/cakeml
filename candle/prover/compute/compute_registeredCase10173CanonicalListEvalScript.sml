(*****************************************************************************
 * Recursive registered-evaluator semantics for historical job canonicality.
 *
 * The fixed-depth numeric canonicalizers are discharged in the predecessor
 * theory.  This layer handles the recursive interval-list representation
 * without unfolding the complete historical equation bundle.
 *****************************************************************************)
Theory compute_registeredCase10173CanonicalListEval
Ancestors
  compute_registeredCase10173CanonicalEval
Libs
  bossLib preamble

Theorem registered_case10173_q_interval_canonical_fst_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_canonical»
        [Uop Fst (Pair (from_cv left) (from_cv right))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_canonical left)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_canonical»
          [Uop Fst (Pair (from_cv left) (from_cv right))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_canonical» [from_cv left]) refs` by
       (irule compute_eval_app1_argument_result
        >> simp [compute_eval_uop_fst_from_cv_components])
  >> simp [registered_case10173_q_interval_canonical_eval]
QED

Theorem registered_case10173_q_interval_canonical_snd_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_canonical»
        [Uop Snd (Pair (from_cv left) (from_cv right))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_canonical right)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_canonical»
          [Uop Snd (Pair (from_cv left) (from_cv right))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_canonical» [from_cv right]) refs` by
       (irule compute_eval_app1_argument_result
        >> simp [compute_eval_uop_snd_from_cv_components])
  >> simp [registered_case10173_q_interval_canonical_eval]
QED

Theorem registered_case10173_q_interval_list_canonical_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_list_canonical» [from_cv encoded])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«encoded»,from_cv encoded)]
        registered_case10173_q_interval_list_canonical_body) refs
Proof
  strip_tac
  >> irule compute_eval_literal_app1
  >> simp [registered_case10173_q_interval_list_canonical_lookup]
QED

Theorem compute_eval_if_ispair_from_cv_components:
  compute_eval clock ceqs
      (If (Uop Ispair (Pair (from_cv left) (from_cv right)))
        pair_branch number_branch) (refs:hol_refs) =
    compute_eval clock ceqs pair_branch refs
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_interval_list_canonical_eval:
  !encoded clock refs.
    cv_size encoded + 4 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical» [from_cv encoded])
        (refs:hol_refs) =
      (M_success
        (from_cv (bounded_object_q_interval_list_canonical encoded)),refs)
Proof
  Induct_on `encoded`
  >- (rpt strip_tac
      >> simp [registered_case10173_q_interval_list_canonical_unfold]
      >> simp
           [registered_case10173_q_interval_list_canonical_body_def,
            compute_evalTheory.subst_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def,
            compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_q_interval_list_canonical_def])
  >> rpt strip_tac
  >> simp [registered_case10173_q_interval_list_canonical_unfold]
  >> simp
       [registered_case10173_q_interval_list_canonical_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [compute_eval_if_ispair_from_cv_components,
        compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_q_interval_list_canonical_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical»
          [Uop Snd (Pair (from_cv encoded) (from_cv encoded'))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical»
          [from_cv encoded']) refs` by
       (irule compute_eval_app1_argument_result
        >> simp
             [compute_eval_uop_snd_from_cv_components,
              cvTheory.cv_size_def])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical»
          [Uop Snd (Pair (from_cv encoded) (from_cv encoded'))]) refs =
      (M_success
        (from_cv
          (bounded_object_q_interval_list_canonical encoded')),refs)` by
       (qpat_x_assum
          `compute_eval (clock - 1)
             registered_case10173_historical_chunk16_ceqs
             (App «candle_cv_q_interval_list_canonical»
               [Uop Snd
                 (Pair (from_cv encoded) (from_cv encoded'))]) refs = _`
          SUBST1_TAC
        >> qpat_x_assum
             `!clock refs. cv_size encoded' + 4 < clock ==> _`
             (qspecl_then [`clock - 1`,`refs`] mp_tac)
        >> fs [cvTheory.cv_size_def])
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        registered_case10173_q_interval_canonical_fst_eval,
        cvTheory.cv_size_def]
QED

Theorem compute_eval_uop_fst_from_cv_components3:
  compute_eval clock ceqs
      (Uop Fst
        (Pair (from_cv head_cv)
          (Pair (from_cv middle_cv) (from_cv tail_cv))))
      (refs:hol_refs) =
    (M_success (from_cv head_cv),refs)
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_fst_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_uop_fst_snd_from_cv_components3:
  compute_eval clock ceqs
      (Uop Fst
        (Uop Snd
          (Pair (from_cv head_cv)
            (Pair (from_cv middle_cv) (from_cv tail_cv)))))
      (refs:hol_refs) =
    (M_success (from_cv middle_cv),refs)
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_fst_def,
     compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_eval_uop_snd_snd_from_cv_components3:
  compute_eval clock ceqs
      (Uop Snd
        (Uop Snd
          (Pair (from_cv head_cv)
            (Pair (from_cv middle_cv) (from_cv tail_cv)))))
      (refs:hol_refs) =
    (M_success (from_cv tail_cv),refs)
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_fst_def,
     compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_interval_list_canonical_head3_eval:
  cv_size head_cv + 4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_list_canonical»
        [Uop Fst
          (Pair (from_cv head_cv)
            (Pair (from_cv middle_cv) (from_cv tail_cv)))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_list_canonical head_cv)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical»
          [Uop Fst
            (Pair (from_cv head_cv)
              (Pair (from_cv middle_cv) (from_cv tail_cv)))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical»
          [from_cv head_cv]) refs` by
       (irule compute_eval_app1_argument_result
        >> simp [compute_eval_uop_fst_from_cv_components3])
  >> simp [registered_case10173_q_interval_list_canonical_eval]
QED

Theorem registered_case10173_q_interval_list_canonical_fst_eval:
  cv_size left + 4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_list_canonical»
        [Uop Fst (Pair (from_cv left) (from_cv right))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_list_canonical left)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical»
          [Uop Fst (Pair (from_cv left) (from_cv right))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical» [from_cv left]) refs` by
       (irule compute_eval_app1_argument_result
        >> simp [compute_eval_uop_fst_from_cv_components])
  >> simp [registered_case10173_q_interval_list_canonical_eval]
QED

Theorem registered_case10173_q_interval_list_canonical_fst_snd_eval:
  cv_size middle_cv + 4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_list_canonical»
        [Uop Fst
          (Uop Snd
            (Pair (from_cv head_cv)
              (Pair (from_cv middle_cv) (from_cv tail_cv))))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_list_canonical middle_cv)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical»
          [Uop Fst
            (Uop Snd
              (Pair (from_cv head_cv)
                (Pair (from_cv middle_cv) (from_cv tail_cv))))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical»
          [from_cv middle_cv]) refs` by
       (irule compute_eval_app1_argument_result
        >> simp [compute_eval_uop_fst_snd_from_cv_components3])
  >> simp [registered_case10173_q_interval_list_canonical_eval]
QED

Theorem registered_case10173_q_interval_list_canonical_snd_snd_eval:
  cv_size tail_cv + 4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_list_canonical»
        [Uop Snd
          (Uop Snd
            (Pair (from_cv head_cv)
              (Pair (from_cv middle_cv) (from_cv tail_cv))))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_list_canonical tail_cv)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical»
          [Uop Snd
            (Uop Snd
              (Pair (from_cv head_cv)
                (Pair (from_cv middle_cv) (from_cv tail_cv))))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical»
          [from_cv tail_cv]) refs` by
       (irule compute_eval_app1_argument_result
        >> simp [compute_eval_uop_snd_snd_from_cv_components3])
  >> simp [registered_case10173_q_interval_list_canonical_eval]
QED

Theorem registered_case10173_fso_variable_job_canonical_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_variable_job_canonical» [from_cv encoded])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«encoded»,from_cv encoded)]
        registered_case10173_fso_variable_job_canonical_body) refs
Proof
  strip_tac
  >> irule compute_eval_literal_app1
  >> simp [registered_case10173_fso_variable_job_canonical_lookup]
QED

Theorem registered_case10173_fso_variable_job_canonical_eval:
  cv_size (Pair box (Pair roots_lower roots_upper)) + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_variable_job_canonical»
        [from_cv (Pair box (Pair roots_lower roots_upper))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_fso_variable_job_canonical
          (Pair box (Pair roots_lower roots_upper)))),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fso_variable_job_canonical_unfold]
  >> simp
       [registered_case10173_fso_variable_job_canonical_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_fso_variable_job_canonical_def,
        compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_cv_fst_def,
        compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_cv_snd_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> fs [cvTheory.cv_size_def]
  >> simp
       [registered_case10173_q_interval_list_canonical_head3_eval]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        registered_case10173_q_interval_list_canonical_fst_snd_eval,
        registered_case10173_q_interval_list_canonical_snd_snd_eval,
        cvTheory.cv_size_def]
QED

Theorem registered_case10173_fso_variable_job_canonical_fst_eval:
  cv_size (Pair box (Pair roots_lower roots_upper)) + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_variable_job_canonical»
        [Uop Fst
          (from_cv
            (Pair (Pair box (Pair roots_lower roots_upper)) remaining))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_fso_variable_job_canonical
          (Pair box (Pair roots_lower roots_upper)))),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fso_variable_job_canonical»
          [Uop Fst
            (from_cv
              (Pair (Pair box (Pair roots_lower roots_upper)) remaining))])
        refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fso_variable_job_canonical»
          [from_cv (Pair box (Pair roots_lower roots_upper))]) refs` by
       (irule compute_eval_app1_argument_result
        >> simp [compute_eval_uop_fst_from_cv_pair])
  >> simp [registered_case10173_fso_variable_job_canonical_eval]
QED

Theorem registered_case10173_fso_variable_jobs_canonical_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_variable_jobs_canonical» [from_cv encoded])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«encoded»,from_cv encoded)]
        registered_case10173_fso_variable_jobs_canonical_body) refs
Proof
  strip_tac
  >> irule compute_eval_literal_app1
  >> simp [registered_case10173_fso_variable_jobs_canonical_lookup]
QED

Theorem bounded_object_fso_variable_jobs_canonical_pair_fixed_components:
  bounded_object_fso_variable_jobs_canonical (Pair object_job object_jobs) =
      Pair object_job object_jobs ==>
  ?box roots_lower roots_upper.
    object_job = Pair box (Pair roots_lower roots_upper) /\
    bounded_object_fso_variable_job_canonical object_job = object_job /\
    bounded_object_fso_variable_jobs_canonical object_jobs = object_jobs
Proof
  Cases_on `object_job`
  >> fs
       [compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_fso_variable_jobs_canonical_def,
        compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_fso_variable_job_canonical_def,
        compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_cv_fst_def,
        compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_cv_snd_def]
  >> Cases_on `c0`
  >> fs
       [compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_fso_variable_jobs_canonical_def,
        compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_fso_variable_job_canonical_def,
        compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_cv_fst_def,
        compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_cv_snd_def]
  >> metis_tac []
QED

Theorem compute_eval_if_ispair_num:
  compute_eval clock ceqs
      (If (Uop Ispair (Num n)) pair_branch number_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs number_branch refs
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fso_variable_jobs_canonical_eval_fixed:
  !encoded clock refs.
    bounded_object_fso_variable_jobs_canonical encoded = encoded /\
    cv_size encoded + 6 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fso_variable_jobs_canonical» [from_cv encoded])
        (refs:hol_refs) =
      (M_success (from_cv encoded),refs)
Proof
  Induct_on `encoded`
  >- (rpt strip_tac
      >> simp [registered_case10173_fso_variable_jobs_canonical_unfold]
      >> fs
           [compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_fso_variable_jobs_canonical_def]
      >> simp
           [registered_case10173_fso_variable_jobs_canonical_body_def,
            compute_evalTheory.subst_def]
      >> simp
           [compute_eval_if_ispair_num,
            compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt strip_tac
  >> drule bounded_object_fso_variable_jobs_canonical_pair_fixed_components
  >> strip_tac
  >> qpat_x_assum
       `encoded = Pair box (Pair roots_lower roots_upper)` SUBST_ALL_TAC
  >> simp [registered_case10173_fso_variable_jobs_canonical_unfold]
  >> simp
       [registered_case10173_fso_variable_jobs_canonical_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (Uop Ispair
          (Pair
            (Pair (from_cv box)
              (Pair (from_cv roots_lower) (from_cv roots_upper)))
            (from_cv encoded'))) refs =
      (M_success (Num 1),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_ispair_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> fs []
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fso_variable_job_canonical»
          [Uop Fst
            (Pair
              (Pair (from_cv box)
                (Pair (from_cv roots_lower) (from_cv roots_upper)))
              (from_cv encoded'))]) refs =
      (M_success
        (Pair (from_cv box)
          (Pair (from_cv roots_lower) (from_cv roots_upper))),refs)` by
       (`App «candle_cv_fso_variable_job_canonical»
            [Uop Fst
              (Pair
                (Pair (from_cv box)
                  (Pair (from_cv roots_lower) (from_cv roots_upper)))
                (from_cv encoded'))] =
          App «candle_cv_fso_variable_job_canonical»
            [Uop Fst
              (from_cv
                (Pair
                  (Pair box (Pair roots_lower roots_upper)) encoded'))]` by
            simp [compute_execTheory.from_cv_def]
        >> qpat_x_assum `App _ _ = App _ _` SUBST1_TAC
        >> mp_tac
             (Q.INST
               [`clock` |-> `clock - 1`,
                `refs` |-> `refs`,
                `box` |-> `box`,
                `roots_lower` |-> `roots_lower`,
                `roots_upper` |-> `roots_upper`,
                `remaining` |-> `encoded'`]
               registered_case10173_fso_variable_job_canonical_fst_eval)
        >> fs [compute_execTheory.from_cv_def])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fso_variable_jobs_canonical»
          [Uop Snd
            (Pair
              (Pair (from_cv box)
                (Pair (from_cv roots_lower) (from_cv roots_upper)))
              (from_cv encoded'))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fso_variable_jobs_canonical»
          [from_cv encoded']) refs` by
       (irule compute_eval_app1_argument_result
        >> simp
             [compute_evalTheory.compute_eval_def,
              compute_execProofTheory.compute_eval_from_cv,
              compute_evalTheory.do_uop_def,
              compute_evalTheory.do_snd_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fso_variable_jobs_canonical»
          [Uop Snd
            (Pair
              (Pair (from_cv box)
                (Pair (from_cv roots_lower) (from_cv roots_upper)))
              (from_cv encoded'))]) refs =
      (M_success (from_cv encoded'),refs)` by
       (qpat_x_assum
          `compute_eval _ _
             (App «candle_cv_fso_variable_jobs_canonical» [Uop Snd _]) _ = _`
          SUBST1_TAC
        >> qpat_x_assum
             `!clock' refs'. cv_size encoded' + 6 < clock' ==> _`
             (qspecl_then [`clock - 1`,`refs`] mp_tac)
        >> fs [])
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fso_variable_jobs_canonical_eval_authenticated:
  bounded_packed_chars_case10173_decimal_authenticated_full_check bytes
      encoded_jobs encoded_roots /\
  cv_size encoded_jobs + 6 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_variable_jobs_canonical»
        [from_cv encoded_jobs]) (refs:hol_refs) =
    (M_success (from_cv encoded_jobs),refs)
Proof
  strip_tac
  >> irule registered_case10173_fso_variable_jobs_canonical_eval_fixed
  >> conj_tac
  >- fs []
  >> metis_tac
       [compute_boundedCase10173ObjectJobCanonicalTheory.bounded_packed_chars_case10173_decimal_authenticated_full_jobs_canonical]
QED

val _ = export_theory ();
