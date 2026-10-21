(*****************************************************************************
 * Structural-clock evaluator semantics for historical job canonicality.
 *
 * The older evaluator theorems use cv_size, which charges the magnitude of
 * every encoded numeral.  The canonicalizers themselves inspect only pair
 * spines and fixed-depth rational shapes.  This layer records that operational
 * fact explicitly, so genuine decimal payloads can be justified at Candle's
 * production default clock.
 *****************************************************************************)
Theory compute_registeredCase10173CanonicalStructuralEval
Ancestors
  compute_registeredCase10173CanonicalListEval
Libs
  bossLib preamble intLib

Definition registered_case10173_structural_list_length_def:
  registered_case10173_structural_list_length (Num n : cv) = 0 /\
  registered_case10173_structural_list_length (Pair item items) =
    SUC (registered_case10173_structural_list_length items)
End

Theorem registered_case10173_q_interval_list_canonical_eval_structural:
  !encoded clock refs.
    registered_case10173_structural_list_length encoded + 4 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical» [from_cv encoded])
        (refs:hol_refs) =
      (M_success
        (from_cv (bounded_object_q_interval_list_canonical encoded)),refs)
Proof
  Induct_on `encoded`
  >- (rpt strip_tac
      >> simp
           [compute_registeredCase10173CanonicalListEvalTheory.registered_case10173_q_interval_list_canonical_unfold]
      >> simp
           [compute_registeredCase10173CanonicalEvalTheory.registered_case10173_q_interval_list_canonical_body_def,
            compute_evalTheory.subst_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def,
            compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_q_interval_list_canonical_def])
  >> rpt strip_tac
  >> simp
       [compute_registeredCase10173CanonicalListEvalTheory.registered_case10173_q_interval_list_canonical_unfold]
  >> simp
       [compute_registeredCase10173CanonicalEvalTheory.registered_case10173_q_interval_list_canonical_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components,
        compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_q_interval_list_canonical_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical»
          [Uop Snd (Pair (from_cv encoded) (from_cv encoded'))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_list_canonical»
          [from_cv encoded']) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components,
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
             `!clock refs.
                registered_case10173_structural_list_length encoded' + 4 <
                  clock ==> _`
             (qspecl_then [`clock - 1`,`refs`] mp_tac)
        >> fs [registered_case10173_structural_list_length_def])
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        compute_registeredCase10173CanonicalListEvalTheory.registered_case10173_q_interval_canonical_fst_eval,
        registered_case10173_structural_list_length_def]
QED

Theorem registered_case10173_q_interval_list_canonical_head3_eval_structural:
  registered_case10173_structural_list_length head_cv + 4 < clock ==>
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
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalListEvalTheory.compute_eval_uop_fst_from_cv_components3])
  >> simp [registered_case10173_q_interval_list_canonical_eval_structural]
QED

Theorem registered_case10173_q_interval_list_canonical_fst_snd_eval_structural:
  registered_case10173_structural_list_length middle_cv + 4 < clock ==>
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
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalListEvalTheory.compute_eval_uop_fst_snd_from_cv_components3])
  >> simp [registered_case10173_q_interval_list_canonical_eval_structural]
QED

Theorem registered_case10173_q_interval_list_canonical_snd_snd_eval_structural:
  registered_case10173_structural_list_length tail_cv + 4 < clock ==>
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
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalListEvalTheory.compute_eval_uop_snd_snd_from_cv_components3])
  >> simp [registered_case10173_q_interval_list_canonical_eval_structural]
QED

Theorem registered_case10173_fso_variable_job_canonical_eval_structural:
  registered_case10173_structural_list_length box + 5 < clock /\
  registered_case10173_structural_list_length roots_lower + 5 < clock /\
  registered_case10173_structural_list_length roots_upper + 5 < clock ==>
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
  >> simp
       [compute_registeredCase10173CanonicalListEvalTheory.registered_case10173_fso_variable_job_canonical_unfold]
  >> simp
       [compute_registeredCase10173CanonicalEvalTheory.registered_case10173_fso_variable_job_canonical_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_fso_variable_job_canonical_def,
        compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_cv_fst_def,
        compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_cv_snd_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> fs []
  >> simp
       [registered_case10173_q_interval_list_canonical_head3_eval_structural]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        registered_case10173_q_interval_list_canonical_fst_snd_eval_structural,
        registered_case10173_q_interval_list_canonical_snd_snd_eval_structural]
QED

Theorem registered_case10173_fso_variable_job_canonical_eval_structural_fixed:
  bounded_object_fso_variable_job_canonical
      (Pair box (Pair roots_lower roots_upper)) =
    Pair box (Pair roots_lower roots_upper) /\
  registered_case10173_structural_list_length box + 5 < clock /\
  registered_case10173_structural_list_length roots_lower + 5 < clock /\
  registered_case10173_structural_list_length roots_upper + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_variable_job_canonical»
        [from_cv (Pair box (Pair roots_lower roots_upper))])
      (refs:hol_refs) =
    (M_success
      (from_cv (Pair box (Pair roots_lower roots_upper))),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock`,
          `refs` |-> `refs`,
          `box` |-> `box`,
          `roots_lower` |-> `roots_lower`,
          `roots_upper` |-> `roots_upper`]
         registered_case10173_fso_variable_job_canonical_eval_structural)
  >> fs []
QED

Definition registered_case10173_structural_job_clock_def:
  registered_case10173_structural_job_clock (Num n : cv) = 0 /\
  registered_case10173_structural_job_clock (Pair box (Num n)) = 0 /\
  registered_case10173_structural_job_clock
      (Pair box (Pair roots_lower roots_upper)) =
    registered_case10173_structural_list_length box +
    registered_case10173_structural_list_length roots_lower +
    registered_case10173_structural_list_length roots_upper + 5
End

Definition registered_case10173_structural_jobs_clock_def:
  registered_case10173_structural_jobs_clock (Num n : cv) = 1 /\
  registered_case10173_structural_jobs_clock (Pair object_job object_jobs) =
    registered_case10173_structural_job_clock object_job +
    registered_case10173_structural_jobs_clock object_jobs + 1
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Theorem registered_case10173_fso_variable_jobs_canonical_eval_structural:
  !encoded clock refs.
    bounded_object_fso_variable_jobs_canonical encoded = encoded /\
    registered_case10173_structural_jobs_clock encoded < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fso_variable_jobs_canonical» [from_cv encoded])
        (refs:hol_refs) =
      (M_success (from_cv encoded),refs)
Proof
  Induct_on `encoded`
  >- (rpt strip_tac
      >> simp
           [compute_registeredCase10173CanonicalListEvalTheory.registered_case10173_fso_variable_jobs_canonical_unfold]
      >> fs
           [compute_boundedCase10173ObjectJobCanonicalTheory.bounded_object_fso_variable_jobs_canonical_def]
      >> simp
           [compute_registeredCase10173CanonicalEvalTheory.registered_case10173_fso_variable_jobs_canonical_body_def,
            compute_evalTheory.subst_def]
      >> simp
           [compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_num,
            compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt strip_tac
  >> drule
       compute_registeredCase10173CanonicalListEvalTheory.bounded_object_fso_variable_jobs_canonical_pair_fixed_components
  >> strip_tac
  >> qpat_x_assum
       `encoded = Pair box (Pair roots_lower roots_upper)` SUBST_ALL_TAC
  >> simp
       [compute_registeredCase10173CanonicalListEvalTheory.registered_case10173_fso_variable_jobs_canonical_unfold]
  >> simp
       [compute_registeredCase10173CanonicalEvalTheory.registered_case10173_fso_variable_jobs_canonical_body_def,
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
  >> `registered_case10173_structural_list_length box + 5 < clock - 1` by
       (fs
          [registered_case10173_structural_jobs_clock_def,
           registered_case10173_structural_job_clock_def]
        >> intLib.ARITH_TAC)
  >> `registered_case10173_structural_list_length roots_lower + 5 <
        clock - 1` by
       (fs
          [registered_case10173_structural_jobs_clock_def,
           registered_case10173_structural_job_clock_def]
        >> intLib.ARITH_TAC)
  >> `registered_case10173_structural_list_length roots_upper + 5 <
        clock - 1` by
       (fs
          [registered_case10173_structural_jobs_clock_def,
           registered_case10173_structural_job_clock_def]
        >> intLib.ARITH_TAC)
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
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval (clock - 1)
                registered_case10173_historical_chunk16_ceqs
                (App «candle_cv_fso_variable_job_canonical»
                  [from_cv (Pair box (Pair roots_lower roots_upper))]) refs`
        >> conj_tac
        >- (irule
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
            >> simp
                 [compute_evalTheory.compute_eval_def,
                  compute_execProofTheory.compute_eval_from_cv,
                  compute_evalTheory.do_uop_def,
                  compute_evalTheory.do_fst_def,
                  ml_monadBaseTheory.st_ex_bind_def,
                  ml_monadBaseTheory.st_ex_return_def])
        >> mp_tac
             (Q.INST
               [`clock` |-> `clock - 1`,
                `refs` |-> `refs`,
                `box` |-> `box`,
                `roots_lower` |-> `roots_lower`,
                `roots_upper` |-> `roots_upper`]
               registered_case10173_fso_variable_job_canonical_eval_structural_fixed)
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
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
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
             `!clock refs.
                registered_case10173_structural_jobs_clock encoded' < clock ==>
                _`
             (qspecl_then [`clock - 1`,`refs`] mp_tac)
        >> fs
             [registered_case10173_structural_jobs_clock_def,
              registered_case10173_structural_job_clock_def]
        >> intLib.ARITH_TAC)
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
