(*****************************************************************************
 * Compose the genuine first-job source execution with the small certified
 * handoff.  No memoized historical program result is used in this theory.
 *****************************************************************************)
Theory compute_registeredCase10173FastGenuineCertifiedEval
Ancestors
  compute_registeredCase10173FastGenuineProgramRun
  compute_registeredCase10173FastLiteralHandoff
Libs
  bossLib preamble intLib

Theorem registered_case10173_fast_literal_final_stack_exact:
  registered_case10173_ordinary_result_push
      (registered_case10173_taylor_object
        registered_case10173_fast_literal_result)
      (Num 0) =
    Pair registered_case10173_fast_literal_item (Num 0)
Proof
  simp
    [compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_result_push_def,
     compute_registeredCase10173FastLiteralHandoffTheory.registered_case10173_fast_literal_item_def]
QED

Theorem registered_case10173_genuine_fast_program_run_spliced_eval:
  38266 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv registered_case10173_genuine_center_boxes;
         from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_genuine_encoded_radii;
         from_cv registered_case10173_first_job_roots;
         App «candle_cv_case10173_hist_splice_aux»
           [Num 31;from_cv registered_case10173_genuine_center_program];
         App «candle_cv_case10173_hist_splice_aux»
           [Num 31;from_cv registered_case10173_genuine_box_program];
         Num 0]) (refs:hol_refs) =
    (M_success
      (from_cv (Pair registered_case10173_fast_literal_item (Num 0))),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_case10173_hist_program_run»
          [from_cv registered_case10173_genuine_center_boxes;
           from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_genuine_encoded_radii;
           from_cv registered_case10173_first_job_roots;
           App «candle_cv_case10173_hist_splice_aux»
             [Num 31;from_cv registered_case10173_genuine_center_program];
           App «candle_cv_case10173_hist_splice_aux»
             [Num 31;from_cv registered_case10173_genuine_box_program];
           Num 0]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_case10173_hist_program_run»
          [from_cv registered_case10173_genuine_center_boxes;
           from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_genuine_encoded_radii;
           from_cv registered_case10173_first_job_roots;
           from_cv registered_case10173_genuine_spliced_center_program;
           from_cv registered_case10173_genuine_spliced_box_program;
           from_cv (Num 0)]) refs` by
       (irule
          compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_compute_eval_app7_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173GenuineProgramResultEvalTheory.registered_case10173_genuine_center_splice_eval,
              compute_registeredCase10173GenuineProgramResultEvalTheory.registered_case10173_genuine_box_splice_eval,
              compute_evalTheory.compute_eval_def,
              ml_monadBaseTheory.st_ex_return_def]
        >> intLib.ARITH_TAC)
  >> pop_assum SUBST1_TAC
  >> simp
       [compute_registeredCase10173FastGenuineProgramRunTheory.registered_case10173_genuine_fast_literal_program_run_eval,
        registered_case10173_fast_literal_final_stack_exact]
QED

Theorem registered_case10173_genuine_fast_hist_program_eval:
  38269 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program»
        [from_cv registered_case10173_genuine_center_program;
         from_cv registered_case10173_genuine_box_program;
         from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_first_job_roots])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_fast_program_result),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistProgramEvalTheory.registered_case10173_hist_program_eval_from_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `registered_case10173_genuine_center_boxes`
  >> qexists_tac `registered_case10173_fast_literal_item`
  >> qexists_tac `registered_case10173_genuine_encoded_radii`
  >> qexists_tac `Pair registered_case10173_fast_literal_item (Num 0)`
  >> conj_tac
  >- (irule
        compute_registeredCase10173GenuineProgramResultEvalTheory.registered_case10173_genuine_center_environment_source_eval
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule registered_case10173_genuine_fast_program_run_spliced_eval
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule
        compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_head_cons_eval
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule
        compute_registeredCase10173FastLiteralHandoffTheory.registered_case10173_fast_program_result_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173GenuineProgramResultEvalTheory.registered_case10173_genuine_radius_source_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_genuine_fast_hist_certified_check_eval:
  38270 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_certified_check»
        [from_cv registered_case10173_genuine_center_program;
         from_cv registered_case10173_genuine_box_program;
         from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_first_job_roots])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_fast_certified_verdict),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_hist_certified_check_eval_from_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `registered_case10173_fast_program_result`
  >> conj_tac
  >- (irule registered_case10173_genuine_fast_hist_program_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173FastLiteralHandoffTheory.registered_case10173_fast_certified_finish_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_genuine_fast_hist_certified_check_accept:
  38270 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (Uop Fst
        (App «candle_cv_case10173_hist_certified_check»
          [from_cv registered_case10173_genuine_center_program;
           from_cv registered_case10173_genuine_box_program;
           from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_first_job_roots]))
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`verdict` |-> `registered_case10173_fast_certified_verdict`]
         compute_registeredCase10173GenuineProgramResultEvalTheory.registered_case10173_cv_fst_accepts_shape)
  >> impl_tac
  >- simp
       [compute_registeredCase10173FastLiteralHandoffTheory.registered_case10173_fast_certified_verdict_accepts]
  >> strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_genuine_fast_hist_certified_check_eval,
        compute_execTheory.from_cv_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
