(*****************************************************************************
 * Evaluator semantics for the one genuine case-16594 cell-0 whole-call job. *
 *                                                                            *
 * This is deliberately a control-flow theorem: the expensive numerical      *
 * conclusion is supplied by the already authenticated production-dispatch   *
 * entry theorem rather than replayed through the wrapper.                    *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WholeJobEval
Ancestors
  compute_boundedCase16594Cell0WholeStructure
Libs
  bossLib preamble intLib

Theorem bounded_case16594_cell0_whole_job_check_unfold:
  5 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_job_check»
      [from_cv bounded_case16594_cell0_whole_plan_codes;
       from_cv bounded_case16594_cell0_whole_source_instructions;
       from_cv bounded_case16594_cell0_whole_packed_cell;
       from_cv bounded_case16594_cell0_whole_job])
    (refs:hol_refs) =
  compute_eval (clock - 5) bounded_case16594_cell0_whole_combined_ceqs
    bounded_case16594_cell0_whole_dispatch_cexp refs
Proof
  Cases_on `clock`
  >- simp []
  >> strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_boundedCase16594Cell0WholeCombinedLookupsTheory.bounded_case16594_cell0_whole_combined_whole_job_check_lookup,
        compute_evalTheory.option_def,compute_evalTheory.check_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_case16594_cell0_whole_packed_cell_shape,
        bounded_case16594_cell0_whole_job_shape,
        bounded_case16594_cell0_whole_dispatch_cexp_def,
        compute_execTheory.from_cv_def,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_fst_def,compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> `n - 5 = SUC n - 6` by intLib.ARITH_TAC
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_cell0_whole_job_check_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_runtime_cell0_codes_cv + 8 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_job_check»
      [from_cv bounded_case16594_cell0_whole_plan_codes;
       from_cv bounded_case16594_cell0_whole_source_instructions;
       from_cv bounded_case16594_cell0_whole_packed_cell;
       from_cv bounded_case16594_cell0_whole_job])
    (refs:hol_refs) = (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> `5 < clock` by intLib.ARITH_TAC
  >> rw [bounded_case16594_cell0_whole_job_check_unfold]
  >> once_rewrite_tac [bounded_case16594_cell0_whole_dispatch_identity]
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         compute_boundedCase16594Cell0WholeCombinedEntryTheory.bounded_case16594_cell0_fast_hol_light_entry_eval_combined_clock)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
