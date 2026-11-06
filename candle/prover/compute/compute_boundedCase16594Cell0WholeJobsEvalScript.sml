(*****************************************************************************
 * Evaluator semantics for the genuine singleton jobs list.                  *
 *                                                                            *
 * The recursive wrapper is proved around the separately authenticated job;  *
 * no numerical action trace is replayed here.                                *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WholeJobsEval
Ancestors
  compute_boundedCase16594Cell0WholeJobEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_cell0_whole_jobs_check_body_def:
  bounded_case16594_cell0_whole_jobs_check_body =
    If (Uop Ispair (Var «packed_cells»))
      (If (Uop Ispair (Var «jobs»))
        (App «candle_cv_bool_and»
          [Binop Eq
            (App «candle_cv_q_packed_object_whole_job_check»
              [Var «plan_codes»;Var «source_instructions»;
               Uop Fst (Var «packed_cells»);Uop Fst (Var «jobs»)])
            (Num 1);
           App «candle_cv_q_packed_object_whole_jobs_check»
             [Var «plan_codes»;Var «source_instructions»;
              Uop Snd (Var «packed_cells»);Uop Snd (Var «jobs»)]])
        (Num 0))
      (If (Uop Ispair (Var «jobs»)) (Num 0)
        (App «candle_cv_bool_and»
          [Binop Eq (Var «packed_cells») (Num 0);
           Binop Eq (Var «jobs») (Num 0)]))
End

Definition bounded_case16594_cell0_whole_bool_and_body_def:
  bounded_case16594_cell0_whole_bool_and_body =
    If (Var «a») (Var «b») (Num 0)
End

Theorem bounded_case16594_cell0_whole_jobs_check_named_lookup:
  ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
      «candle_cv_q_packed_object_whole_jobs_check» =
    SOME
      ([«plan_codes»;«source_instructions»;«packed_cells»;«jobs»],
       bounded_case16594_cell0_whole_jobs_check_body)
Proof
  rw
    [compute_boundedCase16594Cell0WholeCombinedLookupsTheory.bounded_case16594_cell0_whole_combined_whole_jobs_check_lookup,
     bounded_case16594_cell0_whole_jobs_check_body_def]
QED

Theorem bounded_case16594_cell0_whole_bool_and_named_lookup:
  ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
      «candle_cv_bool_and» =
    SOME ([«a»;«b»],bounded_case16594_cell0_whole_bool_and_body)
Proof
  rw
    [compute_boundedCase16594Cell0WholeCombinedLookupsTheory.bounded_case16594_cell0_whole_combined_bool_and_lookup,
     bounded_case16594_cell0_whole_bool_and_body_def]
QED

Theorem bounded_case16594_cell0_compute_eval_literal_app4:
  0 < clock /\
  ALOOKUP ceqs function_name =
      SOME ([name1;name2;name3;name4],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv value1;from_cv value2;from_cv value3;from_cv value4])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name1,from_cv value1);(name2,from_cv value2);
         (name3,from_cv value3);(name4,from_cv value4)] body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_jobs_check_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_jobs_check»
      [from_cv plan_codes;from_cv source_instructions;
       from_cv packed_cells;from_cv jobs]) (refs:hol_refs) =
  compute_eval (clock - 1) bounded_case16594_cell0_whole_combined_ceqs
    (subst
      [(«plan_codes»,from_cv plan_codes);
       («source_instructions»,from_cv source_instructions);
       («packed_cells»,from_cv packed_cells);(«jobs»,from_cv jobs)]
      bounded_case16594_cell0_whole_jobs_check_body) refs
Proof
  strip_tac
  >> irule bounded_case16594_cell0_compute_eval_literal_app4
  >> simp [bounded_case16594_cell0_whole_jobs_check_named_lookup]
QED

Theorem bounded_case16594_cell0_whole_bool_and_true_one_eval:
  0 < clock /\
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      first_expression (refs:hol_refs) = (M_success (Num 1),refs) /\
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      second_expression refs = (M_success (Num 1),refs) ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_bool_and» [first_expression;second_expression]) refs =
    (M_success (Num 1),refs)
Proof
  Cases_on `clock`
  >- simp []
  >> strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_case16594_cell0_whole_bool_and_named_lookup,
        compute_evalTheory.option_def,compute_evalTheory.check_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        bounded_case16594_cell0_whole_bool_and_body_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_compute_eval_if_true_result:
  compute_eval clock ceqs condition (refs:hol_refs) =
      (M_success (Num 1),refs) /\
  compute_eval clock ceqs true_branch refs = result ==>
  compute_eval clock ceqs (If condition true_branch false_branch) refs = result
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     ml_monadBaseTheory.st_ex_bind_def]
QED

Theorem bounded_case16594_cell0_whole_compute_eval_app4_argument_results:
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
        [from_cv result1;from_cv result2;from_cv result3;from_cv result4])
      refs
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
        compute_evalTheory.option_def,compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_compute_eval_pair_fst:
  compute_eval clock ceqs
      (Uop Fst (from_cv (Pair left right))) (refs:hol_refs) =
    (M_success (from_cv left),refs)
Proof
  simp
    [compute_execTheory.from_cv_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
     compute_execProofTheory.compute_eval_from_cv,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_compute_eval_pair_snd:
  compute_eval clock ceqs
      (Uop Snd (from_cv (Pair left right))) (refs:hol_refs) =
    (M_success (from_cv right),refs)
Proof
  simp
    [compute_execTheory.from_cv_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
     compute_execProofTheory.compute_eval_from_cv,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_compute_eval_eq_one:
  compute_eval clock ceqs expression (refs:hol_refs) =
      (M_success (Num 1),refs) ==>
  compute_eval clock ceqs (Binop Eq expression (Num 1)) refs =
    (M_success (Num 1),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_binop_def,compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_nil_tails:
  bounded_case16594_cell0_whole_packed_cells_tail = Num 0 /\
  bounded_case16594_cell0_whole_jobs_tail = Num 0
Proof
  rw
    [compute_boundedCase16594Cell0WholeStructureTheory.bounded_case16594_cell0_whole_packed_cells_tail_def,
     compute_boundedCase16594Cell0WholeStructureTheory.bounded_case16594_cell0_whole_jobs_tail_def]
QED

Theorem bounded_case16594_cell0_whole_jobs_empty_eval:
  3 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_jobs_check»
      [from_cv bounded_case16594_cell0_whole_plan_codes;
       from_cv bounded_case16594_cell0_whole_source_instructions;
       from_cv (Num 0);from_cv (Num 0)]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_cell0_whole_jobs_check_unfold]
  >> simp
       [bounded_case16594_cell0_whole_jobs_check_body_def,
        bounded_case16594_cell0_whole_bool_and_named_lookup,
        bounded_case16594_cell0_whole_bool_and_body_def,
        compute_evalTheory.option_def,compute_evalTheory.check_def,
        compute_evalTheory.compute_eval_def,compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_execTheory.from_cv_def,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_eq_def,compute_evalTheory.do_binop_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_jobs_singleton_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_runtime_cell0_codes_cv + 12 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_jobs_check»
      [from_cv bounded_case16594_cell0_whole_plan_codes;
       from_cv bounded_case16594_cell0_whole_source_instructions;
       from_cv
         (Pair bounded_case16594_cell0_whole_packed_cell (Num 0));
       from_cv (Pair bounded_case16594_cell0_whole_job (Num 0))])
    (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_cell0_whole_jobs_check_unfold]
  >> simp
       [bounded_case16594_cell0_whole_jobs_check_body_def,
        compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule bounded_case16594_cell0_whole_compute_eval_if_true_result
  >> conj_tac
  >- simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_execTheory.from_cv_def,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule bounded_case16594_cell0_whole_compute_eval_if_true_result
  >> conj_tac
  >- simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_execTheory.from_cv_def,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule bounded_case16594_cell0_whole_bool_and_true_one_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_cell0_whole_compute_eval_eq_one
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_cell0_whole_combined_ceqs
              (App «candle_cv_q_packed_object_whole_job_check»
                [from_cv bounded_case16594_cell0_whole_plan_codes;
                 from_cv bounded_case16594_cell0_whole_source_instructions;
                 from_cv bounded_case16594_cell0_whole_packed_cell;
                 from_cv bounded_case16594_cell0_whole_job]) refs`
      >> conj_tac
      >- (irule
            bounded_case16594_cell0_whole_compute_eval_app4_argument_results
          >> simp
               [bounded_case16594_cell0_whole_compute_eval_pair_fst,
                compute_execProofTheory.compute_eval_from_cv,
                compute_execTheory.from_cv_def,
                compute_evalTheory.compute_eval_def,
                compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
                ml_monadBaseTheory.st_ex_bind_def,
                ml_monadBaseTheory.st_ex_return_def]
          >> intLib.ARITH_TAC)
      >> irule
           (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
             bounded_case16594_cell0_whole_job_check_eval_clock)
      >> intLib.ARITH_TAC)
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_cell0_whole_combined_ceqs
          (App «candle_cv_q_packed_object_whole_jobs_check»
            [from_cv bounded_case16594_cell0_whole_plan_codes;
             from_cv bounded_case16594_cell0_whole_source_instructions;
             from_cv (Num 0);from_cv (Num 0)]) refs`
  >> conj_tac
  >- (irule bounded_case16594_cell0_whole_compute_eval_app4_argument_results
      >> simp
           [bounded_case16594_cell0_whole_compute_eval_pair_snd,
            compute_execProofTheory.compute_eval_from_cv,
            compute_execTheory.from_cv_def,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_cell0_whole_jobs_empty_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
