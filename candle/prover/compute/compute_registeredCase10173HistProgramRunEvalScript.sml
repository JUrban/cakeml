(*****************************************************************************
 * Registered evaluator control semantics for the paired historical program
 * loop.  Numerical instruction semantics remain explicit in [hist_step]; the
 * recursion, termination, instruction selection, and stack threading are
 * proved here once for arbitrary programs.
 *****************************************************************************)
Theory compute_registeredCase10173HistProgramRunEval
Ancestors
  compute_registeredCase10173HistProgramEval
Libs
  bossLib preamble

Definition registered_case10173_hist_program_run_body_def:
  registered_case10173_hist_program_run_body =
    If (Uop Ispair (Var «center_program»))
      (If (Uop Ispair (Var «box_program»))
        (App «candle_cv_case10173_hist_program_run»
          [Var «center_boxes»;Var «boxes»;Var «radii»;Var «roots»;
           Uop Snd (Var «center_program»);
           Uop Snd (Var «box_program»);
           App «candle_cv_case10173_hist_step»
             [Var «center_boxes»;Var «boxes»;Var «radii»;Var «roots»;
              Uop Fst (Var «center_program»);
              Uop Fst (Var «box_program»);Var «stack»]])
        (Var «stack»))
      (Var «stack»)
End

Theorem registered_case10173_hist_program_run_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_case10173_hist_program_run» =
    SOME
      ([«center_boxes»;«boxes»;«radii»;«roots»;
        «center_program»;«box_program»;«stack»],
       registered_case10173_hist_program_run_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_compute_eval_literal_app7:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME
      ([name1;name2;name3;name4;name5;name6;name7],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv argument1;from_cv argument2;from_cv argument3;
         from_cv argument4;from_cv argument5;from_cv argument6;
         from_cv argument7]) (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name1,from_cv argument1);(name2,from_cv argument2);
         (name3,from_cv argument3);(name4,from_cv argument4);
         (name5,from_cv argument5);(name6,from_cv argument6);
         (name7,from_cv argument7)] body) refs
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

Theorem registered_case10173_compute_eval_app7_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) /\
  compute_eval clock ceqs argument3 refs =
      (M_success (from_cv result3),refs) /\
  compute_eval clock ceqs argument4 refs =
      (M_success (from_cv result4),refs) /\
  compute_eval clock ceqs argument5 refs =
      (M_success (from_cv result5),refs) /\
  compute_eval clock ceqs argument6 refs =
      (M_success (from_cv result6),refs) /\
  compute_eval clock ceqs argument7 refs =
      (M_success (from_cv result7),refs) ==>
  compute_eval clock ceqs
      (App function_name
        [argument1;argument2;argument3;argument4;
         argument5;argument6;argument7]) refs =
    compute_eval clock ceqs
      (App function_name
        [from_cv result1;from_cv result2;from_cv result3;from_cv result4;
         from_cv result5;from_cv result6;from_cv result7]) refs
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
  >> Cases_on `LENGTH q = 7`
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

Theorem registered_case10173_hist_program_run_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv center_program;from_cv box_program;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
         («radii»,from_cv radii);(«roots»,from_cv roots);
         («center_program»,from_cv center_program);
         («box_program»,from_cv box_program);(«stack»,from_cv stack)]
        registered_case10173_hist_program_run_body) refs
Proof
  strip_tac
  >> irule registered_case10173_compute_eval_literal_app7
  >> simp [registered_case10173_hist_program_run_lookup]
QED

Theorem registered_case10173_hist_program_run_center_nil_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv (Num center_nil);from_cv box_program;from_cv stack])
      (refs:hol_refs) =
    (M_success (from_cv stack),refs)
Proof
  strip_tac
  >> simp [registered_case10173_hist_program_run_unfold]
  >> simp
       [registered_case10173_hist_program_run_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_hist_program_run_box_nil_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv (Pair center_instruction center_program);
         from_cv (Num box_nil);from_cv stack]) (refs:hol_refs) =
    (M_success (from_cv stack),refs)
Proof
  strip_tac
  >> simp [registered_case10173_hist_program_run_unfold]
  >> simp
       [registered_case10173_hist_program_run_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_hist_program_run_cons_eval:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_step»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv center_instruction;from_cv box_instruction;from_cv stack])
      (refs:hol_refs) =
      (M_success (from_cv next_stack),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv center_program;from_cv box_program;from_cv next_stack]) refs =
      (M_success (from_cv final_stack),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv (Pair center_instruction center_program);
         from_cv (Pair box_instruction box_program);from_cv stack]) refs =
    (M_success (from_cv final_stack),refs)
Proof
  strip_tac
  >> simp [registered_case10173_hist_program_run_unfold]
  >> simp
       [registered_case10173_hist_program_run_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_case10173_hist_step»
          [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
           Uop Fst (Pair (from_cv center_instruction)
             (from_cv center_program));
           Uop Fst (Pair (from_cv box_instruction) (from_cv box_program));
           from_cv stack]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_case10173_hist_step»
          [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
           from_cv center_instruction;from_cv box_instruction;from_cv stack])
        refs` by
       (irule registered_case10173_compute_eval_app7_argument_results
        >> fs
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components,
              compute_execProofTheory.compute_eval_from_cv])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_case10173_hist_program_run»
          [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
           Uop Snd (from_cv (Pair center_instruction center_program));
           Uop Snd (from_cv (Pair box_instruction box_program));
           App «candle_cv_case10173_hist_step»
             [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
              Uop Fst (from_cv (Pair center_instruction center_program));
              Uop Fst (from_cv (Pair box_instruction box_program));
              from_cv stack]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_case10173_hist_program_run»
          [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
           from_cv center_program;from_cv box_program;from_cv next_stack]) refs` by
        (irule registered_case10173_compute_eval_app7_argument_results
        >> fs
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components,
              compute_execProofTheory.compute_eval_from_cv])
  >> fs []
QED

val _ = export_theory ();
