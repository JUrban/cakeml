(*****************************************************************************
 * Registered evaluator control semantics for one paired historical program
 * instruction.  The unique synchronized opcode 10 delegates to the historical
 * dihedral item; every ordinary synchronized instruction delegates to the
 * existing fixed/nonlinear stack step.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10HistStepEval
Ancestors
  compute_registeredCase10173HistoricalChunk16Tag10Data
  compute_registeredCase10173HistProgramRunEval
Libs
  bossLib preamble

Definition registered_case10173_tag10_hist_step_body_def:
  registered_case10173_tag10_hist_step_body =
    If (Binop Eq (Var «center_instruction») (Num 10))
      (If (Binop Eq (Var «box_instruction») (Num 10))
        (Pair
          (App «candle_cv_case10173_hist_item»
            [Var «center_boxes»;Var «boxes»;Var «radii»;Var «roots»])
          (Var «stack»))
        (Pair
          (App «candle_cv_fsa_item_default»
            [Var «center_boxes»;Var «boxes»])
          (Var «stack»)))
      (If (Binop Eq (Var «box_instruction») (Num 10))
        (Pair
          (App «candle_cv_fsa_item_default»
            [Var «center_boxes»;Var «boxes»])
          (Var «stack»))
        (App «candle_cv_fso_program_step_fixed_nonlinear»
          [Var «center_boxes»;Var «boxes»;Var «radii»;
           Var «center_instruction»;Var «box_instruction»;
           Var «stack»]))
End

Theorem registered_case10173_tag10_hist_step_lookup:
  ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs
      «candle_cv_case10173_hist_step» =
    SOME
      ([«center_boxes»;«boxes»;«radii»;«roots»;
        «center_instruction»;«box_instruction»;«stack»],
       registered_case10173_tag10_hist_step_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_tag10_hist_step_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_step»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv center_instruction;from_cv box_instruction;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
         («radii»,from_cv radii);(«roots»,from_cv roots);
         («center_instruction»,from_cv center_instruction);
         («box_instruction»,from_cv box_instruction);
         («stack»,from_cv stack)]
        registered_case10173_tag10_hist_step_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_compute_eval_literal_app7
  >> simp [registered_case10173_tag10_hist_step_lookup]
QED

Theorem registered_case10173_tag10_compute_eval_if_zero:
  compute_eval clock ceqs condition (refs:hol_refs) =
      (M_success (Num 0),refs) ==>
  compute_eval clock ceqs (If condition yes_branch no_branch) refs =
    compute_eval clock ceqs no_branch refs
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_hist_step_special_eval_from_item:
  0 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_item»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots])
      (refs:hol_refs) =
      (M_success (from_cv item),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_step»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv (Num 10);from_cv (Num 10);from_cv stack]) refs =
    (M_success (from_cv (Pair item stack)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_tag10_hist_step_unfold]
  >> simp
       [registered_case10173_tag10_hist_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (Binop Eq (Num 10) (Num 10)) refs =
      (M_success (Num 1),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_evalTheory.do_binop_def,
          compute_evalTheory.do_eq_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_hist_step_ordinary_eval_from_step:
  0 < clock /\
  center_instruction <> Num 10 /\ box_instruction <> Num 10 /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv center_instruction;from_cv box_instruction;from_cv stack])
      (refs:hol_refs) =
      (M_success (from_cv next_stack),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_step»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv center_instruction;from_cv box_instruction;from_cv stack])
      refs =
    (M_success (from_cv next_stack),refs)
Proof
  strip_tac
  >> simp [registered_case10173_tag10_hist_step_unfold]
  >> simp
       [registered_case10173_tag10_hist_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> `from_cv center_instruction <> (Num 10:compute_exp)` by
       metis_tac
         [compute_execProofTheory.from_cv_11,
          compute_execTheory.from_cv_def]
  >> `from_cv box_instruction <> (Num 10:compute_exp)` by
       metis_tac
         [compute_execProofTheory.from_cv_11,
          compute_execTheory.from_cv_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (Binop Eq (from_cv center_instruction) (Num 10)) refs =
      (M_success (Num 0),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_binop_def,
          compute_evalTheory.do_eq_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (Binop Eq (from_cv box_instruction) (Num 10)) refs =
      (M_success (Num 0),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_binop_def,
          compute_evalTheory.do_eq_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> simp [registered_case10173_tag10_compute_eval_if_zero]
QED

val _ = export_theory ();
