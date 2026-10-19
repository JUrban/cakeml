(*****************************************************************************
 * Registered evaluator refinement for polynomial coordinate results.
 *
 * A source variable instruction looks up one center interval, constructs its
 * unit gradient and full zero Hessian, and immediately performs Taylor
 * completion.  This theory packages those four exact source computations as
 * one checked object result, without evaluating a closed polynomial program.
 *****************************************************************************)
Theory compute_registeredCase10173ResultVariableEval
Ancestors
  compute_registeredCase10173PolynomialVariableEval
  compute_registeredCase10173TaylorCompleteObjectEval
  compute_registeredCase10173HistoricalCombinatorEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_result_variable_body_def:
  registered_case10173_fs_result_variable_body =
    App «candle_cv_fs_result_complete_rounded»
      [Var «radii»;
       Num 1;
       App «candle_cv_fs_first_make»
         [App «candle_cv_fs_interval_lookup»
            [Var «variable»;Var «dimensions»];
          App «candle_cv_fs_interval_unit»
            [Var «variable»;Var «dimensions»]];
       App «candle_cv_fs_interval_zero_matrix»
         [Var «dimensions»;Var «dimensions»]]
End

Theorem registered_case10173_fs_result_variable_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_variable» =
    SOME
      ([«dimensions»;«radii»;«variable»],
       registered_case10173_fs_result_variable_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_variable_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_variable»
        [from_cv dimensions;from_cv radii;from_cv variable])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («variable»,from_cv variable)]
        registered_case10173_fs_result_variable_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_fs_result_variable_lookup]
QED

Theorem registered_case10173_fs_result_variable_num_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_variable»
        [from_cv dimensions;from_cv radii;Num variable])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («variable»,Num variable)]
        registered_case10173_fs_result_variable_body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        registered_case10173_fs_result_variable_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_fs_result_variable_center_eval:
  variable < LENGTH dimensions /\
  variable + 2 < clock /\
  8 * (LENGTH dimensions + 1) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_make»
        [App «candle_cv_fs_interval_lookup»
           [Num variable;
            from_cv (bounded_interval64_object_cv_list dimensions)];
         App «candle_cv_fs_interval_unit»
           [Num variable;
            from_cv (bounded_interval64_object_cv_list dimensions)]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (bounded_interval64_object_cv (EL variable dimensions))
          (bounded_interval64_object_cv_list
            (registered_case10173_interval_unit_decimal
              variable dimensions)))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_first_make»
            [from_cv
               (bounded_interval64_object_cv (EL variable dimensions));
             from_cv
               (bounded_interval64_object_cv_list
                 (registered_case10173_interval_unit_decimal
                   variable dimensions))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule
            compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_fs_interval_lookup_num_object_list_eval
          >> simp [])
      >> irule
           compute_registeredCase10173PolynomialVariableEvalTheory.registered_case10173_fs_interval_unit_object_eval
      >> simp [])
  >> irule
       compute_registeredCase10173HistoricalBasicEvalTheory.registered_case10173_fs_first_make_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_result_variable_object_eval:
  variable < LENGTH dimensions /\
  zero_rows =
    REPLICATE (LENGTH dimensions)
      (REPLICATE (LENGTH dimensions) bounded_interval64_zero) /\
  bounded_hessian64_rows (bounded_interval64_zeros 21) =
    SOME zero_rows /\
  bounded_object_fs_taylor_complete radii T
      (EL variable dimensions)
      (registered_case10173_interval_unit_decimal variable dimensions)
      (bounded_interval64_zeros 21) zero_rows = SOME result /\
  2 < clock /\
  variable + 2 < clock - 1 /\
  8 * (LENGTH dimensions + 1) < clock - 1 /\
  4 * (2 * LENGTH dimensions + 2) < clock - 1 /\
  256 *
      (2 * LENGTH radii + LENGTH zero_rows +
       LENGTH
         (registered_case10173_interval_unit_decimal
           variable dimensions) + 2) < clock - 1 ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_variable»
        [from_cv (bounded_interval64_object_cv_list dimensions);
         from_cv (registered_case10173_word64_object_cv_list radii);
         Num variable])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> simp
       [registered_case10173_fs_result_variable_num_unfold,
        registered_case10173_fs_result_variable_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_complete_rounded»
            [from_cv
               (registered_case10173_word64_object_cv_list radii);
             from_cv (bounded_bool_object_cv T);
             from_cv
               (Pair
                 (bounded_interval64_object_cv (EL variable dimensions))
                 (bounded_interval64_object_cv_list
                   (registered_case10173_interval_unit_decimal
                     variable dimensions)));
             from_cv (bounded_interval64_object_cv_matrix zero_rows)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- simp [compute_execProofTheory.compute_eval_from_cv]
      >> conj_tac
      >- (simp_tac std_ss
            [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def,
             compute_execTheory.from_cv_def]
          >> ACCEPT_TAC
               (SIMP_RULE std_ss
                 [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def,
                  compute_execTheory.from_cv_def]
                 (SPECL
                   [``(Num 1:cv)``,``(refs:hol_refs)``,
                    ``(clock - 1:num)``,
                    ``registered_case10173_historical_chunk16_ceqs``]
                   compute_execProofTheory.compute_eval_from_cv)))
      >> conj_tac
      >- (irule registered_case10173_fs_result_variable_center_eval
          >> simp [])
      >> rw []
      >> irule
           compute_registeredCase10173PolynomialShapeEvalTheory.registered_case10173_fs_interval_zero_matrix_object_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173TaylorCompleteObjectEvalTheory.registered_case10173_fs_result_complete_rounded_object_eval
  >> asm_rewrite_tac []
  >> qexists_tac `bounded_interval64_zeros 21`
  >> metis_tac []
QED

val _ = export_theory ();
