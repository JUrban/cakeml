(*****************************************************************************
 * Registered source refinement for the historical square-root Hessian.
 *
 * The source operates on the native full six-by-six matrix, while the typed
 * numerical checker stores only the 21 upper-triangular entries.  This theory
 * first verifies the literal full-matrix execution.  A later refinement uses
 * bounded_hessian64_rows to connect that result to the compact checker state.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalSqrtHessianEval
Ancestors
  compute_registeredCase10173HistoricalSecondOrderPrimitiveEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_sqrt_hessian_entry_body_def:
  registered_case10173_fs_hist_sqrt_hessian_entry_body =
    Let «scaled_row»
      (App «candle_cv_fs_angle_interval_mul»
        [Var «logarithmic_derivative»;
         App «candle_cv_fs_interval_lookup»
           [Var «rowindex»;Var «input_gradient»]])
      (Let «inside»
        (App «candle_cv_fs_interval_add»
          [App «candle_cv_fs_angle_interval_mul»
            [App «candle_cv_fs_interval_lookup»
               [Var «colindex»;Var «input_gradient»];
             Var «scaled_row»];
           App «candle_cv_fs_angle_matrix_lookup»
             [Var «rowindex»;Var «colindex»;Var «input_hessian»]])
        (App «candle_cv_fs_angle_interval_mul»
          [Var «derivative_value»;Var «inside»]))
End

Theorem registered_case10173_fs_hist_sqrt_hessian_entry_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_sqrt_hessian_entry» =
    SOME
      ([«rowindex»;«colindex»;«derivative_value»;
        «logarithmic_derivative»;«input_gradient»;«input_hessian»],
       registered_case10173_fs_hist_sqrt_hessian_entry_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_sqrt_hessian_entry_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_sqrt_hessian_entry»
        [from_cv rowindex;from_cv colindex;from_cv derivative_value;
         from_cv logarithmic_derivative;from_cv input_gradient;
         from_cv input_hessian]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«rowindex»,from_cv rowindex);
         («colindex»,from_cv colindex);
         («derivative_value»,from_cv derivative_value);
         («logarithmic_derivative»,from_cv logarithmic_derivative);
         («input_gradient»,from_cv input_gradient);
         («input_hessian»,from_cv input_hessian)]
        registered_case10173_fs_hist_sqrt_hessian_entry_body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_sqrt_hessian_entry_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_hist_sqrt_hessian_entry_typed_eval:
  rowindex < 6 /\
  colindex < 6 /\
  rowindex < LENGTH gradient /\
  colindex < LENGTH gradient /\
  rowindex < LENGTH hessian_rows /\
  colindex < LENGTH (EL rowindex hessian_rows) /\
  bounded_interval64_mul_decimal logarithmic_derivative
      (EL rowindex gradient) = SOME scaled_row /\
  bounded_interval64_mul_decimal
      (EL colindex gradient) scaled_row = SOME outer /\
  bounded_interval64_add outer
      (EL colindex (EL rowindex hessian_rows)) = SOME inside /\
  bounded_interval64_mul_decimal derivative inside = SOME result /\
  20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_sqrt_hessian_entry»
        [from_cv (Num rowindex);from_cv (Num colindex);
         from_cv (bounded_interval64_object_cv derivative);
         from_cv (bounded_interval64_object_cv logarithmic_derivative);
         from_cv (bounded_interval64_object_cv_list gradient);
         from_cv (bounded_interval64_object_cv_matrix hessian_rows)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_sqrt_hessian_entry_unfold]
  >> simp
       [registered_case10173_fs_hist_sqrt_hessian_entry_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv scaled_row)`
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_mul»
            [from_cv (bounded_interval64_object_cv logarithmic_derivative);
             App «candle_cv_fs_interval_lookup»
               [Num rowindex;
                from_cv (bounded_interval64_object_cv_list gradient)]]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_mul»
            [from_cv (bounded_interval64_object_cv logarithmic_derivative);
             from_cv
               (bounded_interval64_object_cv (EL rowindex gradient))]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp [compute_execProofTheory.compute_eval_from_cv]
        >> irule
             (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
               compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval)
        >> simp []
        >> intLib.ARITH_TAC)
      >> rw []
      >> irule
           compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
      >> simp
           [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv inside)`
  >> conj_tac
  >- (`bounded_object_fs_interval_mul_decimal
          (bounded_interval64_object_cv (EL colindex gradient))
          (bounded_interval64_object_cv scaled_row) =
        SOME (bounded_interval64_object_cv outer)` by
       metis_tac
         [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact]
      >> `bounded_object_fs_interval_add
          (bounded_interval64_object_cv outer)
          (bounded_interval64_object_cv
            (EL colindex (EL rowindex hessian_rows))) =
        SOME (bounded_interval64_object_cv inside)` by
       metis_tac
         [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact]
      >> `compute_eval (clock - 2)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_mul»
            [App «candle_cv_fs_interval_lookup»
               [Num colindex;
                from_cv (bounded_interval64_object_cv_list gradient)];
             from_cv (bounded_interval64_object_cv scaled_row)]) refs =
        (M_success (from_cv (bounded_interval64_object_cv outer)),refs)` by
       (`compute_eval (clock - 2)
            registered_case10173_historical_chunk16_ceqs
            (App «candle_cv_fs_angle_interval_mul»
              [App «candle_cv_fs_interval_lookup»
                 [Num colindex;
                  from_cv (bounded_interval64_object_cv_list gradient)];
               from_cv (bounded_interval64_object_cv scaled_row)]) refs =
          compute_eval (clock - 2)
            registered_case10173_historical_chunk16_ceqs
            (App «candle_cv_fs_angle_interval_mul»
              [from_cv
                 (bounded_interval64_object_cv (EL colindex gradient));
               from_cv (bounded_interval64_object_cv scaled_row)]) refs` by
         (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
          >> simp [compute_execProofTheory.compute_eval_from_cv]
          >> irule
               (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                 compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval)
          >> simp []
          >> intLib.ARITH_TAC)
        >> rw []
        >> irule
             compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
        >> simp []
        >> intLib.ARITH_TAC)
      >> `compute_eval (clock - 2)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_matrix_lookup»
            [Num rowindex;Num colindex;
             from_cv (bounded_interval64_object_cv_matrix hessian_rows)]) refs =
        (M_success
          (from_cv
            (bounded_interval64_object_cv
              (EL colindex (EL rowindex hessian_rows)))),refs)` by
       (irule
          (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
            compute_registeredCase10173HistoricalSecondOrderPrimitiveEvalTheory.registered_case10173_fs_angle_matrix_lookup_typed_eval)
        >> simp []
        >> intLib.ARITH_TAC)
      >> `compute_eval (clock - 2)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_add»
            [App «candle_cv_fs_angle_interval_mul»
               [App «candle_cv_fs_interval_lookup»
                  [Num colindex;
                   from_cv (bounded_interval64_object_cv_list gradient)];
                from_cv (bounded_interval64_object_cv scaled_row)];
             App «candle_cv_fs_angle_matrix_lookup»
               [Num rowindex;Num colindex;
                from_cv
                  (bounded_interval64_object_cv_matrix hessian_rows)]]) refs =
        compute_eval (clock - 2)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_add»
            [from_cv (bounded_interval64_object_cv outer);
             from_cv
               (bounded_interval64_object_cv
                 (EL colindex (EL rowindex hessian_rows)))]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp [])
      >> rw []
      >> irule
           compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_add_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
  >> simp
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
