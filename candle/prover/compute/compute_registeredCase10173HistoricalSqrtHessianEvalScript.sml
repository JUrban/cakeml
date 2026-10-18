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

Definition registered_case10173_sqrt_hessian_entry_rows_decimal_def:
  registered_case10173_sqrt_hessian_entry_rows_decimal derivative
      logarithmic_derivative gradient hessian_rows rowindex colindex =
    case bounded_interval64_mul_decimal logarithmic_derivative
      (EL rowindex gradient) of
    | NONE => NONE
    | SOME scaled_row =>
      case bounded_interval64_mul_decimal
        (EL colindex gradient) scaled_row of
      | NONE => NONE
      | SOME outer =>
        case bounded_interval64_add outer
          (EL colindex (EL rowindex hessian_rows)) of
        | NONE => NONE
        | SOME inside => bounded_interval64_mul_decimal derivative inside
End

Theorem registered_case10173_fs_hist_sqrt_hessian_entry_rows_typed_eval:
  rowindex < 6 /\
  colindex < 6 /\
  LENGTH gradient = 6 /\
  LENGTH hessian_rows = 6 /\
  EVERY (\row. LENGTH row = 6) hessian_rows /\
  registered_case10173_sqrt_hessian_entry_rows_decimal derivative
      logarithmic_derivative gradient hessian_rows rowindex colindex =
    SOME result /\
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
  rw [registered_case10173_sqrt_hessian_entry_rows_decimal_def]
  >> every_case_tac
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_sqrt_hessian_entry_typed_eval)
  >> simp []
  >> gvs [EVERY_EL]
QED

Definition registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal_def:
  registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal derivative
      logarithmic_derivative gradient hessian_rows rowindex colindex =
    if colindex < rowindex then
      registered_case10173_sqrt_hessian_entry_rows_decimal derivative
        logarithmic_derivative gradient hessian_rows colindex rowindex
    else
      registered_case10173_sqrt_hessian_entry_rows_decimal derivative
        logarithmic_derivative gradient hessian_rows rowindex colindex
End

Definition registered_case10173_fs_hist_sqrt_hessian_symmetric_entry_body_def:
  registered_case10173_fs_hist_sqrt_hessian_symmetric_entry_body =
    If (Binop Less (Var «colindex») (Var «rowindex»))
      (App «candle_cv_fs_hist_sqrt_hessian_entry»
        [Var «colindex»;Var «rowindex»;Var «derivative_value»;
         Var «logarithmic_derivative»;Var «input_gradient»;
         Var «input_hessian»])
      (App «candle_cv_fs_hist_sqrt_hessian_entry»
        [Var «rowindex»;Var «colindex»;Var «derivative_value»;
         Var «logarithmic_derivative»;Var «input_gradient»;
         Var «input_hessian»])
End

Theorem registered_case10173_fs_hist_sqrt_hessian_symmetric_entry_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_sqrt_hessian_symmetric_entry» =
    SOME
      ([«rowindex»;«colindex»;«derivative_value»;
        «logarithmic_derivative»;«input_gradient»;«input_hessian»],
       registered_case10173_fs_hist_sqrt_hessian_symmetric_entry_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_sqrt_hessian_symmetric_entry_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_sqrt_hessian_symmetric_entry»
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
        registered_case10173_fs_hist_sqrt_hessian_symmetric_entry_body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_sqrt_hessian_symmetric_entry_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_hist_sqrt_hessian_symmetric_entry_typed_eval:
  rowindex < 6 /\
  colindex < 6 /\
  LENGTH gradient = 6 /\
  LENGTH hessian_rows = 6 /\
  EVERY (\row. LENGTH row = 6) hessian_rows /\
  registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal derivative
      logarithmic_derivative gradient hessian_rows rowindex colindex =
    SOME result /\
  21 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_sqrt_hessian_symmetric_entry»
        [from_cv (Num rowindex);from_cv (Num colindex);
         from_cv (bounded_interval64_object_cv derivative);
         from_cv (bounded_interval64_object_cv logarithmic_derivative);
         from_cv (bounded_interval64_object_cv_list gradient);
         from_cv (bounded_interval64_object_cv_matrix hessian_rows)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_sqrt_hessian_symmetric_entry_unfold]
  >> simp
       [registered_case10173_fs_hist_sqrt_hessian_symmetric_entry_body_def,
        compute_evalTheory.subst_def]
  >> Cases_on `colindex < rowindex`
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (Binop Less (Num colindex) (Num rowindex)) refs =
        (M_success (Num 1),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_evalTheory.do_binop_def,
          compute_evalTheory.do_reln_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_sqrt_hessian_entry_rows_typed_eval)
      >> fs
           [registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal_def]
      )
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (Binop Less (Num colindex) (Num rowindex)) refs =
      (M_success (Num 0),refs)` by
     simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_reln_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_sqrt_hessian_entry_rows_typed_eval)
  >> fs
       [registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal_def]
QED

Definition registered_case10173_sqrt_hessian_row_rows_decimal_def:
  registered_case10173_sqrt_hessian_row_rows_decimal derivative
      logarithmic_derivative gradient hessian_rows rowindex =
    case registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
      derivative logarithmic_derivative gradient hessian_rows rowindex 0 of
    | NONE => NONE
    | SOME r0 =>
      case registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
        derivative logarithmic_derivative gradient hessian_rows rowindex 1 of
      | NONE => NONE
      | SOME r1 =>
        case registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
          derivative logarithmic_derivative gradient hessian_rows rowindex 2 of
        | NONE => NONE
        | SOME r2 =>
          case registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
            derivative logarithmic_derivative gradient hessian_rows rowindex 3 of
          | NONE => NONE
          | SOME r3 =>
            case registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
              derivative logarithmic_derivative gradient hessian_rows rowindex 4 of
            | NONE => NONE
            | SOME r4 =>
              case registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
                derivative logarithmic_derivative gradient hessian_rows rowindex 5 of
              | NONE => NONE
              | SOME r5 => SOME [r0;r1;r2;r3;r4;r5]
End

Definition registered_case10173_fs_hist_sqrt_hessian_row_body_def:
  registered_case10173_fs_hist_sqrt_hessian_row_body =
    App «candle_cv_fs_angle_six»
      [App «candle_cv_fs_hist_sqrt_hessian_symmetric_entry»
         [Var «rowindex»;Num 0;Var «derivative_value»;
          Var «logarithmic_derivative»;Var «input_gradient»;
          Var «input_hessian»];
       App «candle_cv_fs_hist_sqrt_hessian_symmetric_entry»
         [Var «rowindex»;Num 1;Var «derivative_value»;
          Var «logarithmic_derivative»;Var «input_gradient»;
          Var «input_hessian»];
       App «candle_cv_fs_hist_sqrt_hessian_symmetric_entry»
         [Var «rowindex»;Num 2;Var «derivative_value»;
          Var «logarithmic_derivative»;Var «input_gradient»;
          Var «input_hessian»];
       App «candle_cv_fs_hist_sqrt_hessian_symmetric_entry»
         [Var «rowindex»;Num 3;Var «derivative_value»;
          Var «logarithmic_derivative»;Var «input_gradient»;
          Var «input_hessian»];
       App «candle_cv_fs_hist_sqrt_hessian_symmetric_entry»
         [Var «rowindex»;Num 4;Var «derivative_value»;
          Var «logarithmic_derivative»;Var «input_gradient»;
          Var «input_hessian»];
       App «candle_cv_fs_hist_sqrt_hessian_symmetric_entry»
         [Var «rowindex»;Num 5;Var «derivative_value»;
          Var «logarithmic_derivative»;Var «input_gradient»;
          Var «input_hessian»]]
End

Theorem registered_case10173_fs_hist_sqrt_hessian_row_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_sqrt_hessian_row» =
    SOME
      ([«rowindex»;«derivative_value»;«logarithmic_derivative»;
        «input_gradient»;«input_hessian»],
       registered_case10173_fs_hist_sqrt_hessian_row_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_sqrt_hessian_row_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_sqrt_hessian_row»
        [from_cv rowindex;from_cv derivative_value;
         from_cv logarithmic_derivative;from_cv input_gradient;
         from_cv input_hessian]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«rowindex»,from_cv rowindex);
         («derivative_value»,from_cv derivative_value);
         («logarithmic_derivative»,from_cv logarithmic_derivative);
         («input_gradient»,from_cv input_gradient);
         («input_hessian»,from_cv input_hessian)]
        registered_case10173_fs_hist_sqrt_hessian_row_body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_sqrt_hessian_row_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_hist_sqrt_hessian_row_typed_eval:
  rowindex < 6 /\
  LENGTH gradient = 6 /\
  LENGTH hessian_rows = 6 /\
  EVERY (\row. LENGTH row = 6) hessian_rows /\
  registered_case10173_sqrt_hessian_row_rows_decimal derivative
      logarithmic_derivative gradient hessian_rows rowindex = SOME result /\
  23 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_sqrt_hessian_row»
        [from_cv (Num rowindex);
         from_cv (bounded_interval64_object_cv derivative);
         from_cv (bounded_interval64_object_cv logarithmic_derivative);
         from_cv (bounded_interval64_object_cv_list gradient);
         from_cv (bounded_interval64_object_cv_matrix hessian_rows)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv_list result)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_sqrt_hessian_row_unfold]
  >> simp
       [registered_case10173_fs_hist_sqrt_hessian_row_body_def,
        compute_evalTheory.subst_def]
  >> Cases_on
       `registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
          derivative logarithmic_derivative gradient hessian_rows
          rowindex 0`
  >> gvs [registered_case10173_sqrt_hessian_row_rows_decimal_def]
  >> Cases_on
       `registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
          derivative logarithmic_derivative gradient hessian_rows
          rowindex 1`
  >> gvs []
  >> Cases_on
       `registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
          derivative logarithmic_derivative gradient hessian_rows
          rowindex 2`
  >> gvs []
  >> Cases_on
       `registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
          derivative logarithmic_derivative gradient hessian_rows
          rowindex 3`
  >> gvs []
  >> Cases_on
       `registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
          derivative logarithmic_derivative gradient hessian_rows
          rowindex 4`
  >> gvs []
  >> Cases_on
       `registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
          derivative logarithmic_derivative gradient hessian_rows
          rowindex 5`
  >> gvs []
  >> rename1
       `registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
          derivative logarithmic_derivative gradient hessian_rows
          rowindex 0 = SOME r0`
  >> rename1
       `registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
          derivative logarithmic_derivative gradient hessian_rows
          rowindex 1 = SOME r1`
  >> rename1
       `registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
          derivative logarithmic_derivative gradient hessian_rows
          rowindex 2 = SOME r2`
  >> rename1
       `registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
          derivative logarithmic_derivative gradient hessian_rows
          rowindex 3 = SOME r3`
  >> rename1
       `registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
          derivative logarithmic_derivative gradient hessian_rows
          rowindex 4 = SOME r4`
  >> rename1
       `registered_case10173_sqrt_hessian_symmetric_entry_rows_decimal
          derivative logarithmic_derivative gradient hessian_rows
          rowindex 5 = SOME r5`
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_six»
            [from_cv (bounded_interval64_object_cv r0);
             from_cv (bounded_interval64_object_cv r1);
             from_cv (bounded_interval64_object_cv r2);
             from_cv (bounded_interval64_object_cv r3);
             from_cv (bounded_interval64_object_cv r4);
             from_cv (bounded_interval64_object_cv r5)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_compute_eval_app6_argument_results
      >> simp []
      >> rpt conj_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_sqrt_hessian_symmetric_entry_typed_eval)
      >> fs []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
  >> irule
       (SIMP_RULE std_ss
         [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
          compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
