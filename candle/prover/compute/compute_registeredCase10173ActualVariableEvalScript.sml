(*****************************************************************************
 * Registered evaluation of an actual completed coordinate variable.
 *
 * The source variable instruction performs Taylor completion before its
 * result reaches sqrt.  This theory connects the word-level recomputation in
 * the actual-operand contract to that unchanged registered source call.
 *****************************************************************************)
Theory compute_registeredCase10173ActualVariableEval
Ancestors
  compute_boundedCase10173ActualSqrtOperand
  compute_registeredCase10173ResultVariableEval
Libs
  bossLib preamble intLib

Theorem bounded_case10173_actual_interval64_nth_el:
  !values index.
    index < LENGTH values ==>
    bounded_interval64_nth values index = SOME (EL index values)
Proof
  Induct
  >> Cases_on `index`
  >> simp [compute_boundedTaylorBaseTheory.bounded_interval64_nth_def]
QED

Theorem registered_case10173_actual_variable_object_eval:
  LENGTH radii = 6 /\
  LENGTH dimensions = 6 /\
  variable < 6 /\
  zero_rows = REPLICATE 6 (REPLICATE 6 bounded_interval64_zero) /\
  bounded_hessian64_rows (bounded_interval64_zeros 21) = SOME zero_rows /\
  bounded_case10173_actual_variable_decimal radii dimensions variable =
    SOME result /\
  8192 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_variable»
        [from_cv (bounded_interval64_object_cv_list dimensions);
         from_cv (registered_case10173_word64_object_cv_list radii);
         Num variable])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_taylor64_rows_object_cv result zero_rows)),refs)
Proof
  strip_tac
  >> `bounded_interval64_nth dimensions variable =
        SOME (EL variable dimensions)` by
       (irule bounded_case10173_actual_interval64_nth_el
        >> simp [])
  >> `registered_case10173_interval_unit_decimal variable dimensions =
        THE (bounded_interval64_unit_vector_decimal variable)` by
       (irule
          compute_registeredCase10173PolynomialVariableEvalTheory.registered_case10173_interval_unit_decimal_six
        >> simp [])
  >> `bounded_taylor64_complete_decimal radii T
        (EL variable dimensions)
        (registered_case10173_interval_unit_decimal variable dimensions)
        (bounded_interval64_zeros 21) = SOME result` by
       (qpat_x_assum
          `bounded_case10173_actual_variable_decimal _ _ _ = SOME result`
          mp_tac
        >> rw
             [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_variable_decimal_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_object_fs_taylor_complete radii T
        (EL variable dimensions)
        (registered_case10173_interval_unit_decimal variable dimensions)
        (bounded_interval64_zeros 21) zero_rows =
      SOME (bounded_taylor64_rows_object_cv result zero_rows)` by
       (irule
          compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_taylor_complete_exact
        >> simp [])
  >> irule
       compute_registeredCase10173ResultVariableEvalTheory.registered_case10173_fs_result_variable_object_eval
  >> simp []
  >> conj_tac
  >- (fs
        [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_interval64_unit_vector_decimal_def]
      >> intLib.ARITH_TAC)
  >> metis_tac []
QED

val _ = export_theory ();
