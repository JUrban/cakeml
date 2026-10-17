(*****************************************************************************
 * Registered evaluator for the constant historical delta_x4 Hessian.
 *
 * The literal source returns six rows, whereas the bounded numerical model
 * stores the symmetric Hessian in 21 entries.  This theory first proves the
 * exact registered source evaluator over its native six-by-six matrix.  The
 * subsequent typed refinement can therefore state the layout relation via
 * bounded_hessian64_rows instead of identifying the two representations.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaX4HessianEval
Ancestors
  compute_registeredCase10173HistoricalSecondOrderMatrixScaleEval
Libs
  bossLib preamble intLib

Definition registered_case10173_interval_one_cv_def:
  registered_case10173_interval_one_cv =
    Pair
      (Pair (Num 1000000000000) (Num 0))
      (Pair (Num 1000000000000) (Num 0))
End

Definition registered_case10173_fs_hist_delta_x4_hessian_body_def:
  registered_case10173_fs_hist_delta_x4_hessian_body =
    Let «zero_value»
      (App «candle_cv_fs_interval_zero» [])
      (Let «one_value»
        (App «candle_cv_fs_interval_one» [])
        (Let «negative_one»
          (App «candle_cv_fs_interval_neg» [Var «one_value»])
          (Let «negative_two»
            (App «candle_cv_fs_angle_interval_scale_neg_two»
              [Var «one_value»])
            (App «candle_cv_fs_angle_six»
              [App «candle_cv_fs_angle_six»
                 [Var «negative_two»;Var «one_value»;Var «one_value»;
                  Var «negative_two»;Var «one_value»;Var «one_value»];
               App «candle_cv_fs_angle_six»
                 [Var «one_value»;Var «zero_value»;Var «negative_one»;
                  Var «zero_value»;Var «one_value»;Var «zero_value»];
               App «candle_cv_fs_angle_six»
                 [Var «one_value»;Var «negative_one»;Var «zero_value»;
                  Var «zero_value»;Var «zero_value»;Var «one_value»];
               App «candle_cv_fs_angle_six»
                 [Var «negative_two»;Var «zero_value»;Var «zero_value»;
                  Var «zero_value»;Var «zero_value»;Var «zero_value»];
               App «candle_cv_fs_angle_six»
                 [Var «one_value»;Var «one_value»;Var «zero_value»;
                  Var «zero_value»;Var «zero_value»;Var «negative_one»];
               App «candle_cv_fs_angle_six»
                 [Var «one_value»;Var «zero_value»;Var «one_value»;
                  Var «zero_value»;Var «negative_one»;Var «zero_value»]]))))
End

Definition registered_case10173_fs_hist_delta_x4_hessian_object_def:
  registered_case10173_fs_hist_delta_x4_hessian_object =
    let zero_value = registered_case10173_interval_zero_cv in
    let one_value = registered_case10173_interval_one_cv in
    case bounded_object_fs_interval_neg one_value of
    | NONE => NONE
    | SOME negative_one =>
      case registered_case10173_fs_interval_scale_neg_two_object one_value of
      | NONE => NONE
      | SOME negative_two =>
        SOME
          (registered_case10173_cv_matrix
            [[negative_two;one_value;one_value;
              negative_two;one_value;one_value];
             [one_value;zero_value;negative_one;
              zero_value;one_value;zero_value];
             [one_value;negative_one;zero_value;
              zero_value;zero_value;one_value];
             [negative_two;zero_value;zero_value;
              zero_value;zero_value;zero_value];
             [one_value;one_value;zero_value;
              zero_value;zero_value;negative_one];
             [one_value;zero_value;one_value;
              zero_value;negative_one;zero_value]])
End

Theorem registered_case10173_fs_hist_delta_x4_hessian_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_delta_x4_hessian» =
    SOME ([],registered_case10173_fs_hist_delta_x4_hessian_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_delta_x4_hessian_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_hessian» []) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      registered_case10173_fs_hist_delta_x4_hessian_body refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_delta_x4_hessian_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_interval_zero_cv_typed:
  registered_case10173_interval_zero_cv =
    bounded_interval64_object_cv bounded_interval64_zero
Proof
  simp
    [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_interval_zero_cv_def,
     compute_boundedIntervalListTheory.bounded_interval64_zero_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
QED

Theorem registered_case10173_interval_one_cv_typed:
  registered_case10173_interval_one_cv =
    bounded_interval64_object_cv bounded_atan_one_decimal
Proof
  simp
    [registered_case10173_interval_one_cv_def,
     compute_boundedAtanDecimalTheory.bounded_atan_one_decimal_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
QED

Theorem registered_case10173_fs_hist_delta_x4_hessian_object_bounded:
  bounded_historical_delta_x4_hessian_decimal = SOME hessian /\
  bounded_hessian64_rows hessian = SOME rows ==>
  registered_case10173_fs_hist_delta_x4_hessian_object =
    SOME (bounded_interval64_object_cv_matrix rows)
Proof
  strip_tac
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_delta_x4_hessian_decimal_source_trace
  >> strip_tac
  >> `registered_case10173_fs_interval_raw_scale_object 2
        registered_case10173_interval_one_cv =
      SOME (bounded_interval64_object_cv two)` by
       metis_tac
         [registered_case10173_interval_one_cv_typed,
          compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_atan_one_scale2_object_exact]
  >> `registered_case10173_fs_interval_scale_neg_two_object
        registered_case10173_interval_one_cv =
      SOME
        (bounded_interval64_object_cv (bounded_interval64_neg two))` by
       simp
         [compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_interval_scale_neg_two_object_def,
          registered_case10173_interval_one_cv_typed,
          compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
  >> `bounded_object_fs_interval_neg
        registered_case10173_interval_one_cv =
      SOME
        (bounded_interval64_object_cv
          (bounded_interval64_neg bounded_atan_one_decimal))` by
       simp
         [registered_case10173_interval_one_cv_typed,
          compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
  >> gvs
       [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def,
        registered_case10173_fs_hist_delta_x4_hessian_object_def,
        registered_case10173_interval_zero_cv_typed,
        registered_case10173_interval_one_cv_typed]
  >> qpat_x_assum
       `SOME _ =
          registered_case10173_fs_interval_scale_neg_two_object _`
       (fn scale_neg_two => rw [GSYM scale_neg_two])
  >> once_rewrite_tac
       [GSYM
          compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_cv_matrix_map_bounded_interval64_object_cv]
  >> simp []
QED

Theorem registered_case10173_fs_hist_delta_x4_hessian_object_eval:
  registered_case10173_fs_hist_delta_x4_hessian_object = SOME result /\
  20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_hessian» []) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rw [registered_case10173_fs_hist_delta_x4_hessian_object_def]
  >> every_case_tac
  >> gvs []
  >> simp [registered_case10173_fs_hist_delta_x4_hessian_unfold]
  >> simp
       [registered_case10173_fs_hist_delta_x4_hessian_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv registered_case10173_interval_zero_cv`
  >> conj_tac
  >- (simp
        [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_interval_zero_cv_def,
         compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_zero_eval]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv registered_case10173_interval_one_cv`
  >> conj_tac
  >- (simp
        [registered_case10173_interval_one_cv_def,
         compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_one_eval]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x'`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 5)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_six»
            [from_cv
               (registered_case10173_cv_list
                 [x;registered_case10173_interval_one_cv;
                  registered_case10173_interval_one_cv;x;
                  registered_case10173_interval_one_cv;
                  registered_case10173_interval_one_cv]);
             from_cv
               (registered_case10173_cv_list
                 [registered_case10173_interval_one_cv;
                  registered_case10173_interval_zero_cv;x';
                  registered_case10173_interval_zero_cv;
                  registered_case10173_interval_one_cv;
                  registered_case10173_interval_zero_cv]);
             from_cv
               (registered_case10173_cv_list
                 [registered_case10173_interval_one_cv;x';
                  registered_case10173_interval_zero_cv;
                  registered_case10173_interval_zero_cv;
                  registered_case10173_interval_zero_cv;
                  registered_case10173_interval_one_cv]);
             from_cv
               (registered_case10173_cv_list
                 [x;registered_case10173_interval_zero_cv;
                  registered_case10173_interval_zero_cv;
                  registered_case10173_interval_zero_cv;
                  registered_case10173_interval_zero_cv;
                  registered_case10173_interval_zero_cv]);
             from_cv
               (registered_case10173_cv_list
                 [registered_case10173_interval_one_cv;
                  registered_case10173_interval_one_cv;
                  registered_case10173_interval_zero_cv;
                  registered_case10173_interval_zero_cv;
                  registered_case10173_interval_zero_cv;x']);
             from_cv
               (registered_case10173_cv_list
                 [registered_case10173_interval_one_cv;
                  registered_case10173_interval_zero_cv;
                  registered_case10173_interval_one_cv;
                  registered_case10173_interval_zero_cv;x';
                  registered_case10173_interval_zero_cv])]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_compute_eval_app6_argument_results
      >> simp []
      >> rpt conj_tac
      >> irule
           compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval
      >> intLib.ARITH_TAC)
  >> simp [registered_case10173_cv_matrix_def]
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_delta_x4_hessian_typed_eval:
  bounded_historical_delta_x4_hessian_decimal = SOME hessian /\
  bounded_hessian64_rows hessian = SOME rows /\
  20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_hessian» []) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_matrix rows)),refs)
Proof
  rpt strip_tac
  >> irule registered_case10173_fs_hist_delta_x4_hessian_object_eval
  >> conj_tac >- first_assum ACCEPT_TAC
  >> irule registered_case10173_fs_hist_delta_x4_hessian_object_bounded
  >> simp []
QED

val _ = export_theory ();
