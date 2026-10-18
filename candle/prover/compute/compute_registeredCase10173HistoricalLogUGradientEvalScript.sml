(*****************************************************************************
 * Registered-source refinement for the historical logarithmic-u gradient.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalLogUGradientEval
Ancestors
  compute_registeredCase10173HistoricalBHessianEval
Libs
  bossLib preamble intLib

Definition registered_case10173_log_u_gradient_entry_decimal_def:
  registered_case10173_log_u_gradient_entry_decimal u126_gradient
      reciprocal_u126 u135_gradient reciprocal_u135 coordinate =
    case bounded_interval64_mul_decimal
      (EL coordinate u126_gradient) reciprocal_u126 of
    | NONE => NONE
    | SOME logarithmic_126 =>
      case bounded_interval64_mul_decimal
        (EL coordinate u135_gradient) reciprocal_u135 of
      | NONE => NONE
      | SOME logarithmic_135 =>
          bounded_interval64_add logarithmic_126 logarithmic_135
End

Definition registered_case10173_fs_hist_log_u_gradient_entry_body_def:
  registered_case10173_fs_hist_log_u_gradient_entry_body =
    App «candle_cv_fs_interval_add»
      [App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_interval_lookup»
          [Var «coordinate»;Var «u126_gradient»];
         Var «reciprocal_u126»];
       App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_interval_lookup»
          [Var «coordinate»;Var «u135_gradient»];
         Var «reciprocal_u135»]]
End

Theorem registered_case10173_fs_hist_log_u_gradient_entry_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_log_u_gradient_entry» =
    SOME
      ([«coordinate»;«u126_gradient»;«reciprocal_u126»;
        «u135_gradient»;«reciprocal_u135»],
       registered_case10173_fs_hist_log_u_gradient_entry_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_log_u_gradient_entry_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_log_u_gradient_entry»
        [from_cv coordinate;from_cv u126_gradient;
         from_cv reciprocal_u126;from_cv u135_gradient;
         from_cv reciprocal_u135]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«coordinate»,from_cv coordinate);
         («u126_gradient»,from_cv u126_gradient);
         («reciprocal_u126»,from_cv reciprocal_u126);
         («u135_gradient»,from_cv u135_gradient);
         («reciprocal_u135»,from_cv reciprocal_u135)]
        registered_case10173_fs_hist_log_u_gradient_entry_body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_log_u_gradient_entry_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_hist_log_u_gradient_entry_typed_eval:
  coordinate < 6 /\
  LENGTH u126_gradient = 6 /\
  LENGTH u135_gradient = 6 /\
  registered_case10173_log_u_gradient_entry_decimal u126_gradient
    reciprocal_u126 u135_gradient reciprocal_u135 coordinate = SOME result /\
  22 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_log_u_gradient_entry»
        [from_cv (Num coordinate);
         from_cv (bounded_interval64_object_cv_list u126_gradient);
         from_cv (bounded_interval64_object_cv reciprocal_u126);
         from_cv (bounded_interval64_object_cv_list u135_gradient);
         from_cv (bounded_interval64_object_cv reciprocal_u135)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_log_u_gradient_entry_unfold]
  >> simp
       [registered_case10173_fs_hist_log_u_gradient_entry_body_def,
        compute_evalTheory.subst_def]
  >> Cases_on
       `bounded_interval64_mul_decimal
          (EL coordinate u126_gradient) reciprocal_u126`
  >> gvs [registered_case10173_log_u_gradient_entry_decimal_def]
  >> Cases_on
       `bounded_interval64_mul_decimal
          (EL coordinate u135_gradient) reciprocal_u135`
  >> gvs []
  >> rename1
       `bounded_interval64_mul_decimal
          (EL coordinate u126_gradient) reciprocal_u126 =
        SOME logarithmic_126`
  >> rename1
       `bounded_interval64_mul_decimal
          (EL coordinate u135_gradient) reciprocal_u135 =
        SOME logarithmic_135`
  >> irule
       compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_interval_add_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv logarithmic_126`
  >> qexists_tac `bounded_interval64_object_cv logarithmic_135`
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact]
  >> conj_tac
  >> irule registered_case10173_fs_hist_gradient_correction_typed_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_log_u_gradient_decimal_def:
  registered_case10173_log_u_gradient_decimal u126_gradient reciprocal_u126
      u135_gradient reciprocal_u135 =
    case registered_case10173_log_u_gradient_entry_decimal u126_gradient
      reciprocal_u126 u135_gradient reciprocal_u135 0 of
    | NONE => NONE
    | SOME r0 =>
      case registered_case10173_log_u_gradient_entry_decimal u126_gradient
        reciprocal_u126 u135_gradient reciprocal_u135 1 of
      | NONE => NONE
      | SOME r1 =>
        case registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 2 of
        | NONE => NONE
        | SOME r2 =>
          case registered_case10173_log_u_gradient_entry_decimal u126_gradient
            reciprocal_u126 u135_gradient reciprocal_u135 3 of
          | NONE => NONE
          | SOME r3 =>
            case registered_case10173_log_u_gradient_entry_decimal u126_gradient
              reciprocal_u126 u135_gradient reciprocal_u135 4 of
            | NONE => NONE
            | SOME r4 =>
              case registered_case10173_log_u_gradient_entry_decimal u126_gradient
                reciprocal_u126 u135_gradient reciprocal_u135 5 of
              | NONE => NONE
              | SOME r5 => SOME [r0;r1;r2;r3;r4;r5]
End

Definition registered_case10173_fs_hist_log_u_gradient_body_def:
  registered_case10173_fs_hist_log_u_gradient_body =
    App «candle_cv_fs_angle_six»
      [App «candle_cv_fs_hist_log_u_gradient_entry»
        [Num 0;Var «u126_gradient»;Var «reciprocal_u126»;
         Var «u135_gradient»;Var «reciprocal_u135»];
       App «candle_cv_fs_hist_log_u_gradient_entry»
        [Num 1;Var «u126_gradient»;Var «reciprocal_u126»;
         Var «u135_gradient»;Var «reciprocal_u135»];
       App «candle_cv_fs_hist_log_u_gradient_entry»
        [Num 2;Var «u126_gradient»;Var «reciprocal_u126»;
         Var «u135_gradient»;Var «reciprocal_u135»];
       App «candle_cv_fs_hist_log_u_gradient_entry»
        [Num 3;Var «u126_gradient»;Var «reciprocal_u126»;
         Var «u135_gradient»;Var «reciprocal_u135»];
       App «candle_cv_fs_hist_log_u_gradient_entry»
        [Num 4;Var «u126_gradient»;Var «reciprocal_u126»;
         Var «u135_gradient»;Var «reciprocal_u135»];
       App «candle_cv_fs_hist_log_u_gradient_entry»
        [Num 5;Var «u126_gradient»;Var «reciprocal_u126»;
         Var «u135_gradient»;Var «reciprocal_u135»]]
End

Theorem registered_case10173_fs_hist_log_u_gradient_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_log_u_gradient» =
    SOME
      ([«u126_gradient»;«reciprocal_u126»;
        «u135_gradient»;«reciprocal_u135»],
       registered_case10173_fs_hist_log_u_gradient_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_log_u_gradient_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_log_u_gradient»
        [from_cv u126_gradient;from_cv reciprocal_u126;
         from_cv u135_gradient;from_cv reciprocal_u135]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«u126_gradient»,from_cv u126_gradient);
         («reciprocal_u126»,from_cv reciprocal_u126);
         («u135_gradient»,from_cv u135_gradient);
         («reciprocal_u135»,from_cv reciprocal_u135)]
        registered_case10173_fs_hist_log_u_gradient_body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_log_u_gradient_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_hist_log_u_gradient_typed_eval:
  LENGTH u126_gradient = 6 /\
  LENGTH u135_gradient = 6 /\
  registered_case10173_log_u_gradient_decimal u126_gradient reciprocal_u126
    u135_gradient reciprocal_u135 = SOME result /\
  24 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_log_u_gradient»
        [from_cv (bounded_interval64_object_cv_list u126_gradient);
         from_cv (bounded_interval64_object_cv reciprocal_u126);
         from_cv (bounded_interval64_object_cv_list u135_gradient);
         from_cv (bounded_interval64_object_cv reciprocal_u135)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv_list result)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_log_u_gradient_unfold]
  >> simp
       [registered_case10173_fs_hist_log_u_gradient_body_def,
        compute_evalTheory.subst_def]
  >> Cases_on
       `registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 0`
  >> gvs [registered_case10173_log_u_gradient_decimal_def]
  >> Cases_on
       `registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 1`
  >> gvs []
  >> Cases_on
       `registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 2`
  >> gvs []
  >> Cases_on
       `registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 3`
  >> gvs []
  >> Cases_on
       `registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 4`
  >> gvs []
  >> Cases_on
       `registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 5`
  >> gvs []
  >> rename1
       `registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 0 = SOME r0`
  >> rename1
       `registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 1 = SOME r1`
  >> rename1
       `registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 2 = SOME r2`
  >> rename1
       `registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 3 = SOME r3`
  >> rename1
       `registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 4 = SOME r4`
  >> rename1
       `registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 5 = SOME r5`
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
             registered_case10173_fs_hist_log_u_gradient_entry_typed_eval)
      >> simp []
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
