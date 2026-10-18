(*****************************************************************************
 * Registered-source refinement for the historical logarithmic-u gradient.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalLogUGradientEval
Ancestors
  compute_registeredCase10173HistoricalBHessianEval
Libs
  bossLib preamble intLib

(* The registered historical source writes the gradient factor before the
 * reciprocal, while the compact semantic trace uses list-scale and hence
 * writes the reciprocal first.  Establish exact algorithmic commutativity,
 * including directed rounding and the mixed-sign endpoint selection, rather
 * than treating the two source orders as an informal arithmetic identity. *)
Theorem registered_case10173_word_mul_div_floor_decimal_comm:
  bounded_word64_mul_div_floor_decimal left right =
    bounded_word64_mul_div_floor_decimal right left
Proof
  simp
    [compute_boundedTheory.bounded_word64_mul_div_floor_decimal_def,
     wordsTheory.WORD_MULT_COMM, arithmeticTheory.MULT_COMM]
QED

Theorem registered_case10173_word_mul_div_ceil_decimal_comm:
  bounded_word64_mul_div_ceil_decimal left right =
    bounded_word64_mul_div_ceil_decimal right left
Proof
  simp
    [compute_boundedTheory.bounded_word64_mul_div_ceil_decimal_def,
     wordsTheory.WORD_MULT_COMM, arithmeticTheory.MULT_COMM]
QED

Theorem registered_case10173_signed_mul_floor_decimal_comm:
  bounded_signed_word64_mul_floor_decimal left right =
    bounded_signed_word64_mul_floor_decimal right left
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp
       [compute_boundedSignedTheory.bounded_signed_word64_mul_floor_decimal_def,
        registered_case10173_word_mul_div_floor_decimal_comm,
        registered_case10173_word_mul_div_ceil_decimal_comm, EQ_SYM_EQ]
QED

Theorem registered_case10173_signed_mul_ceil_decimal_comm:
  bounded_signed_word64_mul_ceil_decimal left right =
    bounded_signed_word64_mul_ceil_decimal right left
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp
       [compute_boundedSignedTheory.bounded_signed_word64_mul_ceil_decimal_def,
        registered_case10173_word_mul_div_floor_decimal_comm,
        registered_case10173_word_mul_div_ceil_decimal_comm, EQ_SYM_EQ]
QED

Theorem registered_case10173_scaled_mul_floor_decimal_comm:
  bounded_scaled_mul_floor64_decimal left right =
    bounded_scaled_mul_floor64_decimal right left
Proof
  simp
    [compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_def,
     registered_case10173_signed_mul_floor_decimal_comm]
QED

Theorem registered_case10173_scaled_mul_ceil_decimal_comm:
  bounded_scaled_mul_ceil64_decimal left right =
    bounded_scaled_mul_ceil64_decimal right left
Proof
  simp
    [compute_boundedIntervalDecimalTheory.bounded_scaled_mul_ceil64_decimal_def,
     registered_case10173_signed_mul_ceil_decimal_comm]
QED

Theorem registered_case10173_product_from_pairs_decimal_comm:
  bounded_interval64_product_from_pairs_decimal ll rl lu ru =
    bounded_interval64_product_from_pairs_decimal rl ll ru lu
Proof
  simp
    [compute_boundedIntervalDecimalTheory.bounded_interval64_product_from_pairs_decimal_def,
     registered_case10173_scaled_mul_floor_decimal_comm,
     registered_case10173_scaled_mul_ceil_decimal_comm]
QED

Theorem registered_case10173_signed64_min_comm_normalized:
  bounded_signed64_normalized left /\
  bounded_signed64_normalized right ==>
  bounded_signed64_min left right = bounded_signed64_min right left
Proof
  strip_tac
  >> Cases_on `bounded_signed64_le left right`
  >> Cases_on `bounded_signed64_le right left`
  >> fs [compute_boundedSignedEndpointTheory.bounded_signed64_min_def]
  >> metis_tac
       [compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedObjectDecimalIntervalTheory.bounded_signed64_to_int_injective_normalized,
        integerTheory.INT_LE_TOTAL, integerTheory.INT_LE_ANTISYM]
QED

Theorem registered_case10173_product_mixed_decimal_comm:
  bounded_interval64_product_mixed_decimal ll lu rl ru =
    bounded_interval64_product_mixed_decimal rl ru ll lu
Proof
  simp
    [compute_boundedIntervalDecimalTheory.bounded_interval64_product_mixed_decimal_def,
     registered_case10173_scaled_mul_floor_decimal_comm,
     registered_case10173_scaled_mul_ceil_decimal_comm]
  >> Cases_on `bounded_scaled_mul_floor64_decimal ll ru`
  >> Cases_on `bounded_scaled_mul_floor64_decimal lu rl`
  >> simp []
  >> imp_res_tac
       compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_normalized
  >> simp [registered_case10173_signed64_min_comm_normalized]
QED

Theorem registered_case10173_interval_mul_decimal_comm:
  bounded_interval64_mul_decimal left right =
    bounded_interval64_mul_decimal right left
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp
       [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_decimal_def,
        compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def,
        registered_case10173_product_from_pairs_decimal_comm,
        registered_case10173_product_mixed_decimal_comm, CONJ_COMM]
  >> Cases_on `bounded_signed64_nonnegative b`
  >> Cases_on `bounded_signed64_nonpositive b0`
  >> Cases_on `bounded_signed64_nonnegative b'`
  >> Cases_on `bounded_signed64_nonpositive b0'`
  >> simp
       [registered_case10173_product_from_pairs_decimal_comm,
        registered_case10173_product_mixed_decimal_comm]
QED

Theorem registered_case10173_list_scale_decimal_el:
  !values result index.
    bounded_interval64_list_scale_decimal scalar values = SOME result /\
    index < LENGTH values ==>
    bounded_interval64_mul_decimal scalar (EL index values) =
      SOME (EL index result)
Proof
  Induct
  >> rw
       [compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_def]
  >> Cases_on `index`
  >> BasicProvers.every_case_tac
  >> gvs []
  >> res_tac
QED

Theorem registered_case10173_list_add_el:
  !left right result index.
    bounded_interval64_list_add left right = SOME result /\
    index < LENGTH left ==>
    bounded_interval64_add (EL index left) (EL index right) =
      SOME (EL index result)
Proof
  Induct
  >> Cases_on `right`
  >> rw [compute_boundedIntervalListTheory.bounded_interval64_list_add_def]
  >> Cases_on `index`
  >> BasicProvers.every_case_tac
  >> gvs []
  >> res_tac
QED

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

Theorem registered_case10173_log_u_gradient_decimal_compact:
  LENGTH u126_gradient = 6 /\
  LENGTH u135_gradient = 6 /\
  bounded_interval64_list_scale_decimal reciprocal_u126 u126_gradient =
    SOME logarithmic_126 /\
  bounded_interval64_list_scale_decimal reciprocal_u135 u135_gradient =
    SOME logarithmic_135 /\
  bounded_interval64_list_add logarithmic_126 logarithmic_135 = SOME result ==>
  registered_case10173_log_u_gradient_decimal u126_gradient reciprocal_u126
    u135_gradient reciprocal_u135 = SOME result
Proof
  rpt strip_tac
  >> `LENGTH logarithmic_126 = 6` by
       metis_tac
         [compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_length]
  >> `LENGTH logarithmic_135 = 6` by
       metis_tac
         [compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_length]
  >> `LENGTH result = 6` by
       metis_tac
         [compute_boundedIntervalListTheory.bounded_interval64_list_add_length]
  >> `!coordinate. coordinate < 6 ==>
        registered_case10173_log_u_gradient_entry_decimal u126_gradient
          reciprocal_u126 u135_gradient reciprocal_u135 coordinate =
        SOME (EL coordinate result)` by
       (rpt strip_tac
        >> `bounded_interval64_mul_decimal reciprocal_u126
              (EL coordinate u126_gradient) =
            SOME (EL coordinate logarithmic_126)` by
             metis_tac [registered_case10173_list_scale_decimal_el]
        >> `bounded_interval64_mul_decimal reciprocal_u135
              (EL coordinate u135_gradient) =
            SOME (EL coordinate logarithmic_135)` by
             metis_tac [registered_case10173_list_scale_decimal_el]
        >> `bounded_interval64_add (EL coordinate logarithmic_126)
              (EL coordinate logarithmic_135) =
            SOME (EL coordinate result)` by
             metis_tac [registered_case10173_list_add_el]
        >> fs
             [registered_case10173_log_u_gradient_entry_decimal_def,
              registered_case10173_interval_mul_decimal_comm])
  >> fs [registered_case10173_log_u_gradient_decimal_def]
  >> fs [listTheory.LENGTH_EQ_NUM_compute]
QED

val _ = export_theory ();
