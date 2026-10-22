(*****************************************************************************
 * Source-exact registered evaluator composition for the historical
 * first-order dihedral calculation.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalFirstOrderEval
Ancestors
  compute_registeredCase10173HistoricalDeltaCenterEval
  compute_registeredCase10173HistoricalCVectorEval
  compute_registeredCase10173HistoricalAtanIntervalEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_first_order_body_def:
  registered_case10173_fs_hist_first_order_body =
    Let «delta»
      (App «candle_cv_fs_angle_delta_value» [Var «environment»])
    (Let «delta_gradient»
      (App «candle_cv_fs_angle_delta_gradient» [Var «environment»])
    (Let «root_delta_d»
      (App «candle_cv_fs_hist_positive_inv»
        [App «candle_cv_fs_angle_interval_scale»
          [Num 2;Var «root_delta»]])
    (Let «root_delta_gradient»
      (App «candle_cv_fsn_interval_list_scale»
        [Var «root_delta_d»;Var «delta_gradient»])
    (Let «delta_x4_value»
      (App «candle_cv_fs_hist_delta_x4_value» [Var «environment»])
    (Let «delta_x4_gradient»
      (App «candle_cv_fs_hist_delta_x4_gradient» [Var «environment»])
    (Let «u126»
      (App «candle_cv_fs_hist_u126» [Var «environment»])
    (Let «u135»
      (App «candle_cv_fs_hist_u135» [Var «environment»])
    (Let «b»
      (App «candle_cv_fs_angle_interval_mul»
        [Var «root_delta»;Var «root_four_x0»])
    (Let «two_over_root_four_x0»
      (App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_angle_interval_scale»
          [Num 2;App «candle_cv_fs_interval_one» []];
         App «candle_cv_fs_hist_positive_inv» [Var «root_four_x0»]])
    (Let «b_gradient_base»
      (App «candle_cv_fsn_interval_list_scale»
        [Var «root_four_x0»;Var «root_delta_gradient»])
    (Let «b_gradient»
      (App «candle_cv_fs_angle_six»
        [App «candle_cv_fs_interval_add»
          [App «candle_cv_fs_interval_lookup»
            [Num 0;Var «b_gradient_base»];
           App «candle_cv_fs_angle_interval_mul»
            [Var «root_delta»;Var «two_over_root_four_x0»]];
         App «candle_cv_fs_interval_lookup»
          [Num 1;Var «b_gradient_base»];
         App «candle_cv_fs_interval_lookup»
          [Num 2;Var «b_gradient_base»];
         App «candle_cv_fs_interval_lookup»
          [Num 3;Var «b_gradient_base»];
         App «candle_cv_fs_interval_lookup»
          [Num 4;Var «b_gradient_base»];
         App «candle_cv_fs_interval_lookup»
          [Num 5;Var «b_gradient_base»]])
    (Let «c»
      (App «candle_cv_fs_hist_c_vector»
        [Var «delta_x4_value»;Var «b»;
         Var «delta_x4_gradient»;Var «b_gradient»])
    (Let «reciprocal_u»
      (App «candle_cv_fs_hist_positive_inv»
        [App «candle_cv_fs_angle_interval_mul»
          [Uop Fst (Var «u126»);Uop Fst (Var «u135»)]])
    (Let «gradient_base»
      (App «candle_cv_fsn_interval_list_scale»
        [Var «reciprocal_u»;Var «c»])
    (Let «special_gradient»
      (App «candle_cv_fs_angle_interval_mul»
        [Var «root_four_x0»;
         App «candle_cv_fs_hist_positive_inv»
          [App «candle_cv_fs_angle_interval_scale»
            [Num 2;Var «root_delta»]]])
    (Let «gradient»
      (App «candle_cv_fs_hist_replace_three»
        [Var «gradient_base»;Var «special_gradient»])
    (Let «quotient»
      (App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_interval_neg» [Var «delta_x4_value»];
         App «candle_cv_fs_hist_positive_inv» [Var «b»]])
    (Let «value»
      (App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_interval_of_q»
          [App «candle_cv_q_pi_half_interval» []];
         App «candle_cv_fs_hist_atan_interval» [Var «quotient»]])
      (App «candle_cv_fs_first_make»
        [Var «value»;Var «gradient»])))))))))))))))))))
End

Theorem registered_case10173_fs_hist_first_order_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_first_order» =
    SOME
      ([«environment»;«root_delta»;«root_four_x0»],
       registered_case10173_fs_hist_first_order_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_first_order_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_first_order»
        [from_cv environment;from_cv root_delta;from_cv root_four_x0])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«environment»,from_cv environment);
         («root_delta»,from_cv root_delta);
         («root_four_x0»,from_cv root_four_x0)]
        registered_case10173_fs_hist_first_order_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanConstantEvalTheory.registered_case10173_hist_compute_eval_literal_app3
  >> simp [registered_case10173_fs_hist_first_order_lookup]
QED

fun registered_case10173_first_order_let_tac result =
  irule
    compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac result
  >> conj_tac >- (fs [] >> intLib.ARITH_TAC);

Theorem registered_case10173_fs_hist_first_order_composition_eval:
  ! (environment:cv) (root_delta:cv) (root_four_x0:cv)
    (delta_value_result:cv) (delta_gradient:cv) (root_delta_d:cv)
    (root_delta_gradient:cv) (delta_x4_value:cv)
    (delta_x4_gradient:cv) (u126:cv) (u135:cv) (b:cv)
    (two_over_root_four_x0:cv) (b_gradient_base:cv)
    (b_gradient:cv) (c:cv) (reciprocal_u:cv) (gradient_base:cv)
    (special_gradient:cv) (gradient:cv) (quotient:cv) (value:cv).
  20 < clock /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_value» [from_cv environment])
      (refs:hol_refs) =
    (M_success (from_cv delta_value_result),refs) /\
  compute_eval (clock - 2) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_gradient» [from_cv environment]) refs =
    (M_success (from_cv delta_gradient),refs) /\
  compute_eval (clock - 3) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_inv»
        [App «candle_cv_fs_angle_interval_scale»
          [Num 2;from_cv root_delta]]) refs =
    (M_success (from_cv root_delta_d),refs) /\
  compute_eval (clock - 4) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_list_scale»
        [from_cv root_delta_d;from_cv delta_gradient]) refs =
    (M_success (from_cv root_delta_gradient),refs) /\
  compute_eval (clock - 5) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_value» [from_cv environment]) refs =
    (M_success (from_cv delta_x4_value),refs) /\
  compute_eval (clock - 6) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_gradient» [from_cv environment]) refs =
    (M_success (from_cv delta_x4_gradient),refs) /\
  compute_eval (clock - 7) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u126» [from_cv environment]) refs =
    (M_success (from_cv u126),refs) /\
  compute_eval (clock - 8) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u135» [from_cv environment]) refs =
    (M_success (from_cv u135),refs) /\
  compute_eval (clock - 9) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [from_cv root_delta;from_cv root_four_x0]) refs =
    (M_success (from_cv b),refs) /\
  compute_eval (clock - 10) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_angle_interval_scale»
          [Num 2;App «candle_cv_fs_interval_one» []];
         App «candle_cv_fs_hist_positive_inv»
          [from_cv root_four_x0]]) refs =
    (M_success (from_cv two_over_root_four_x0),refs) /\
  compute_eval (clock - 11) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_list_scale»
        [from_cv root_four_x0;from_cv root_delta_gradient]) refs =
    (M_success (from_cv b_gradient_base),refs) /\
  compute_eval (clock - 12) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_six»
        [App «candle_cv_fs_interval_add»
          [App «candle_cv_fs_interval_lookup»
            [Num 0;from_cv b_gradient_base];
           App «candle_cv_fs_angle_interval_mul»
            [from_cv root_delta;from_cv two_over_root_four_x0]];
         App «candle_cv_fs_interval_lookup»
          [Num 1;from_cv b_gradient_base];
         App «candle_cv_fs_interval_lookup»
          [Num 2;from_cv b_gradient_base];
         App «candle_cv_fs_interval_lookup»
          [Num 3;from_cv b_gradient_base];
         App «candle_cv_fs_interval_lookup»
          [Num 4;from_cv b_gradient_base];
         App «candle_cv_fs_interval_lookup»
          [Num 5;from_cv b_gradient_base]]) refs =
    (M_success (from_cv b_gradient),refs) /\
  compute_eval (clock - 13) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_c_vector»
        [from_cv delta_x4_value;from_cv b;
         from_cv delta_x4_gradient;from_cv b_gradient]) refs =
    (M_success (from_cv c),refs) /\
  compute_eval (clock - 14) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_inv»
        [App «candle_cv_fs_angle_interval_mul»
          [Uop Fst (from_cv u126);Uop Fst (from_cv u135)]]) refs =
    (M_success (from_cv reciprocal_u),refs) /\
  compute_eval (clock - 15) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_list_scale»
        [from_cv reciprocal_u;from_cv c]) refs =
    (M_success (from_cv gradient_base),refs) /\
  compute_eval (clock - 16) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [from_cv root_four_x0;
         App «candle_cv_fs_hist_positive_inv»
          [App «candle_cv_fs_angle_interval_scale»
            [Num 2;from_cv root_delta]]]) refs =
    (M_success (from_cv special_gradient),refs) /\
  compute_eval (clock - 17) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_replace_three»
        [from_cv gradient_base;from_cv special_gradient]) refs =
    (M_success (from_cv gradient),refs) /\
  compute_eval (clock - 18) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_interval_neg» [from_cv delta_x4_value];
         App «candle_cv_fs_hist_positive_inv» [from_cv b]]) refs =
    (M_success (from_cv quotient),refs) /\
  compute_eval (clock - 19) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_interval_of_q»
          [App «candle_cv_q_pi_half_interval» []];
         App «candle_cv_fs_hist_atan_interval» [from_cv quotient]]) refs =
    (M_success (from_cv value),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_first_order»
        [from_cv environment;from_cv root_delta;from_cv root_four_x0]) refs =
    (M_success (from_cv (Pair value gradient)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_first_order_unfold]
  >> simp
       [registered_case10173_fs_hist_first_order_body_def,
        compute_evalTheory.subst_def]
  >> registered_case10173_first_order_let_tac `from_cv delta_value_result`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv delta_gradient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv root_delta_d`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv root_delta_gradient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv delta_x4_value`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv delta_x4_gradient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv u126`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv u135`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv b`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac
       `from_cv two_over_root_four_x0`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv b_gradient_base`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv b_gradient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv c`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv reciprocal_u`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv gradient_base`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv special_gradient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv gradient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv quotient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_first_order_let_tac `from_cv value`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalBasicEvalTheory.registered_case10173_fs_first_make_eval)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
