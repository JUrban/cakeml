(*****************************************************************************
 * Source-exact registered evaluator composition for the historical
 * second-order dihedral calculation.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalSecondOrderEval
Ancestors
  compute_registeredCase10173HistoricalFinalHessianEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_second_order_body_def:
  registered_case10173_fs_hist_second_order_body =
    Let «delta_second»
      (App «candle_cv_fs_hist_delta_second» [Var «boxes»])
    (Let «root_delta»
      (App «candle_cv_fs_hist_second_sqrt_supplied»
        [Var «delta_second»;Var «root_delta_value»])
    (Let «root_delta_gradient»
      (App «candle_cv_fs_hist_second_gradient» [Var «root_delta»])
    (Let «root_delta_hessian»
      (App «candle_cv_fs_hist_second_hessian» [Var «root_delta»])
    (Let «delta_x4_second»
      (App «candle_cv_fs_hist_delta_x4_second» [Var «boxes»])
    (Let «delta_x4_value»
      (App «candle_cv_fs_hist_second_value» [Var «delta_x4_second»])
    (Let «delta_x4_gradient»
      (App «candle_cv_fs_hist_second_gradient» [Var «delta_x4_second»])
    (Let «delta_x4_hessian»
      (App «candle_cv_fs_hist_second_hessian» [Var «delta_x4_second»])
    (Let «u126»
      (App «candle_cv_fs_hist_u126» [Var «boxes»])
    (Let «u135»
      (App «candle_cv_fs_hist_u135» [Var «boxes»])
    (Let «b»
      (App «candle_cv_fs_angle_interval_mul»
        [Var «root_delta_value»;Var «root_four_x0»])
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
            [Var «root_delta_value»;Var «two_over_root_four_x0»]];
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
    (Let «x0»
      (App «candle_cv_fs_interval_lookup» [Num 0;Var «boxes»])
    (Let «b_hessian»
      (App «candle_cv_fs_hist_b_hessian»
        [Var «root_four_x0»;Var «root_delta_value»;
         Var «root_delta_gradient»;Var «root_delta_hessian»;
         Var «two_over_root_four_x0»;Var «x0»])
    (Let «c»
      (App «candle_cv_fs_hist_c_vector»
        [Var «delta_x4_value»;Var «b»;
         Var «delta_x4_gradient»;Var «b_gradient»])
    (Let «reciprocal_u126»
      (App «candle_cv_fs_hist_positive_inv» [Uop Fst (Var «u126»)])
    (Let «reciprocal_u135»
      (App «candle_cv_fs_hist_positive_inv» [Uop Fst (Var «u135»)])
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
            [Num 2;Var «root_delta_value»]]])
    (Let «gradient»
      (App «candle_cv_fs_hist_replace_three»
        [Var «gradient_base»;Var «special_gradient»])
    (Let «log_u_gradient»
      (App «candle_cv_fs_hist_log_u_gradient»
        [Uop Snd (Var «u126»);Var «reciprocal_u126»;
         Uop Snd (Var «u135»);Var «reciprocal_u135»])
    (Let «hessian»
      (App «candle_cv_fs_hist_final_hessian»
        [Var «b»;Var «delta_x4_value»;Var «delta_x4_gradient»;
         Var «delta_x4_hessian»;Var «b_gradient»;Var «b_hessian»;
         Var «reciprocal_u»;Var «gradient»;Var «log_u_gradient»])
    (Let «quotient»
      (App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_interval_neg» [Var «delta_x4_value»];
         App «candle_cv_fs_hist_positive_inv» [Var «b»]])
    (Let «value»
      (App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_interval_of_q»
          [App «candle_cv_q_pi_half_interval» []];
         App «candle_cv_fs_hist_atan_interval» [Var «quotient»]])
      (App «candle_cv_fs_hist_second_make»
        [Var «value»;Var «gradient»;Var «hessian»])))))))))))))))))))))))))))
End

Theorem registered_case10173_fs_hist_second_order_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_second_order» =
    SOME
      ([«boxes»;«root_delta_value»;«root_four_x0»],
       registered_case10173_fs_hist_second_order_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_second_order_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_order»
        [from_cv boxes;from_cv root_delta_value;from_cv root_four_x0])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«boxes»,from_cv boxes);
         («root_delta_value»,from_cv root_delta_value);
         («root_four_x0»,from_cv root_four_x0)]
        registered_case10173_fs_hist_second_order_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanConstantEvalTheory.registered_case10173_hist_compute_eval_literal_app3
  >> simp [registered_case10173_fs_hist_second_order_lookup]
QED

fun registered_case10173_second_order_let_tac result =
  irule
    compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac result
  >> conj_tac >- (fs [] >> intLib.ARITH_TAC);

Theorem registered_case10173_fs_hist_second_order_composition_eval:
  ! (boxes:cv) (root_delta_value:cv) (root_four_x0:cv)
    (delta_second:cv) (root_delta:cv) (root_delta_gradient:cv)
    (root_delta_hessian:cv) (delta_x4_second:cv) (delta_x4_value:cv)
    (delta_x4_gradient:cv) (delta_x4_hessian:cv) (u126:cv) (u135:cv)
    (b:cv) (two_over_root_four_x0:cv) (b_gradient_base:cv)
    (b_gradient:cv) (x0:cv) (b_hessian:cv) (c:cv)
    (reciprocal_u126:cv) (reciprocal_u135:cv) (reciprocal_u:cv)
    (gradient_base:cv) (special_gradient:cv) (gradient:cv)
    (log_u_gradient:cv) (hessian:cv) (quotient:cv) (value:cv).
  28 < clock /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_second» [from_cv boxes])
      (refs:hol_refs) =
    (M_success (from_cv delta_second),refs) /\
  compute_eval (clock - 2) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_sqrt_supplied»
        [from_cv delta_second;from_cv root_delta_value]) refs =
    (M_success (from_cv root_delta),refs) /\
  compute_eval (clock - 3) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_gradient» [from_cv root_delta]) refs =
    (M_success (from_cv root_delta_gradient),refs) /\
  compute_eval (clock - 4) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_hessian» [from_cv root_delta]) refs =
    (M_success (from_cv root_delta_hessian),refs) /\
  compute_eval (clock - 5) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_second» [from_cv boxes]) refs =
    (M_success (from_cv delta_x4_second),refs) /\
  compute_eval (clock - 6) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_value» [from_cv delta_x4_second]) refs =
    (M_success (from_cv delta_x4_value),refs) /\
  compute_eval (clock - 7) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_gradient» [from_cv delta_x4_second]) refs =
    (M_success (from_cv delta_x4_gradient),refs) /\
  compute_eval (clock - 8) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_hessian» [from_cv delta_x4_second]) refs =
    (M_success (from_cv delta_x4_hessian),refs) /\
  compute_eval (clock - 9) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u126» [from_cv boxes]) refs =
    (M_success (from_cv u126),refs) /\
  compute_eval (clock - 10) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u135» [from_cv boxes]) refs =
    (M_success (from_cv u135),refs) /\
  compute_eval (clock - 11) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [from_cv root_delta_value;from_cv root_four_x0]) refs =
    (M_success (from_cv b),refs) /\
  compute_eval (clock - 12) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_angle_interval_scale»
          [Num 2;App «candle_cv_fs_interval_one» []];
         App «candle_cv_fs_hist_positive_inv»
          [from_cv root_four_x0]]) refs =
    (M_success (from_cv two_over_root_four_x0),refs) /\
  compute_eval (clock - 13) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_list_scale»
        [from_cv root_four_x0;from_cv root_delta_gradient]) refs =
    (M_success (from_cv b_gradient_base),refs) /\
  compute_eval (clock - 14) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_six»
        [App «candle_cv_fs_interval_add»
          [App «candle_cv_fs_interval_lookup»
            [Num 0;from_cv b_gradient_base];
           App «candle_cv_fs_angle_interval_mul»
            [from_cv root_delta_value;from_cv two_over_root_four_x0]];
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
  compute_eval (clock - 15) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup» [Num 0;from_cv boxes]) refs =
    (M_success (from_cv x0),refs) /\
  compute_eval (clock - 16) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_b_hessian»
        [from_cv root_four_x0;from_cv root_delta_value;
         from_cv root_delta_gradient;from_cv root_delta_hessian;
         from_cv two_over_root_four_x0;from_cv x0]) refs =
    (M_success (from_cv b_hessian),refs) /\
  compute_eval (clock - 17) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_c_vector»
        [from_cv delta_x4_value;from_cv b;
         from_cv delta_x4_gradient;from_cv b_gradient]) refs =
    (M_success (from_cv c),refs) /\
  compute_eval (clock - 18) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_inv» [Uop Fst (from_cv u126)]) refs =
    (M_success (from_cv reciprocal_u126),refs) /\
  compute_eval (clock - 19) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_inv» [Uop Fst (from_cv u135)]) refs =
    (M_success (from_cv reciprocal_u135),refs) /\
  compute_eval (clock - 20) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_inv»
        [App «candle_cv_fs_angle_interval_mul»
          [Uop Fst (from_cv u126);Uop Fst (from_cv u135)]]) refs =
    (M_success (from_cv reciprocal_u),refs) /\
  compute_eval (clock - 21) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_list_scale»
        [from_cv reciprocal_u;from_cv c]) refs =
    (M_success (from_cv gradient_base),refs) /\
  compute_eval (clock - 22) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [from_cv root_four_x0;
         App «candle_cv_fs_hist_positive_inv»
          [App «candle_cv_fs_angle_interval_scale»
            [Num 2;from_cv root_delta_value]]]) refs =
    (M_success (from_cv special_gradient),refs) /\
  compute_eval (clock - 23) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_replace_three»
        [from_cv gradient_base;from_cv special_gradient]) refs =
    (M_success (from_cv gradient),refs) /\
  compute_eval (clock - 24) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_log_u_gradient»
        [Uop Snd (from_cv u126);from_cv reciprocal_u126;
         Uop Snd (from_cv u135);from_cv reciprocal_u135]) refs =
    (M_success (from_cv log_u_gradient),refs) /\
  compute_eval (clock - 25) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_final_hessian»
        [from_cv b;from_cv delta_x4_value;from_cv delta_x4_gradient;
         from_cv delta_x4_hessian;from_cv b_gradient;from_cv b_hessian;
         from_cv reciprocal_u;from_cv gradient;from_cv log_u_gradient]) refs =
    (M_success (from_cv hessian),refs) /\
  compute_eval (clock - 26) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_interval_neg» [from_cv delta_x4_value];
         App «candle_cv_fs_hist_positive_inv» [from_cv b]]) refs =
    (M_success (from_cv quotient),refs) /\
  compute_eval (clock - 27) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_interval_of_q»
          [App «candle_cv_q_pi_half_interval» []];
         App «candle_cv_fs_hist_atan_interval» [from_cv quotient]]) refs =
    (M_success (from_cv value),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_order»
        [from_cv boxes;from_cv root_delta_value;from_cv root_four_x0]) refs =
    (M_success
      (from_cv (Pair value (Pair gradient hessian) : cv)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_second_order_unfold]
  >> simp
       [registered_case10173_fs_hist_second_order_body_def,
        compute_evalTheory.subst_def]
  >> registered_case10173_second_order_let_tac `from_cv delta_second`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv root_delta`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv root_delta_gradient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv root_delta_hessian`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv delta_x4_second`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv delta_x4_value`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv delta_x4_gradient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv delta_x4_hessian`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv u126`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv u135`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv b`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac
       `from_cv two_over_root_four_x0`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv b_gradient_base`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv b_gradient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv x0`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv b_hessian`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv c`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv reciprocal_u126`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv reciprocal_u135`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv reciprocal_u`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv gradient_base`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv special_gradient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv gradient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv log_u_gradient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv hessian`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv quotient`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_second_order_let_tac `from_cv value`
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalSecondOrderPrimitiveEvalTheory.registered_case10173_fs_hist_second_make_eval)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
