(*****************************************************************************
 * Complete evaluator refinement for the historical production guard.
 *
 * This theory composes the twelve source-level let bindings with the
 * authenticated guard predicates.  It remains packet independent: the next
 * layer extracts these premises from an arbitrary accepted decimal packet.
 *****************************************************************************)
Theory compute_registeredCase10173ProductionGuardFullEval
Ancestors
  compute_registeredCase10173ProductionGuardBindingEval
Libs
  bossLib preamble intLib

Definition registered_case10173_hist_production_guard_body_def:
  registered_case10173_hist_production_guard_body =
    Let «center_environment»
      (App «candle_cv_fs_interval_list_of_q»
        [App «candle_cv_q_center_environment_list» [Var «boxes»]])
      (Let «box_environment»
        (App «candle_cv_fs_interval_list_of_q» [Var «boxes»])
        (Let «center_root_delta»
          (App «candle_cv_fs_interval_lookup» [Num 0;Var «roots»])
          (Let «center_root_four_x0»
            (App «candle_cv_fs_interval_lookup» [Num 1;Var «roots»])
            (Let «box_root_delta»
              (App «candle_cv_fs_interval_lookup» [Num 2;Var «roots»])
              (Let «box_root_four_x0»
                (App «candle_cv_fs_interval_lookup» [Num 3;Var «roots»])
                (Let «center_u126»
                  (Uop Fst
                    (App «candle_cv_fs_hist_u126»
                      [Var «center_environment»]))
                  (Let «center_u135»
                    (Uop Fst
                      (App «candle_cv_fs_hist_u135»
                        [Var «center_environment»]))
                    (Let «box_u126»
                      (Uop Fst
                        (App «candle_cv_fs_hist_u126»
                          [Var «box_environment»]))
                      (Let «box_u135»
                        (Uop Fst
                          (App «candle_cv_fs_hist_u135»
                            [Var «box_environment»]))
                        (Let «center_quotient»
                          (App «candle_cv_fs_hist_quotient»
                            [App «candle_cv_fs_hist_delta_x4_value»
                               [Var «center_environment»];
                             Var «center_root_delta»;
                             Var «center_root_four_x0»])
                          (Let «box_quotient»
                            (App «candle_cv_fs_hist_quotient»
                              [App «candle_cv_fs_hist_second_value»
                                 [App «candle_cv_fs_hist_delta_x4_second»
                                    [Var «box_environment»]];
                               Var «box_root_delta»;
                               Var «box_root_four_x0»])
                            registered_case10173_hist_production_guard_checks_body)))))))))))
End

Theorem registered_case10173_hist_production_guard_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_case10173_hist_production_guard» =
    SOME
      ([«boxes»;«roots»],
       registered_case10173_hist_production_guard_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_production_guard_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_production_guard»
        [from_cv boxes;from_cv roots]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«boxes»,from_cv boxes);(«roots»,from_cv roots)]
        registered_case10173_hist_production_guard_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_hist_production_guard_lookup]
QED

Theorem registered_case10173_hist_root_lookup_0_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [Num 0;
         from_cv
           (bounded_interval64_object_cv_list
             [r0;r1;r2;r3])])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv r0)),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE (srw_ss()) []
         (Q.SPECL
           [`0`,`[r0;r1;r2;r3]`,`clock`,`refs`]
           compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_fs_interval_lookup_num_object_list_eval))
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_hist_root_lookup_1_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [Num 1;
         from_cv
           (bounded_interval64_object_cv_list
             [r0;r1;r2;r3])])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv r1)),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE (srw_ss()) []
         (Q.SPECL
           [`1`,`[r0;r1;r2;r3]`,`clock`,`refs`]
           compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_fs_interval_lookup_num_object_list_eval))
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_hist_root_lookup_2_eval:
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [Num 2;
         from_cv
           (bounded_interval64_object_cv_list
             [r0;r1;r2;r3])])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv r2)),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE (srw_ss()) []
         (Q.SPECL
           [`2`,`[r0;r1;r2;r3]`,`clock`,`refs`]
           compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_fs_interval_lookup_num_object_list_eval))
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_hist_root_lookup_3_eval:
  5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [Num 3;
         from_cv
           (bounded_interval64_object_cv_list
             [r0;r1;r2;r3])])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv r3)),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE (srw_ss()) []
         (Q.SPECL
           [`3`,`[r0;r1;r2;r3]`,`clock`,`refs`]
           compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_fs_interval_lookup_num_object_list_eval))
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_hist_production_guard_typed_eval:
  registered_case10173_q_center_environment_positive boxes =
      SOME center_boxes /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME [cx0;cx1;cx2;cx3;cx4;cx5] /\
  bounded_object_positive_q_interval64_decimal_list boxes =
      SOME [bx0;bx1;bx2;bx3;bx4;bx5] /\
  bounded_historical_u126_decimal [cx0;cx1;cx2;cx3;cx4;cx5] =
      SOME (center_u126,center_u126_gradient) /\
  bounded_historical_u135_decimal [cx0;cx1;cx2;cx3;cx4;cx5] =
      SOME (center_u135,center_u135_gradient) /\
  bounded_historical_u126_decimal [bx0;bx1;bx2;bx3;bx4;bx5] =
      SOME (box_u126,box_u126_gradient) /\
  bounded_historical_u135_decimal [bx0;bx1;bx2;bx3;bx4;bx5] =
      SOME (box_u135,box_u135_gradient) /\
  bounded_historical_delta_x4_value_decimal
      [cx0;cx1;cx2;cx3;cx4;cx5] = SOME center_delta_x4 /\
  bounded_historical_delta_x4_second_decimal
      [bx0;bx1;bx2;bx3;bx4;bx5] =
      SOME (box_delta_x4,box_delta_x4_gradient,box_delta_x4_hessian) /\
  bounded_hessian64_rows box_delta_x4_hessian =
      SOME box_delta_x4_hessian_rows /\
  bounded_interval64_mul_decimal
      center_root_delta center_root_four_x0 = SOME center_product /\
  bounded_interval64_positive_inv_certificate_decimal
      center_product center_reciprocal /\
  bounded_interval64_mul_decimal
      (bounded_interval64_neg center_delta_x4) center_reciprocal =
      SOME center_quotient /\
  bounded_interval64_mul_decimal
      box_root_delta box_root_four_x0 = SOME box_product /\
  bounded_interval64_positive_inv_certificate_decimal
      box_product box_reciprocal /\
  bounded_interval64_mul_decimal
      (bounded_interval64_neg box_delta_x4) box_reciprocal =
      SOME box_quotient /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower center_root_delta) /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower center_root_four_x0) /\
  0 <
    (w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower center_root_delta)) *
     w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower center_root_four_x0))) DIV
      1000000000000 /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower box_root_delta) /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower box_root_four_x0) /\
  0 <
    (w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower box_root_delta)) *
     w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower box_root_four_x0))) DIV
      1000000000000 /\
  bounded_interval64_valid center_u126 /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower center_u126) /\
  bounded_interval64_valid center_u135 /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower center_u135) /\
  0 <
    (w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower center_u126)) *
     w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower center_u135))) DIV
      1000000000000 /\
  bounded_interval64_valid box_u126 /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower box_u126) /\
  bounded_interval64_valid box_u135 /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower box_u135) /\
  0 <
    (w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower box_u126)) *
     w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower box_u135))) DIV
      1000000000000 /\
  word_lo
    (bounded_signed64_magnitude
      (bounded_interval64_lower center_quotient))
    bounded_atan_scale_decimal /\
  word_lo
    (bounded_signed64_magnitude
      (bounded_interval64_upper center_quotient))
    bounded_atan_scale_decimal /\
  word_lo
    (bounded_signed64_magnitude
      (bounded_interval64_lower box_quotient))
    bounded_atan_scale_decimal /\
  word_lo
    (bounded_signed64_magnitude
      (bounded_interval64_upper box_quotient))
    bounded_atan_scale_decimal /\
  bounded_case10173_positive_environment
      [cx0;cx1;cx2;cx3;cx4;cx5] /\
  bounded_case10173_positive_environment
      [bx0;bx1;bx2;bx3;bx4;bx5] /\
  3000 +
      8 * (registered_case10173_center_list_length boxes + 1) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_production_guard»
        [from_cv boxes;
         from_cv
           (bounded_interval64_object_cv_list
             [center_root_delta;center_root_four_x0;
              box_root_delta;box_root_four_x0])])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_hist_production_guard_unfold]
  >> simp
       [registered_case10173_hist_production_guard_body_def,
        compute_registeredCase10173ProductionGuardCompositionEvalTheory.registered_case10173_hist_production_guard_checks_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv_list
            [cx0;cx1;cx2;cx3;cx4;cx5])`
  >> conj_tac
  >- (irule registered_case10173_hist_center_environment_binding_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv_list
            [bx0;bx1;bx2;bx3;bx4;bx5])`
  >> conj_tac
  >- (irule
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_interval_list_of_q_object_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv center_root_delta)`
  >> conj_tac
  >- (irule registered_case10173_hist_root_lookup_0_eval
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv center_root_four_x0)`
  >> conj_tac
  >- (irule registered_case10173_hist_root_lookup_1_eval
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv box_root_delta)`
  >> conj_tac
  >- (irule registered_case10173_hist_root_lookup_2_eval
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv box_root_four_x0)`
  >> conj_tac
  >- (irule registered_case10173_hist_root_lookup_3_eval
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv center_u126)`
  >> conj_tac
  >- (irule registered_case10173_hist_u126_value_binding_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv center_u135)`
  >> conj_tac
  >- (irule registered_case10173_hist_u135_value_binding_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv box_u126)`
  >> conj_tac
  >- (irule registered_case10173_hist_u126_value_binding_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv box_u135)`
  >> conj_tac
  >- (irule registered_case10173_hist_u135_value_binding_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv center_quotient)`
  >> conj_tac
  >- (irule registered_case10173_hist_quotient_binding_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `center_delta_x4`
      >> qexists_tac `center_product`
      >> qexists_tac `center_reciprocal`
      >> simp []
      >> irule
           compute_registeredCase10173HistoricalDeltaX4GeneralEvalTheory.registered_case10173_historical_delta_x4_value_environment_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv box_quotient)`
  >> conj_tac
  >- (irule registered_case10173_hist_quotient_binding_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `box_delta_x4`
      >> qexists_tac `box_product`
      >> qexists_tac `box_reciprocal`
      >> simp []
      >> irule registered_case10173_hist_delta_x4_second_value_binding_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE (srw_ss())
         [compute_registeredCase10173ProductionGuardCompositionEvalTheory.registered_case10173_hist_production_guard_checks_body_def,
          compute_evalTheory.subst_def,
          compute_execProofTheory.subst_from_cv]
         compute_registeredCase10173ProductionGuardCompositionEvalTheory.registered_case10173_hist_production_guard_checks_eval)
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
