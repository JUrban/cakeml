(*****************************************************************************
 * Registered-source refinement for the historical delta-gradient dispatcher
 * and its monotone box assembly.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaGradientBoxEval
Ancestors
  compute_registeredCase10173HistoricalDeltaGradientBlockEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_delta_gradient_component_block_body_def:
  registered_case10173_fs_hist_delta_gradient_component_block_body =
    If (Binop Eq (Var «coordinate») (Num 0))
      (App «candle_cv_fs_hist_delta_gradient_block_0» [Var «environment»])
      (If (Binop Eq (Var «coordinate») (Num 1))
        (App «candle_cv_fs_hist_delta_gradient_block_1» [Var «environment»])
        (If (Binop Eq (Var «coordinate») (Num 2))
          (App «candle_cv_fs_hist_delta_gradient_block_2» [Var «environment»])
          (If (Binop Eq (Var «coordinate») (Num 3))
            (App «candle_cv_fs_hist_delta_gradient_block_3» [Var «environment»])
            (If (Binop Eq (Var «coordinate») (Num 4))
              (App «candle_cv_fs_hist_delta_gradient_block_4» [Var «environment»])
              (App «candle_cv_fs_hist_delta_gradient_block_5» [Var «environment»])))))
End

Theorem registered_case10173_fs_hist_delta_gradient_component_block_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_delta_gradient_component_block» =
    SOME
      ([«coordinate»;«environment»],
       registered_case10173_fs_hist_delta_gradient_component_block_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_delta_gradient_component_block_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_gradient_component_block»
        [from_cv coordinate;from_cv environment]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«coordinate»,from_cv coordinate);
         («environment»,from_cv environment)]
        registered_case10173_fs_hist_delta_gradient_component_block_body)
      refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp
       [registered_case10173_fs_hist_delta_gradient_component_block_lookup]
QED

Theorem registered_case10173_fs_hist_delta_gradient_component_block0_typed_eval:
  bounded_historical_delta_gradient_component_decimal 0 environment =
      SOME result /\
  50 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_gradient_component_block»
        [from_cv (Num 0);
         from_cv (bounded_interval64_object_cv_list environment)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> simp
       [registered_case10173_fs_hist_delta_gradient_component_block_unfold]
  >> simp
       [registered_case10173_fs_hist_delta_gradient_component_block_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (Binop Eq (Num 0) (Num 0)) refs =
      (M_success (Num 1),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_evalTheory.do_binop_def,
          compute_evalTheory.do_eq_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success]
  >> irule
       compute_registeredCase10173HistoricalDeltaGradientBlockEvalTheory.registered_case10173_fs_hist_delta_gradient_block0_typed_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_compute_eval_num_eq:
  compute_eval clock ceqs (Binop Eq (Num left) (Num right))
      (refs:hol_refs) =
    (M_success (Num (if left = right then 1 else 0)),refs)
Proof
  Cases_on `left = right`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

fun registered_case10173_gradient_component_dispatch_tac target =
  rpt strip_tac
  >> simp
       [registered_case10173_fs_hist_delta_gradient_component_block_unfold]
  >> simp
       [registered_case10173_fs_hist_delta_gradient_component_block_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [registered_case10173_compute_eval_num_eq,
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success,
        compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero]
  >> irule target
  >> simp []
  >> intLib.ARITH_TAC;

Theorem registered_case10173_fs_hist_delta_gradient_component_block1_typed_eval:
  bounded_historical_delta_gradient_component_decimal 1 environment =
      SOME result /\
  50 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_gradient_component_block»
        [from_cv (Num 1);
         from_cv (bounded_interval64_object_cv_list environment)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  registered_case10173_gradient_component_dispatch_tac
    compute_registeredCase10173HistoricalDeltaGradientBlockEvalTheory.registered_case10173_fs_hist_delta_gradient_block1_typed_eval
QED

Theorem registered_case10173_fs_hist_delta_gradient_component_block2_typed_eval:
  bounded_historical_delta_gradient_component_decimal 2 environment =
      SOME result /\
  50 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_gradient_component_block»
        [from_cv (Num 2);
         from_cv (bounded_interval64_object_cv_list environment)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  registered_case10173_gradient_component_dispatch_tac
    compute_registeredCase10173HistoricalDeltaGradientBlockEvalTheory.registered_case10173_fs_hist_delta_gradient_block2_typed_eval
QED

Theorem registered_case10173_fs_hist_delta_gradient_component_block3_typed_eval:
  bounded_historical_delta_gradient_component_decimal 3 environment =
      SOME result /\
  50 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_gradient_component_block»
        [from_cv (Num 3);
         from_cv (bounded_interval64_object_cv_list environment)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  registered_case10173_gradient_component_dispatch_tac
    compute_registeredCase10173HistoricalDeltaGradientBlockEvalTheory.registered_case10173_fs_hist_delta_gradient_block3_typed_eval
QED

Theorem registered_case10173_fs_hist_delta_gradient_component_block4_typed_eval:
  bounded_historical_delta_gradient_component_decimal 4 environment =
      SOME result /\
  50 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_gradient_component_block»
        [from_cv (Num 4);
         from_cv (bounded_interval64_object_cv_list environment)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  registered_case10173_gradient_component_dispatch_tac
    compute_registeredCase10173HistoricalDeltaGradientBlockEvalTheory.registered_case10173_fs_hist_delta_gradient_block4_typed_eval
QED

Theorem registered_case10173_fs_hist_delta_gradient_component_block5_typed_eval:
  bounded_historical_delta_gradient_component_decimal 5 environment =
      SOME result /\
  50 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_gradient_component_block»
        [from_cv (Num 5);
         from_cv (bounded_interval64_object_cv_list environment)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  registered_case10173_gradient_component_dispatch_tac
    compute_registeredCase10173HistoricalDeltaGradientBlockEvalTheory.registered_case10173_fs_hist_delta_gradient_block5_typed_eval
QED

Theorem registered_case10173_fs_hist_delta_gradient_component_block_typed_eval:
  coordinate < 6 /\
  bounded_historical_delta_gradient_component_decimal coordinate environment =
      SOME result /\
  50 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_gradient_component_block»
        [from_cv (Num coordinate);
         from_cv (bounded_interval64_object_cv_list environment)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  Cases_on `coordinate`
  >- (simp []
      >> ACCEPT_TAC
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_delta_gradient_component_block0_typed_eval))
  >> Cases_on `n`
  >- (simp []
      >> ACCEPT_TAC
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_delta_gradient_component_block1_typed_eval))
  >> Cases_on `n'`
  >- (simp []
      >> ACCEPT_TAC
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_delta_gradient_component_block2_typed_eval))
  >> Cases_on `n`
  >- (simp []
      >> ACCEPT_TAC
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_delta_gradient_component_block3_typed_eval))
  >> Cases_on `n'`
  >- (simp []
      >> ACCEPT_TAC
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_delta_gradient_component_block4_typed_eval))
  >> Cases_on `n`
  >- (simp []
      >> ACCEPT_TAC
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_delta_gradient_component_block5_typed_eval))
  >> simp []
QED

Definition registered_case10173_fs_hist_delta_gradient_sign_entry_body_def:
  registered_case10173_fs_hist_delta_gradient_sign_entry_body =
    Let «derivatives»
      (App «candle_cv_fs_interval_lookup»
        [Var «coordinate»;Var «hessian»])
      (Let «lower_environment»
        (App «candle_cv_fs_hist_monotone_environment»
          [Num 0;Var «boxes»;Var «derivatives»])
        (Let «upper_environment»
          (App «candle_cv_fs_hist_monotone_environment»
            [Num 1;Var «boxes»;Var «derivatives»])
          (Let «lower»
            (App «candle_cv_fs_hist_delta_gradient_component_block»
              [Var «coordinate»;Var «lower_environment»])
            (Let «upper»
              (App «candle_cv_fs_hist_delta_gradient_component_block»
                [Var «coordinate»;Var «upper_environment»])
              (Pair (Uop Fst (Var «lower»))
                (Uop Snd (Var «upper»)))))))
End

Theorem registered_case10173_fs_hist_delta_gradient_sign_entry_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_delta_gradient_sign_entry» =
    SOME
      ([«coordinate»;«boxes»;«hessian»],
       registered_case10173_fs_hist_delta_gradient_sign_entry_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_delta_gradient_sign_entry_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_gradient_sign_entry»
        [from_cv coordinate;from_cv boxes;from_cv hessian])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«coordinate»,from_cv coordinate);(«boxes»,from_cv boxes);
         («hessian»,from_cv hessian)]
        registered_case10173_fs_hist_delta_gradient_sign_entry_body)
      refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_fs_hist_delta_gradient_sign_entry_lookup]
QED

Theorem registered_case10173_fs_hist_delta_gradient_sign_entry_trace_typed_eval:
  coordinate < 6 /\
  coordinate < LENGTH rows /\
  EL coordinate rows = [d0;d1;d2;d3;d4;d5] /\
  bounded_historical_monotone_environment
      [b0;b1;b2;b3;b4;b5] [d0;d1;d2;d3;d4;d5] F =
    SOME lower_environment /\
  bounded_historical_monotone_environment
      [b0;b1;b2;b3;b4;b5] [d0;d1;d2;d3;d4;d5] T =
    SOME upper_environment /\
  bounded_historical_delta_gradient_component_decimal
      coordinate lower_environment = SOME lower_value /\
  bounded_historical_delta_gradient_component_decimal
      coordinate upper_environment = SOME upper_value /\
  90 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_gradient_sign_entry»
        [from_cv (Num coordinate);
         from_cv
           (bounded_interval64_object_cv_list [b0;b1;b2;b3;b4;b5]);
         from_cv (bounded_interval64_object_cv_matrix rows)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (bounded_historical_extreme_interval lower_value upper_value))),
     refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_delta_gradient_sign_entry_unfold]
  >> simp
       [registered_case10173_fs_hist_delta_gradient_sign_entry_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv_list [d0;d1;d2;d3;d4;d5])`
  >> conj_tac
  >- (rw
       [compute_registeredCase10173HistoricalSecondOrderPrimitiveEvalTheory.registered_case10173_object_matrix_as_cv_list]
      >> irule
           compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp [EL_MAP]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv (bounded_interval64_object_cv_list lower_environment)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss []
          (Q.INST [`upper` |-> `F`]
            compute_registeredCase10173HistoricalDeltaX4SecondEvalTheory.registered_case10173_fs_hist_monotone_environment_six_result_typed_eval))
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv (bounded_interval64_object_cv_list upper_environment)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss []
          (Q.INST [`upper` |-> `T`]
            compute_registeredCase10173HistoricalDeltaX4SecondEvalTheory.registered_case10173_fs_hist_monotone_environment_six_result_typed_eval))
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv lower_value)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_hist_delta_gradient_component_block_typed_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv upper_value)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_hist_delta_gradient_component_block_typed_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> Cases_on `lower_value`
  >> Cases_on `upper_value`
  >> simp
       [compute_boundedHistoricalDihedralSecondTheory.bounded_historical_extreme_interval_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> simp
       [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components,
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components]
QED

Theorem registered_case10173_fs_hist_delta_gradient_sign_entry_typed_eval:
  coordinate < 6 /\
  coordinate < LENGTH rows /\
  EL coordinate rows = derivatives /\
  LENGTH environment = 6 /\
  LENGTH derivatives = 6 /\
  bounded_historical_delta_gradient_box_entry_decimal
      environment derivatives coordinate = SOME result /\
  90 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_gradient_sign_entry»
        [from_cv (Num coordinate);
         from_cv (bounded_interval64_object_cv_list environment);
         from_cv (bounded_interval64_object_cv_matrix rows)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> `?b0 b1 b2 b3 b4 b5.
        environment = [b0;b1;b2;b3;b4;b5]` by
       metis_tac
         [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.length_six_cases]
  >> `?d0 d1 d2 d3 d4 d5.
        derivatives = [d0;d1;d2;d3;d4;d5]` by
       metis_tac
         [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.length_six_cases]
  >> gvs []
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_delta_gradient_box_entry_decimal_source_trace
  >> strip_tac
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_delta_gradient_sign_entry_trace_typed_eval)
  >> simp []
QED

val _ = export_theory ();
