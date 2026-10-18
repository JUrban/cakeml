(*****************************************************************************
 * Registered source refinement for the historical delta Hessian.
 *
 * The literal source constructs the symmetric six-by-six matrix directly,
 * while the typed checker keeps the 21 upper-triangular entries.  This file
 * verifies the literal construction and relates it to bounded_hessian64_rows.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaHessianEval
Ancestors
  compute_registeredCase10173HistoricalSqrtSecondEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fs_angle_three_sum_argument_results:
  registered_case10173_fs_interval_sum_object [r0;r1;r2] = SOME result /\
  8 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument0 (refs:hol_refs) = (M_success (from_cv r0),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument1 refs = (M_success (from_cv r1),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument2 refs = (M_success (from_cv r2),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [Pair argument0 (Pair argument1 (Pair argument2 (Num 0)))]) refs =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_sum»
            [from_cv (registered_case10173_cv_list [r0;r1;r2])]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> simp
           [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
            compute_evalTheory.compute_eval_def,
            compute_execProofTheory.compute_eval_from_cv,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_interval_sum_object_list_eval
  >> simp []
QED

Theorem registered_case10173_fs_angle_three_sum_typed_argument_results:
  bounded_interval64_sum [r0;r1;r2] = SOME result /\
  8 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument0 (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv r0)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument1 refs =
    (M_success (from_cv (bounded_interval64_object_cv r1)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument2 refs =
    (M_success (from_cv (bounded_interval64_object_cv r2)),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [Pair argument0 (Pair argument1 (Pair argument2 (Num 0)))]) refs =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> irule registered_case10173_fs_angle_three_sum_argument_results
  >> conj_tac >- simp []
  >> qexists_tac `bounded_interval64_object_cv r0`
  >> qexists_tac `bounded_interval64_object_cv r1`
  >> qexists_tac `bounded_interval64_object_cv r2`
  >> conj_tac
  >- (mp_tac
        (Q.INST
          [`value` |-> `r0`,`values` |-> `[r1;r2]`,`result` |-> `result`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact)
      >> simp [])
  >> simp []
QED

Theorem registered_case10173_fs_angle_six_sum_typed_argument_results:
  bounded_interval64_sum [r0;r1;r2;r3;r4;r5] = SOME result /\
  11 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument0 (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv r0)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument1 refs =
    (M_success (from_cv (bounded_interval64_object_cv r1)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument2 refs =
    (M_success (from_cv (bounded_interval64_object_cv r2)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument3 refs =
    (M_success (from_cv (bounded_interval64_object_cv r3)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument4 refs =
    (M_success (from_cv (bounded_interval64_object_cv r4)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument5 refs =
    (M_success (from_cv (bounded_interval64_object_cv r5)),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_six»
          [argument0;argument1;argument2;
           argument3;argument4;argument5]]) refs =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_angle_six_sum_argument_results
  >> conj_tac >- simp []
  >> qexists_tac `bounded_interval64_object_cv r0`
  >> qexists_tac `bounded_interval64_object_cv r1`
  >> qexists_tac `bounded_interval64_object_cv r2`
  >> qexists_tac `bounded_interval64_object_cv r3`
  >> qexists_tac `bounded_interval64_object_cv r4`
  >> qexists_tac `bounded_interval64_object_cv r5`
  >> conj_tac
  >- (mp_tac
        (Q.INST
          [`value` |-> `r0`,
           `values` |-> `[r1;r2;r3;r4;r5]`,
           `result` |-> `result`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact)
      >> simp [])
  >> simp []
QED

Definition registered_case10173_fs_angle_delta_hessian_body_def:
  registered_case10173_fs_angle_delta_hessian_body =
    Let «x0» (App «candle_cv_fs_interval_lookup» [Num 0;Var «environment»])
    (Let «x1» (App «candle_cv_fs_interval_lookup» [Num 1;Var «environment»])
    (Let «x2» (App «candle_cv_fs_interval_lookup» [Num 2;Var «environment»])
    (Let «x3» (App «candle_cv_fs_interval_lookup» [Num 3;Var «environment»])
    (Let «x4» (App «candle_cv_fs_interval_lookup» [Num 4;Var «environment»])
    (Let «x5» (App «candle_cv_fs_interval_lookup» [Num 5;Var «environment»])
    (Let «h00» (App «candle_cv_fs_angle_interval_scale_neg_two» [Var «x3»])
    (Let «h01» (App «candle_cv_fs_angle_interval_sum»
      [Pair (Var «x3») (Pair (Var «x4»)
        (Pair (App «candle_cv_fs_interval_neg» [Var «x5»]) (Num 0)))])
    (Let «h02» (App «candle_cv_fs_angle_interval_sum»
      [Pair (Var «x3»)
        (Pair (App «candle_cv_fs_interval_neg» [Var «x4»])
          (Pair (Var «x5») (Num 0)))])
    (Let «h03» (App «candle_cv_fs_angle_interval_sum»
      [App «candle_cv_fs_angle_six»
        [App «candle_cv_fs_angle_interval_scale_neg_two» [Var «x0»];
         Var «x1»;Var «x2»;
         App «candle_cv_fs_angle_interval_scale_neg_two» [Var «x3»];
         Var «x4»;Var «x5»]])
    (Let «h04» (App «candle_cv_fs_angle_interval_sum»
      [Pair (Var «x1»)
        (Pair (App «candle_cv_fs_interval_neg» [Var «x2»])
          (Pair (Var «x3») (Num 0)))])
    (Let «h05» (App «candle_cv_fs_angle_interval_sum»
      [Pair (App «candle_cv_fs_interval_neg» [Var «x1»])
        (Pair (Var «x2») (Pair (Var «x3») (Num 0)))])
    (Let «h11» (App «candle_cv_fs_angle_interval_scale_neg_two» [Var «x4»])
    (Let «h12» (App «candle_cv_fs_angle_interval_sum»
      [Pair (App «candle_cv_fs_interval_neg» [Var «x3»])
        (Pair (Var «x4») (Pair (Var «x5») (Num 0)))])
    (Let «h13» (App «candle_cv_fs_angle_interval_sum»
      [Pair (Var «x0»)
        (Pair (App «candle_cv_fs_interval_neg» [Var «x2»])
          (Pair (Var «x4») (Num 0)))])
    (Let «h14» (App «candle_cv_fs_angle_interval_sum»
      [App «candle_cv_fs_angle_six»
        [Var «x0»;
         App «candle_cv_fs_angle_interval_scale_neg_two» [Var «x1»];
         Var «x2»;Var «x3»;
         App «candle_cv_fs_angle_interval_scale_neg_two» [Var «x4»];
         Var «x5»]])
    (Let «h15» (App «candle_cv_fs_angle_interval_sum»
      [Pair (App «candle_cv_fs_interval_neg» [Var «x0»])
        (Pair (Var «x2») (Pair (Var «x4») (Num 0)))])
    (Let «h22» (App «candle_cv_fs_angle_interval_scale_neg_two» [Var «x5»])
    (Let «h23» (App «candle_cv_fs_angle_interval_sum»
      [Pair (Var «x0»)
        (Pair (App «candle_cv_fs_interval_neg» [Var «x1»])
          (Pair (Var «x5») (Num 0)))])
    (Let «h24» (App «candle_cv_fs_angle_interval_sum»
      [Pair (App «candle_cv_fs_interval_neg» [Var «x0»])
        (Pair (Var «x1») (Pair (Var «x5») (Num 0)))])
    (Let «h25» (App «candle_cv_fs_angle_interval_sum»
      [App «candle_cv_fs_angle_six»
        [Var «x0»;Var «x1»;
         App «candle_cv_fs_angle_interval_scale_neg_two» [Var «x2»];
         Var «x3»;Var «x4»;
         App «candle_cv_fs_angle_interval_scale_neg_two» [Var «x5»]]])
    (Let «h33» (App «candle_cv_fs_angle_interval_scale_neg_two» [Var «x0»])
    (Let «h34» (App «candle_cv_fs_angle_interval_sum»
      [Pair (Var «x0») (Pair (Var «x1»)
        (Pair (App «candle_cv_fs_interval_neg» [Var «x5»]) (Num 0)))])
    (Let «h35» (App «candle_cv_fs_angle_interval_sum»
      [Pair (Var «x0») (Pair (Var «x2»)
        (Pair (App «candle_cv_fs_interval_neg» [Var «x4»]) (Num 0)))])
    (Let «h44» (App «candle_cv_fs_angle_interval_scale_neg_two» [Var «x1»])
    (Let «h45» (App «candle_cv_fs_angle_interval_sum»
      [Pair (Var «x1») (Pair (Var «x2»)
        (Pair (App «candle_cv_fs_interval_neg» [Var «x3»]) (Num 0)))])
    (Let «h55» (App «candle_cv_fs_angle_interval_scale_neg_two» [Var «x2»])
      (App «candle_cv_fs_angle_six»
        [App «candle_cv_fs_angle_six»
           [Var «h00»;Var «h01»;Var «h02»;
            Var «h03»;Var «h04»;Var «h05»];
         App «candle_cv_fs_angle_six»
           [Var «h01»;Var «h11»;Var «h12»;
            Var «h13»;Var «h14»;Var «h15»];
         App «candle_cv_fs_angle_six»
           [Var «h02»;Var «h12»;Var «h22»;
            Var «h23»;Var «h24»;Var «h25»];
         App «candle_cv_fs_angle_six»
           [Var «h03»;Var «h13»;Var «h23»;
            Var «h33»;Var «h34»;Var «h35»];
         App «candle_cv_fs_angle_six»
           [Var «h04»;Var «h14»;Var «h24»;
            Var «h34»;Var «h44»;Var «h45»];
         App «candle_cv_fs_angle_six»
           [Var «h05»;Var «h15»;Var «h25»;
            Var «h35»;Var «h45»;Var «h55»]])))))))))))))))))))))))))))
End

Theorem registered_case10173_fs_angle_delta_hessian_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_delta_hessian» =
    SOME ([«environment»],registered_case10173_fs_angle_delta_hessian_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_delta_hessian_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_hessian» [from_cv environment])
      (refs:hol_refs) =
    compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (subst [(«environment»,from_cv environment)]
        registered_case10173_fs_angle_delta_hessian_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_angle_delta_hessian_lookup]
QED

Theorem registered_case10173_bounded_interval64_object_cv_matrix_six_rows:
  bounded_interval64_object_cv_matrix [r0;r1;r2;r3;r4;r5] =
    registered_case10173_cv_list
      [bounded_interval64_object_cv_list r0;
       bounded_interval64_object_cv_list r1;
       bounded_interval64_object_cv_list r2;
       bounded_interval64_object_cv_list r3;
       bounded_interval64_object_cv_list r4;
       bounded_interval64_object_cv_list r5]
Proof
  simp
    [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def,
     compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
     compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
QED

Theorem registered_case10173_fs_angle_delta_hessian_trace_typed_eval:
  bounded_interval64_add (bounded_interval64_neg x3)
      (bounded_interval64_neg x3) = SOME h00 /\
  bounded_interval64_sum [x3;x4;bounded_interval64_neg x5] = SOME h01 /\
  bounded_interval64_sum [x3;bounded_interval64_neg x4;x5] = SOME h02 /\
  bounded_interval64_sum
      [h33;x1;x2;h00;x4;x5] = SOME h03 /\
  bounded_interval64_sum [x1;bounded_interval64_neg x2;x3] = SOME h04 /\
  bounded_interval64_sum [bounded_interval64_neg x1;x2;x3] = SOME h05 /\
  bounded_interval64_add (bounded_interval64_neg x4)
      (bounded_interval64_neg x4) = SOME h11 /\
  bounded_interval64_sum [bounded_interval64_neg x3;x4;x5] = SOME h12 /\
  bounded_interval64_sum [x0;bounded_interval64_neg x2;x4] = SOME h13 /\
  bounded_interval64_sum
      [x0;h44;x2;x3;h11;x5] = SOME h14 /\
  bounded_interval64_sum [bounded_interval64_neg x0;x2;x4] = SOME h15 /\
  bounded_interval64_add (bounded_interval64_neg x5)
      (bounded_interval64_neg x5) = SOME h22 /\
  bounded_interval64_sum [x0;bounded_interval64_neg x1;x5] = SOME h23 /\
  bounded_interval64_sum [bounded_interval64_neg x0;x1;x5] = SOME h24 /\
  bounded_interval64_sum
      [x0;x1;h55;x3;x4;h22] = SOME h25 /\
  bounded_interval64_add (bounded_interval64_neg x0)
      (bounded_interval64_neg x0) = SOME h33 /\
  bounded_interval64_sum [x0;x1;bounded_interval64_neg x5] = SOME h34 /\
  bounded_interval64_sum [x0;x2;bounded_interval64_neg x4] = SOME h35 /\
  bounded_interval64_add (bounded_interval64_neg x1)
      (bounded_interval64_neg x1) = SOME h44 /\
  bounded_interval64_sum [x1;x2;bounded_interval64_neg x3] = SOME h45 /\
  bounded_interval64_add (bounded_interval64_neg x2)
      (bounded_interval64_neg x2) = SOME h55 /\
  75 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_hessian»
        [from_cv
          (bounded_interval64_object_cv_list [x0;x1;x2;x3;x4;x5])])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv_matrix
          [[h00;h01;h02;h03;h04;h05];
           [h01;h11;h12;h13;h14;h15];
           [h02;h12;h22;h23;h24;h25];
           [h03;h13;h23;h33;h34;h35];
           [h04;h14;h24;h34;h44;h45];
           [h05;h15;h25;h35;h45;h55]])),refs)
Proof
  rpt strip_tac
  >> `registered_case10173_fs_interval_scale_neg_two_object
        (bounded_interval64_object_cv x3) =
      SOME (bounded_interval64_object_cv h00)` by
       (irule
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_scale_neg_two_object_typed_exact
        >> simp [])
  >> `registered_case10173_fs_interval_scale_neg_two_object
        (bounded_interval64_object_cv x4) =
      SOME (bounded_interval64_object_cv h11)` by
       (irule
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_scale_neg_two_object_typed_exact
        >> simp [])
  >> `registered_case10173_fs_interval_scale_neg_two_object
        (bounded_interval64_object_cv x5) =
      SOME (bounded_interval64_object_cv h22)` by
       (irule
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_scale_neg_two_object_typed_exact
        >> simp [])
  >> `registered_case10173_fs_interval_scale_neg_two_object
        (bounded_interval64_object_cv x0) =
      SOME (bounded_interval64_object_cv h33)` by
       (irule
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_scale_neg_two_object_typed_exact
        >> simp [])
  >> `registered_case10173_fs_interval_scale_neg_two_object
        (bounded_interval64_object_cv x1) =
      SOME (bounded_interval64_object_cv h44)` by
       (irule
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_scale_neg_two_object_typed_exact
        >> simp [])
  >> `registered_case10173_fs_interval_scale_neg_two_object
        (bounded_interval64_object_cv x2) =
      SOME (bounded_interval64_object_cv h55)` by
       (irule
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_scale_neg_two_object_typed_exact
        >> simp [])
  >> simp [registered_case10173_fs_angle_delta_hessian_unfold]
  >> simp
       [registered_case10173_fs_angle_delta_hessian_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv x0)`
  >> conj_tac
  >- (mp_tac
        (Q.SPECL
          [`0`,`[x0;x1;x2;x3;x4;x5]`,`clock - 1`,`refs`]
          compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval)
      >> simp [compute_execTheory.from_cv_def]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv x1)`
  >> conj_tac
  >- (mp_tac
        (Q.SPECL
          [`1`,`[x0;x1;x2;x3;x4;x5]`,`clock - 2`,`refs`]
          compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval)
      >> simp [compute_execTheory.from_cv_def]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv x2)`
  >> conj_tac
  >- (mp_tac
        (Q.SPECL
          [`2`,`[x0;x1;x2;x3;x4;x5]`,`clock - 3`,`refs`]
          compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval)
      >> simp [compute_execTheory.from_cv_def]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv x3)`
  >> conj_tac
  >- (mp_tac
        (Q.SPECL
          [`3`,`[x0;x1;x2;x3;x4;x5]`,`clock - 4`,`refs`]
          compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval)
      >> simp [compute_execTheory.from_cv_def]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv x4)`
  >> conj_tac
  >- (mp_tac
        (Q.SPECL
          [`4`,`[x0;x1;x2;x3;x4;x5]`,`clock - 5`,`refs`]
          compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval)
      >> simp [compute_execTheory.from_cv_def]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv x5)`
  >> conj_tac
  >- (mp_tac
        (Q.SPECL
          [`5`,`[x0;x1;x2;x3;x4;x5]`,`clock - 6`,`refs`]
          compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval)
      >> simp [compute_execTheory.from_cv_def]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h00)`
  >> conj_tac
  >- (mp_tac
        (Q.INST
          [`source` |-> `bounded_interval64_object_cv x3`,
           `result` |-> `bounded_interval64_object_cv h00`,
           `clock` |-> `clock - 7`,`refs` |-> `refs`]
          compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h01)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_three_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `x3`
      >> qexists_tac `x4`
      >> qexists_tac `bounded_interval64_neg x5`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h02)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_three_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `x3`
      >> qexists_tac `bounded_interval64_neg x4`
      >> qexists_tac `x5`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h03)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_six_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `h33`
      >> qexists_tac `x1`
      >> qexists_tac `x2`
      >> qexists_tac `h00`
      >> qexists_tac `x4`
      >> qexists_tac `x5`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h04)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_three_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `x1`
      >> qexists_tac `bounded_interval64_neg x2`
      >> qexists_tac `x3`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h05)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_three_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `bounded_interval64_neg x1`
      >> qexists_tac `x2`
      >> qexists_tac `x3`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h11)`
  >> conj_tac
  >- (mp_tac
        (Q.INST
          [`source` |-> `bounded_interval64_object_cv x4`,
           `result` |-> `bounded_interval64_object_cv h11`,
           `clock` |-> `clock - 13`,`refs` |-> `refs`]
          compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h12)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_three_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `bounded_interval64_neg x3`
      >> qexists_tac `x4`
      >> qexists_tac `x5`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h13)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_three_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `x0`
      >> qexists_tac `bounded_interval64_neg x2`
      >> qexists_tac `x4`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h14)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_six_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `x0`
      >> qexists_tac `h44`
      >> qexists_tac `x2`
      >> qexists_tac `x3`
      >> qexists_tac `h11`
      >> qexists_tac `x5`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h15)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_three_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `bounded_interval64_neg x0`
      >> qexists_tac `x2`
      >> qexists_tac `x4`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h22)`
  >> conj_tac
  >- (mp_tac
        (Q.INST
          [`source` |-> `bounded_interval64_object_cv x5`,
           `result` |-> `bounded_interval64_object_cv h22`,
           `clock` |-> `clock - 18`,`refs` |-> `refs`]
          compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h23)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_three_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `x0`
      >> qexists_tac `bounded_interval64_neg x1`
      >> qexists_tac `x5`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h24)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_three_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `bounded_interval64_neg x0`
      >> qexists_tac `x1`
      >> qexists_tac `x5`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h25)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_six_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `x0`
      >> qexists_tac `x1`
      >> qexists_tac `h55`
      >> qexists_tac `x3`
      >> qexists_tac `x4`
      >> qexists_tac `h22`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h33)`
  >> conj_tac
  >- (mp_tac
        (Q.INST
          [`source` |-> `bounded_interval64_object_cv x0`,
           `result` |-> `bounded_interval64_object_cv h33`,
           `clock` |-> `clock - 22`,`refs` |-> `refs`]
          compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h34)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_three_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `x0`
      >> qexists_tac `x1`
      >> qexists_tac `bounded_interval64_neg x5`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h35)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_three_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `x0`
      >> qexists_tac `x2`
      >> qexists_tac `bounded_interval64_neg x4`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h44)`
  >> conj_tac
  >- (mp_tac
        (Q.INST
          [`source` |-> `bounded_interval64_object_cv x1`,
           `result` |-> `bounded_interval64_object_cv h44`,
           `clock` |-> `clock - 25`,`refs` |-> `refs`]
          compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h45)`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_three_sum_typed_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `x1`
      >> qexists_tac `x2`
      >> qexists_tac `bounded_interval64_neg x3`
      >> simp
           [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact,
            compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval,
            compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv h55)`
  >> conj_tac
  >- (mp_tac
        (Q.INST
          [`source` |-> `bounded_interval64_object_cv x2`,
           `result` |-> `bounded_interval64_object_cv h55`,
           `clock` |-> `clock - 27`,`refs` |-> `refs`]
          compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 28)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_six»
            [from_cv (bounded_interval64_object_cv_list
               [h00;h01;h02;h03;h04;h05]);
             from_cv (bounded_interval64_object_cv_list
               [h01;h11;h12;h13;h14;h15]);
             from_cv (bounded_interval64_object_cv_list
               [h02;h12;h22;h23;h24;h25]);
             from_cv (bounded_interval64_object_cv_list
               [h03;h13;h23;h33;h34;h35]);
             from_cv (bounded_interval64_object_cv_list
               [h04;h14;h24;h34;h44;h45]);
             from_cv (bounded_interval64_object_cv_list
               [h05;h15;h25;h35;h45;h55])]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_compute_eval_app6_argument_results
      >> simp
           [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
      >> rpt conj_tac
      >> irule
           (SIMP_RULE std_ss
             [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
              compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
              compute_execTheory.from_cv_def]
             compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval)
      >> intLib.ARITH_TAC)
  >> once_rewrite_tac
       [registered_case10173_bounded_interval64_object_cv_matrix_six_rows]
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
