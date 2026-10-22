(*****************************************************************************
 * Registered evaluator semantics for the six ten-term component sums in the
 * historical delta gradient.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaGradientComponentEval
Ancestors
  compute_registeredCase10173HistoricalDeltaValueEval
Libs
  bossLib preamble intLib

val _ = monadsyntax.temp_enable_monad "option";

Theorem registered_case10173_compute_eval_app10_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument0 (refs:hol_refs) =
      (M_success (from_cv result0),refs) /\
  compute_eval clock ceqs argument1 refs =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) /\
  compute_eval clock ceqs argument3 refs =
      (M_success (from_cv result3),refs) /\
  compute_eval clock ceqs argument4 refs =
      (M_success (from_cv result4),refs) /\
  compute_eval clock ceqs argument5 refs =
      (M_success (from_cv result5),refs) /\
  compute_eval clock ceqs argument6 refs =
      (M_success (from_cv result6),refs) /\
  compute_eval clock ceqs argument7 refs =
      (M_success (from_cv result7),refs) /\
  compute_eval clock ceqs argument8 refs =
      (M_success (from_cv result8),refs) /\
  compute_eval clock ceqs argument9 refs =
      (M_success (from_cv result9),refs) ==>
  compute_eval clock ceqs
      (App function_name
        [argument0;argument1;argument2;argument3;argument4;
         argument5;argument6;argument7;argument8;argument9]) refs =
    compute_eval clock ceqs
      (App function_name
        [from_cv result0;from_cv result1;from_cv result2;from_cv result3;
         from_cv result4;from_cv result5;from_cv result6;from_cv result7;
         from_cv result8;from_cv result9]) refs
Proof
  Cases_on `clock`
  >> simp []
  >> strip_tac
  >> Cases_on `ALOOKUP ceqs function_name`
  >- simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `x`
  >> Cases_on `LENGTH q = 10`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_angle_ten_sum_argument_results:
  registered_case10173_fs_interval_sum_object
      [r0;r1;r2;r3;r4;r5;r6;r7;r8;r9] = SOME result /\
  15 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument0 (refs:hol_refs) = (M_success (from_cv r0),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument1 refs = (M_success (from_cv r1),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument2 refs = (M_success (from_cv r2),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument3 refs = (M_success (from_cv r3),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument4 refs = (M_success (from_cv r4),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument5 refs = (M_success (from_cv r5),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument6 refs = (M_success (from_cv r6),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument7 refs = (M_success (from_cv r7),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument8 refs = (M_success (from_cv r8),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument9 refs = (M_success (from_cv r9),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_ten»
          [argument0;argument1;argument2;argument3;argument4;
           argument5;argument6;argument7;argument8;argument9]]) refs =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_sum»
            [from_cv
              (registered_case10173_cv_list
                [r0;r1;r2;r3;r4;r5;r6;r7;r8;r9])]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fs_angle_ten»
                [from_cv r0;from_cv r1;from_cv r2;from_cv r3;from_cv r4;
                 from_cv r5;from_cv r6;from_cv r7;from_cv r8;from_cv r9]) refs`
      >> conj_tac
      >- (irule registered_case10173_compute_eval_app10_argument_results
          >> simp [])
      >> irule
           compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_ten_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_interval_sum_object_list_eval
  >> simp []
QED

Definition registered_case10173_fs_angle_delta_gradient_component0_object_def:
  registered_case10173_fs_angle_delta_gradient_component0_object
      p03 p13 p14 p15 p23 p24 p25 p33 p34 p35 =
    do
      s03 <- registered_case10173_fs_interval_scale_neg_two_object p03;
      n15 <- bounded_object_fs_interval_neg p15;
      n24 <- bounded_object_fs_interval_neg p24;
      n33 <- bounded_object_fs_interval_neg p33;
      registered_case10173_fs_interval_sum_object
        [s03;p13;p14;n15;p23;n24;p25;n33;p34;p35]
    od
End

Definition registered_case10173_fs_angle_delta_gradient_component1_object_def:
  registered_case10173_fs_angle_delta_gradient_component1_object
      p03 p04 p05 p14 p23 p24 p25 p34 p44 p45 =
    do
      n05 <- bounded_object_fs_interval_neg p05;
      s14 <- registered_case10173_fs_interval_scale_neg_two_object p14;
      n23 <- bounded_object_fs_interval_neg p23;
      n44 <- bounded_object_fs_interval_neg p44;
      registered_case10173_fs_interval_sum_object
        [p03;p04;n05;s14;n23;p24;p25;p34;n44;p45]
    od
End

Definition registered_case10173_fs_angle_delta_gradient_component2_object_def:
  registered_case10173_fs_angle_delta_gradient_component2_object
      p03 p04 p05 p13 p14 p15 p25 p35 p45 p55 =
    do
      n04 <- bounded_object_fs_interval_neg p04;
      n13 <- bounded_object_fs_interval_neg p13;
      s25 <- registered_case10173_fs_interval_scale_neg_two_object p25;
      n55 <- bounded_object_fs_interval_neg p55;
      registered_case10173_fs_interval_sum_object
        [p03;n04;p05;n13;p14;p15;s25;p35;p45;n55]
    od
End

Definition registered_case10173_fs_angle_delta_gradient_component3_object_def:
  registered_case10173_fs_angle_delta_gradient_component3_object
      p00 p01 p02 p03 p04 p05 p12 p14 p25 p45 =
    do
      n00 <- bounded_object_fs_interval_neg p00;
      s03 <- registered_case10173_fs_interval_scale_neg_two_object p03;
      n12 <- bounded_object_fs_interval_neg p12;
      n45 <- bounded_object_fs_interval_neg p45;
      registered_case10173_fs_interval_sum_object
        [n00;p01;p02;s03;p04;p05;n12;p14;p25;n45]
    od
End

Definition registered_case10173_fs_angle_delta_gradient_component4_object_def:
  registered_case10173_fs_angle_delta_gradient_component4_object
      p01 p02 p03 p11 p12 p13 p14 p15 p25 p35 =
    do
      n02 <- bounded_object_fs_interval_neg p02;
      n11 <- bounded_object_fs_interval_neg p11;
      s14 <- registered_case10173_fs_interval_scale_neg_two_object p14;
      n35 <- bounded_object_fs_interval_neg p35;
      registered_case10173_fs_interval_sum_object
        [p01;n02;p03;n11;p12;p13;s14;p15;p25;n35]
    od
End

Definition registered_case10173_fs_angle_delta_gradient_component5_object_def:
  registered_case10173_fs_angle_delta_gradient_component5_object
      p01 p02 p03 p12 p14 p22 p23 p24 p25 p34 =
    do
      n01 <- bounded_object_fs_interval_neg p01;
      n22 <- bounded_object_fs_interval_neg p22;
      s25 <- registered_case10173_fs_interval_scale_neg_two_object p25;
      n34 <- bounded_object_fs_interval_neg p34;
      registered_case10173_fs_interval_sum_object
        [n01;p02;p03;p12;p14;n22;p23;p24;s25;n34]
    od
End

Theorem registered_case10173_fs_angle_delta_gradient_component0_trace_eval:
  registered_case10173_fs_interval_scale_neg_two_object p03 = SOME s03 /\
  bounded_object_fs_interval_neg p15 = SOME n15 /\
  bounded_object_fs_interval_neg p24 = SOME n24 /\
  bounded_object_fs_interval_neg p33 = SOME n33 /\
  registered_case10173_fs_interval_sum_object
      [s03;p13;p14;n15;p23;n24;p25;n33;p34;p35] = SOME result /\
  25 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_ten»
          [App «candle_cv_fs_angle_interval_scale_neg_two» [from_cv p03];
           from_cv p13;from_cv p14;
           App «candle_cv_fs_interval_neg» [from_cv p15];from_cv p23;
           App «candle_cv_fs_interval_neg» [from_cv p24];from_cv p25;
           App «candle_cv_fs_interval_neg» [from_cv p33];
           from_cv p34;from_cv p35]]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule registered_case10173_fs_angle_ten_sum_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexistsl_tac [`s03`,`p13`,`p14`,`n15`,`p23`,`n24`,`p25`,`n33`,`p34`,`p35`]
  >> simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval,
        compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_angle_delta_gradient_component1_trace_eval:
  bounded_object_fs_interval_neg p05 = SOME n05 /\
  registered_case10173_fs_interval_scale_neg_two_object p14 = SOME s14 /\
  bounded_object_fs_interval_neg p23 = SOME n23 /\
  bounded_object_fs_interval_neg p44 = SOME n44 /\
  registered_case10173_fs_interval_sum_object
      [p03;p04;n05;s14;n23;p24;p25;p34;n44;p45] = SOME result /\
  25 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_ten»
          [from_cv p03;from_cv p04;
           App «candle_cv_fs_interval_neg» [from_cv p05];
           App «candle_cv_fs_angle_interval_scale_neg_two» [from_cv p14];
           App «candle_cv_fs_interval_neg» [from_cv p23];
           from_cv p24;from_cv p25;from_cv p34;
           App «candle_cv_fs_interval_neg» [from_cv p44];from_cv p45]])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule registered_case10173_fs_angle_ten_sum_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexistsl_tac [`p03`,`p04`,`n05`,`s14`,`n23`,`p24`,`p25`,`p34`,`n44`,`p45`]
  >> simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval,
        compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_angle_delta_gradient_component2_trace_eval:
  bounded_object_fs_interval_neg p04 = SOME n04 /\
  bounded_object_fs_interval_neg p13 = SOME n13 /\
  registered_case10173_fs_interval_scale_neg_two_object p25 = SOME s25 /\
  bounded_object_fs_interval_neg p55 = SOME n55 /\
  registered_case10173_fs_interval_sum_object
      [p03;n04;p05;n13;p14;p15;s25;p35;p45;n55] = SOME result /\
  25 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_ten»
          [from_cv p03;App «candle_cv_fs_interval_neg» [from_cv p04];
           from_cv p05;App «candle_cv_fs_interval_neg» [from_cv p13];
           from_cv p14;from_cv p15;
           App «candle_cv_fs_angle_interval_scale_neg_two» [from_cv p25];
           from_cv p35;from_cv p45;
           App «candle_cv_fs_interval_neg» [from_cv p55]]])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule registered_case10173_fs_angle_ten_sum_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexistsl_tac [`p03`,`n04`,`p05`,`n13`,`p14`,`p15`,`s25`,`p35`,`p45`,`n55`]
  >> simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval,
        compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_angle_delta_gradient_component3_trace_eval:
  bounded_object_fs_interval_neg p00 = SOME n00 /\
  registered_case10173_fs_interval_scale_neg_two_object p03 = SOME s03 /\
  bounded_object_fs_interval_neg p12 = SOME n12 /\
  bounded_object_fs_interval_neg p45 = SOME n45 /\
  registered_case10173_fs_interval_sum_object
      [n00;p01;p02;s03;p04;p05;n12;p14;p25;n45] = SOME result /\
  25 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_ten»
          [App «candle_cv_fs_interval_neg» [from_cv p00];from_cv p01;
           from_cv p02;
           App «candle_cv_fs_angle_interval_scale_neg_two» [from_cv p03];
           from_cv p04;from_cv p05;
           App «candle_cv_fs_interval_neg» [from_cv p12];
           from_cv p14;from_cv p25;
           App «candle_cv_fs_interval_neg» [from_cv p45]]])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule registered_case10173_fs_angle_ten_sum_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexistsl_tac [`n00`,`p01`,`p02`,`s03`,`p04`,`p05`,`n12`,`p14`,`p25`,`n45`]
  >> simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval,
        compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_angle_delta_gradient_component4_trace_eval:
  bounded_object_fs_interval_neg p02 = SOME n02 /\
  bounded_object_fs_interval_neg p11 = SOME n11 /\
  registered_case10173_fs_interval_scale_neg_two_object p14 = SOME s14 /\
  bounded_object_fs_interval_neg p35 = SOME n35 /\
  registered_case10173_fs_interval_sum_object
      [p01;n02;p03;n11;p12;p13;s14;p15;p25;n35] = SOME result /\
  25 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_ten»
          [from_cv p01;App «candle_cv_fs_interval_neg» [from_cv p02];
           from_cv p03;App «candle_cv_fs_interval_neg» [from_cv p11];
           from_cv p12;from_cv p13;
           App «candle_cv_fs_angle_interval_scale_neg_two» [from_cv p14];
           from_cv p15;from_cv p25;
           App «candle_cv_fs_interval_neg» [from_cv p35]]])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule registered_case10173_fs_angle_ten_sum_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexistsl_tac [`p01`,`n02`,`p03`,`n11`,`p12`,`p13`,`s14`,`p15`,`p25`,`n35`]
  >> simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval,
        compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_angle_delta_gradient_component5_trace_eval:
  bounded_object_fs_interval_neg p01 = SOME n01 /\
  bounded_object_fs_interval_neg p22 = SOME n22 /\
  registered_case10173_fs_interval_scale_neg_two_object p25 = SOME s25 /\
  bounded_object_fs_interval_neg p34 = SOME n34 /\
  registered_case10173_fs_interval_sum_object
      [n01;p02;p03;p12;p14;n22;p23;p24;s25;n34] = SOME result /\
  25 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_ten»
          [App «candle_cv_fs_interval_neg» [from_cv p01];from_cv p02;
           from_cv p03;from_cv p12;from_cv p14;
           App «candle_cv_fs_interval_neg» [from_cv p22];
           from_cv p23;from_cv p24;
           App «candle_cv_fs_angle_interval_scale_neg_two» [from_cv p25];
           App «candle_cv_fs_interval_neg» [from_cv p34]]])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule registered_case10173_fs_angle_ten_sum_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexistsl_tac [`n01`,`p02`,`p03`,`p12`,`p14`,`n22`,`p23`,`p24`,`s25`,`n34`]
  >> simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_neg_two_object_eval,
        compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_angle_delta_gradient_component0_object_eval:
  registered_case10173_fs_angle_delta_gradient_component0_object
      p03 p13 p14 p15 p23 p24 p25 p33 p34 p35 = SOME result /\
  25 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_ten»
          [App «candle_cv_fs_angle_interval_scale_neg_two» [from_cv p03];
           from_cv p13;from_cv p14;
           App «candle_cv_fs_interval_neg» [from_cv p15];from_cv p23;
           App «candle_cv_fs_interval_neg» [from_cv p24];from_cv p25;
           App «candle_cv_fs_interval_neg» [from_cv p33];
           from_cv p34;from_cv p35]]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> fs [registered_case10173_fs_angle_delta_gradient_component0_object_def]
  >> every_case_tac >> gvs []
  >> irule registered_case10173_fs_angle_delta_gradient_component0_trace_eval
  >> simp []
QED

Theorem registered_case10173_fs_angle_delta_gradient_component1_object_eval:
  registered_case10173_fs_angle_delta_gradient_component1_object
      p03 p04 p05 p14 p23 p24 p25 p34 p44 p45 = SOME result /\
  25 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_ten»
          [from_cv p03;from_cv p04;
           App «candle_cv_fs_interval_neg» [from_cv p05];
           App «candle_cv_fs_angle_interval_scale_neg_two» [from_cv p14];
           App «candle_cv_fs_interval_neg» [from_cv p23];
           from_cv p24;from_cv p25;from_cv p34;
           App «candle_cv_fs_interval_neg» [from_cv p44];from_cv p45]])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> fs [registered_case10173_fs_angle_delta_gradient_component1_object_def]
  >> every_case_tac >> gvs []
  >> irule registered_case10173_fs_angle_delta_gradient_component1_trace_eval
  >> simp []
QED

Theorem registered_case10173_fs_angle_delta_gradient_component2_object_eval:
  registered_case10173_fs_angle_delta_gradient_component2_object
      p03 p04 p05 p13 p14 p15 p25 p35 p45 p55 = SOME result /\
  25 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_ten»
          [from_cv p03;App «candle_cv_fs_interval_neg» [from_cv p04];
           from_cv p05;App «candle_cv_fs_interval_neg» [from_cv p13];
           from_cv p14;from_cv p15;
           App «candle_cv_fs_angle_interval_scale_neg_two» [from_cv p25];
           from_cv p35;from_cv p45;
           App «candle_cv_fs_interval_neg» [from_cv p55]]])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> fs [registered_case10173_fs_angle_delta_gradient_component2_object_def]
  >> every_case_tac >> gvs []
  >> irule registered_case10173_fs_angle_delta_gradient_component2_trace_eval
  >> simp []
QED

Theorem registered_case10173_fs_angle_delta_gradient_component3_object_eval:
  registered_case10173_fs_angle_delta_gradient_component3_object
      p00 p01 p02 p03 p04 p05 p12 p14 p25 p45 = SOME result /\
  25 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_ten»
          [App «candle_cv_fs_interval_neg» [from_cv p00];from_cv p01;
           from_cv p02;
           App «candle_cv_fs_angle_interval_scale_neg_two» [from_cv p03];
           from_cv p04;from_cv p05;
           App «candle_cv_fs_interval_neg» [from_cv p12];
           from_cv p14;from_cv p25;
           App «candle_cv_fs_interval_neg» [from_cv p45]]])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> fs [registered_case10173_fs_angle_delta_gradient_component3_object_def]
  >> every_case_tac >> gvs []
  >> irule registered_case10173_fs_angle_delta_gradient_component3_trace_eval
  >> simp []
QED

Theorem registered_case10173_fs_angle_delta_gradient_component4_object_eval:
  registered_case10173_fs_angle_delta_gradient_component4_object
      p01 p02 p03 p11 p12 p13 p14 p15 p25 p35 = SOME result /\
  25 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_ten»
          [from_cv p01;App «candle_cv_fs_interval_neg» [from_cv p02];
           from_cv p03;App «candle_cv_fs_interval_neg» [from_cv p11];
           from_cv p12;from_cv p13;
           App «candle_cv_fs_angle_interval_scale_neg_two» [from_cv p14];
           from_cv p15;from_cv p25;
           App «candle_cv_fs_interval_neg» [from_cv p35]]])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> fs [registered_case10173_fs_angle_delta_gradient_component4_object_def]
  >> every_case_tac >> gvs []
  >> irule registered_case10173_fs_angle_delta_gradient_component4_trace_eval
  >> simp []
QED

Theorem registered_case10173_fs_angle_delta_gradient_component5_object_eval:
  registered_case10173_fs_angle_delta_gradient_component5_object
      p01 p02 p03 p12 p14 p22 p23 p24 p25 p34 = SOME result /\
  25 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_ten»
          [App «candle_cv_fs_interval_neg» [from_cv p01];from_cv p02;
           from_cv p03;from_cv p12;from_cv p14;
           App «candle_cv_fs_interval_neg» [from_cv p22];
           from_cv p23;from_cv p24;
           App «candle_cv_fs_angle_interval_scale_neg_two» [from_cv p25];
           App «candle_cv_fs_interval_neg» [from_cv p34]]])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> fs [registered_case10173_fs_angle_delta_gradient_component5_object_def]
  >> every_case_tac >> gvs []
  >> irule registered_case10173_fs_angle_delta_gradient_component5_trace_eval
  >> simp []
QED

val _ = export_theory ();
