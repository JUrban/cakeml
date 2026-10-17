(*****************************************************************************
 * Registered evaluator semantics for the historical delta_x4 box value.
 *
 * Unlike the center-value source, this block preserves raw products until a
 * single outward rounding step.  The trace theorem follows that source order
 * exactly, so the later typed refinement need not assume reassociation of
 * bounded interval operations.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaX4ValueBlockEval
Ancestors
  compute_registeredCase10173HistoricalMonotoneEval
  compute_registeredCase10173HistoricalUValueEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_raw_product_body_def:
  registered_case10173_fs_hist_raw_product_body =
    App «candle_cv_fs_raw_interval_mul» [Var «left»;Var «right»]
End

Theorem registered_case10173_fs_hist_raw_product_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_raw_product» =
    SOME
      ([«left»;«right»],
       registered_case10173_fs_hist_raw_product_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_raw_product_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_raw_product»
        [from_cv left;from_cv right]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«left»,from_cv left);(«right»,from_cv right)]
        registered_case10173_fs_hist_raw_product_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_hist_raw_product_lookup]
QED

Theorem registered_case10173_fs_hist_raw_product_eval:
  bounded_object_fs_raw_interval_mul left right = SOME result /\
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_raw_product»
        [from_cv left;from_cv right]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_raw_product_unfold]
  >> simp
       [registered_case10173_fs_hist_raw_product_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule registered_case10173_fs_raw_interval_mul_result_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_interval_neg_hist_raw_product_eval:
  bounded_object_fs_raw_interval_mul left right = SOME product /\
  bounded_object_fs_interval_neg product = SOME result /\
  5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg»
        [App «candle_cv_fs_hist_raw_product»
          [from_cv left;from_cv right]]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_neg» [from_cv product]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> simp [registered_case10173_fs_hist_raw_product_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
  >> simp []
QED

Definition registered_case10173_fs_hist_delta_x4_value_block_body_def:
  registered_case10173_fs_hist_delta_x4_value_block_body =
    Let «x0»
      (App «candle_cv_fs_interval_lookup» [Num 0;Var «environment»])
      (Let «x1»
        (App «candle_cv_fs_interval_lookup» [Num 1;Var «environment»])
        (Let «x2»
          (App «candle_cv_fs_interval_lookup» [Num 2;Var «environment»])
          (Let «x3»
            (App «candle_cv_fs_interval_lookup» [Num 3;Var «environment»])
            (Let «x4»
              (App «candle_cv_fs_interval_lookup» [Num 4;Var «environment»])
              (Let «x5»
                (App «candle_cv_fs_interval_lookup» [Num 5;Var «environment»])
                (Let «linear»
                  (App «candle_cv_fs_angle_interval_sum»
                    [App «candle_cv_fs_angle_six»
                      [App «candle_cv_fs_interval_neg» [Var «x0»];
                       Var «x1»;Var «x2»;
                       App «candle_cv_fs_interval_neg» [Var «x3»];
                       Var «x4»;Var «x5»]])
                  (Let «raw»
                    (App «candle_cv_fs_angle_interval_sum»
                      [App «candle_cv_fs_angle_six»
                        [App «candle_cv_fs_interval_neg»
                          [App «candle_cv_fs_hist_raw_product»
                            [Var «x1»;Var «x2»]];
                         App «candle_cv_fs_interval_neg»
                          [App «candle_cv_fs_hist_raw_product»
                            [Var «x0»;Var «x3»]];
                         App «candle_cv_fs_hist_raw_product»
                          [Var «x1»;Var «x4»];
                         App «candle_cv_fs_hist_raw_product»
                          [Var «x2»;Var «x5»];
                         App «candle_cv_fs_interval_neg»
                          [App «candle_cv_fs_hist_raw_product»
                            [Var «x4»;Var «x5»]];
                         App «candle_cv_fs_hist_raw_product»
                          [Var «x0»;Var «linear»]]])
                    (App «candle_cv_fs_raw_interval_round»
                      [App «candle_cv_fs_scale» [];Var «raw»]))))))))
End

Theorem registered_case10173_fs_hist_delta_x4_value_block_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_delta_x4_value_block» =
    SOME
      ([«environment»],
       registered_case10173_fs_hist_delta_x4_value_block_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_delta_x4_value_block_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_value_block»
        [from_cv environment]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«environment»,from_cv environment)]
        registered_case10173_fs_hist_delta_x4_value_block_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_delta_x4_value_block_lookup]
QED

Theorem registered_case10173_fs_hist_delta_x4_value_block_trace_eval:
  bounded_object_fs_interval_neg x0 = SOME negative_x0 /\
  bounded_object_fs_interval_neg x3 = SOME negative_x3 /\
  registered_case10173_fs_interval_sum_object
      [negative_x0;x1;x2;negative_x3;x4;x5] = SOME linear /\
  bounded_object_fs_raw_interval_mul x1 x2 = SOME p12 /\
  bounded_object_fs_interval_neg p12 = SOME negative_p12 /\
  bounded_object_fs_raw_interval_mul x0 x3 = SOME p03 /\
  bounded_object_fs_interval_neg p03 = SOME negative_p03 /\
  bounded_object_fs_raw_interval_mul x1 x4 = SOME p14 /\
  bounded_object_fs_raw_interval_mul x2 x5 = SOME p25 /\
  bounded_object_fs_raw_interval_mul x4 x5 = SOME p45 /\
  bounded_object_fs_interval_neg p45 = SOME negative_p45 /\
  bounded_object_fs_raw_interval_mul x0 linear = SOME p0l /\
  registered_case10173_fs_interval_sum_object
      [negative_p12;negative_p03;p14;p25;negative_p45;p0l] =
    SOME raw /\
  bounded_object_fs_raw_interval_round 1000000000000 raw = SOME result /\
  29 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_value_block»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_delta_x4_value_block_unfold]
  >> simp
       [registered_case10173_fs_hist_delta_x4_value_block_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x0`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x1`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x2`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x3`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x4`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x5`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv linear`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_angle_six_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac
           [`negative_x0`,`x1`,`x2`,`negative_x3`,`x4`,`x5`]
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv raw`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_angle_six_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac
           [`negative_p12`,`negative_p03`,`p14`,`p25`,`negative_p45`,`p0l`]
      >> simp [registered_case10173_fs_interval_neg_hist_raw_product_eval]
      >> rpt conj_tac
      >> irule registered_case10173_fs_hist_raw_product_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule registered_case10173_fs_round_scale_result_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_fs_hist_delta_x4_value_block_object_def:
  registered_case10173_fs_hist_delta_x4_value_block_object environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      (case bounded_object_fs_interval_neg x0 of
      | NONE => NONE
      | SOME negative_x0 =>
        case bounded_object_fs_interval_neg x3 of
        | NONE => NONE
        | SOME negative_x3 =>
          case registered_case10173_fs_interval_sum_object
              [negative_x0;x1;x2;negative_x3;x4;x5] of
          | NONE => NONE
          | SOME linear =>
            case bounded_object_fs_raw_interval_mul x1 x2 of
            | NONE => NONE
            | SOME p12 =>
              case bounded_object_fs_interval_neg p12 of
              | NONE => NONE
              | SOME negative_p12 =>
                case bounded_object_fs_raw_interval_mul x0 x3 of
                | NONE => NONE
                | SOME p03 =>
                  case bounded_object_fs_interval_neg p03 of
                  | NONE => NONE
                  | SOME negative_p03 =>
                    case bounded_object_fs_raw_interval_mul x1 x4 of
                    | NONE => NONE
                    | SOME p14 =>
                      case bounded_object_fs_raw_interval_mul x2 x5 of
                      | NONE => NONE
                      | SOME p25 =>
                        case bounded_object_fs_raw_interval_mul x4 x5 of
                        | NONE => NONE
                        | SOME p45 =>
                          case bounded_object_fs_interval_neg p45 of
                          | NONE => NONE
                          | SOME negative_p45 =>
                            case bounded_object_fs_raw_interval_mul x0 linear of
                            | NONE => NONE
                            | SOME p0l =>
                              case registered_case10173_fs_interval_sum_object
                                  [negative_p12;negative_p03;p14;p25;
                                   negative_p45;p0l] of
                              | NONE => NONE
                              | SOME raw =>
                                  bounded_object_fs_raw_interval_round
                                    1000000000000 raw)
    | _ => NONE
End

Theorem registered_case10173_fs_hist_delta_x4_value_block_object_eval:
  registered_case10173_fs_hist_delta_x4_value_block_object environment =
      SOME result /\
  29 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_value_block»
        [from_cv (registered_case10173_cv_list environment)])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> fs [registered_case10173_fs_hist_delta_x4_value_block_object_def]
  >> every_case_tac
  >> gvs []
  >> irule registered_case10173_fs_hist_delta_x4_value_block_trace_eval
  >> simp []
QED

Definition registered_case10173_interval_ints_sum_def:
  registered_case10173_interval_ints_sum ([]:cv list) = SOME (0:int,0:int) /\
  registered_case10173_interval_ints_sum (value::values) =
    case bounded_object_interval_ints value of
    | NONE => NONE
    | SOME (lower,upper) =>
      case registered_case10173_interval_ints_sum values of
      | NONE => NONE
      | SOME (rest_lower,rest_upper) =>
          SOME (lower + rest_lower,upper + rest_upper)
End

Theorem bounded_object_fs_canonical_signed_value_exists:
  !raw value.
  bounded_object_signed_int raw = SOME value ==>
  ?result.
    bounded_object_fs_canonical raw = SOME result /\
    bounded_object_signed_int result = SOME value
Proof
  rpt gen_tac
  >> Cases_on `raw`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_canonical_def]
  >> Cases_on `n < n'`
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_fs_add_signed_value_exists:
  !left right left_value right_value.
  bounded_object_signed_int left = SOME left_value /\
  bounded_object_signed_int right = SOME right_value ==>
  ?result.
    bounded_object_fs_add left right = SOME result /\
    bounded_object_signed_int result = SOME (left_value + right_value)
Proof
  rpt gen_tac
  >> strip_tac
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_add_signed_value
  >> imp_res_tac bounded_object_fs_canonical_signed_value_exists
  >> fs [compute_boundedObjectDecimalAddTheory.bounded_object_fs_add_def]
QED

Theorem bounded_object_fs_interval_add_signed_values_exists:
  !left right left_lower left_upper right_lower right_upper.
  bounded_object_interval_ints left = SOME (left_lower,left_upper) /\
  bounded_object_interval_ints right = SOME (right_lower,right_upper) ==>
  ?result.
    bounded_object_fs_interval_add left right = SOME result /\
    bounded_object_interval_ints result =
      SOME (left_lower + right_lower,left_upper + right_upper)
Proof
  rpt gen_tac
  >> Cases_on `left`
  >> Cases_on `right`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def]
  >> strip_tac
  >> mp_tac
       (Q.SPECL [`c`,`c'`,`left_lower`,`right_lower`]
          bounded_object_fs_add_signed_value_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `lower_result` strip_assume_tac)
  >> mp_tac
       (Q.SPECL [`c0`,`c0'`,`left_upper`,`right_upper`]
          bounded_object_fs_add_signed_value_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `upper_result` strip_assume_tac)
  >> qexists_tac `Pair lower_result upper_result`
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def]
QED

Theorem registered_case10173_interval_sum_object_signed_values:
  !lower upper.
    registered_case10173_interval_ints_sum values = SOME (lower,upper) ==>
    ?result.
      registered_case10173_fs_interval_sum_object values = SOME result /\
      bounded_object_interval_ints result = SOME (lower,upper)
Proof
  Induct_on `values`
  >- simp
       [registered_case10173_interval_ints_sum_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_sum_object_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_interval_zero_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> rpt gen_tac
  >> rw
       [registered_case10173_interval_ints_sum_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_sum_object_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> imp_res_tac bounded_object_fs_interval_add_signed_values_exists
  >> metis_tac []
QED

Theorem bounded_interval64_sum_aux_endpoint_values:
  !accumulator result.
    bounded_interval64_sum_aux values accumulator = SOME result ==>
    ?lower upper.
      registered_case10173_interval_ints_sum
        (MAP bounded_interval64_object_cv values) = SOME (lower,upper) /\
      bounded_signed64_to_int (bounded_interval64_lower result) =
        bounded_signed64_to_int (bounded_interval64_lower accumulator) + lower /\
      bounded_signed64_to_int (bounded_interval64_upper result) =
        bounded_signed64_to_int (bounded_interval64_upper accumulator) + upper
Proof
  Induct_on `values`
  >- (rw
       [compute_boundedDeltaTaylorTheory.bounded_interval64_sum_aux_def,
        registered_case10173_interval_ints_sum_def]
      >> qexistsl_tac [`0`,`0`]
      >> simp [])
  >> rpt gen_tac
  >> rw [compute_boundedDeltaTaylorTheory.bounded_interval64_sum_aux_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedIntervalAddTheory.bounded_interval64_add_value
  >> res_tac
  >> qexistsl_tac
       [`bounded_signed64_to_int (bounded_interval64_lower h) + lower`,
        `bounded_signed64_to_int (bounded_interval64_upper h) + upper`]
  >> simp
       [registered_case10173_interval_ints_sum_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_object_cv]
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_sum_endpoint_values:
  bounded_interval64_sum values = SOME result ==>
  registered_case10173_interval_ints_sum
      (MAP bounded_interval64_object_cv values) =
    SOME
      (bounded_signed64_to_int (bounded_interval64_lower result),
       bounded_signed64_to_int (bounded_interval64_upper result))
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_interval64_sum_def]
  >> imp_res_tac bounded_interval64_sum_aux_endpoint_values
  >> fs
       [compute_boundedIntervalListTheory.bounded_interval64_zero_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
QED

Theorem bounded_interval64_sum_aux_valid:
  !accumulator result.
    bounded_interval64_valid accumulator /\
    bounded_interval64_sum_aux values accumulator = SOME result ==>
    bounded_interval64_valid result
Proof
  Induct_on `values`
  >> rw [compute_boundedDeltaTaylorTheory.bounded_interval64_sum_aux_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedIntervalAddTheory.bounded_interval64_add_value
  >> res_tac
QED

Theorem bounded_interval64_sum_valid:
  bounded_interval64_sum values = SOME result ==>
  bounded_interval64_valid result
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_interval64_sum_def]
  >> match_mp_tac
       (Q.SPECL [`bounded_interval64_zero`,`result`]
         (Q.INST [`values` |-> `values`]
            bounded_interval64_sum_aux_valid))
  >> simp
       [compute_boundedIntervalListTheory.bounded_interval64_zero_valid]
QED

Theorem bounded_object_fs_interval_add_target_object_cv:
  !left right left_lower left_upper right_lower right_upper
   target_lower target_upper.
    bounded_object_interval_ints left = SOME (left_lower,left_upper) /\
    bounded_object_interval_ints right = SOME (right_lower,right_upper) /\
    bounded_signed64_normalized target_lower /\
    bounded_signed64_normalized target_upper /\
    bounded_signed64_to_int target_lower = left_lower + right_lower /\
    bounded_signed64_to_int target_upper = left_upper + right_upper ==>
    bounded_object_fs_interval_add left right =
      SOME
        (bounded_interval64_object_cv
          (BoundedInterval64 target_lower target_upper))
Proof
  rpt gen_tac
  >> Cases_on `left`
  >> Cases_on `right`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def]
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`left` |-> `c`, `right` |-> `c'`,
          `left_value` |-> `left_lower`,
          `right_value` |-> `right_lower`]
         compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_add_signed_value)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `raw_lower` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`left` |-> `c0`, `right` |-> `c0'`,
          `left_value` |-> `left_upper`,
          `right_value` |-> `right_upper`]
         compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_add_signed_value)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `raw_upper` strip_assume_tac)
  >> `bounded_object_fs_canonical raw_lower =
        SOME (bounded_signed64_object_cv target_lower)` by
       (irule
          compute_boundedObjectDecimalAddTheory.bounded_object_fs_canonical_object_cv
        >> simp [])
  >> `bounded_object_fs_canonical raw_upper =
        SOME (bounded_signed64_object_cv target_upper)` by
       (irule
          compute_boundedObjectDecimalAddTheory.bounded_object_fs_canonical_object_cv
        >> simp [])
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_add_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def]
QED

Theorem registered_case10173_interval_sum_object_typed_exact:
  bounded_interval64_sum (value::values) = SOME result ==>
  registered_case10173_fs_interval_sum_object
      (MAP bounded_interval64_object_cv (value::values)) =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> imp_res_tac bounded_interval64_sum_endpoint_values
  >> imp_res_tac bounded_interval64_sum_valid
  >> fs
       [registered_case10173_interval_ints_sum_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_object_cv]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_interval_sum_object_signed_values
  >> fs
       [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_sum_object_def]
  >> Cases_on `result`
  >> fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> irule bounded_object_fs_interval_add_target_object_cv
  >> simp []
QED

Theorem bounded_object_fs_interval_neg_signed_values_exists:
  !source lower upper.
    bounded_object_interval_ints source = SOME (lower,upper) ==>
    ?result.
      bounded_object_fs_interval_neg source = SOME result /\
      bounded_object_interval_ints result = SOME (-upper,-lower)
Proof
  rpt gen_tac
  >> Cases_on `source`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def]
  >> strip_tac
  >> mp_tac
       (Q.INST [`source` |-> `c0`, `value` |-> `upper`]
          compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_neg_signed_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `negative_upper` strip_assume_tac)
  >> mp_tac
       (Q.INST [`source` |-> `c`, `value` |-> `lower`]
          compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_neg_signed_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `negative_lower` strip_assume_tac)
  >> qexists_tac `Pair negative_upper negative_lower`
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_neg_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def]
QED

Theorem bounded_object_fs_raw_interval_mul_ints_exists:
  !left right left_lower left_upper right_lower right_upper.
    bounded_object_interval_ints left = SOME (left_lower,left_upper) /\
    bounded_object_interval_ints right = SOME (right_lower,right_upper) ==>
    ?result.
      bounded_object_fs_raw_interval_mul left right = SOME result /\
      bounded_object_interval_ints result =
        SOME
          (bounded_object_int_min4
             (left_lower * right_lower) (left_lower * right_upper)
             (left_upper * right_lower) (left_upper * right_upper),
           bounded_object_int_max4
             (left_lower * right_lower) (left_lower * right_upper)
             (left_upper * right_lower) (left_upper * right_upper))
Proof
  rpt gen_tac
  >> Cases_on `left`
  >> Cases_on `right`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def]
  >> rename1
       `bounded_object_fs_raw_interval_mul
          (Pair left_lower_object left_upper_object)
          (Pair right_lower_object right_upper_object) = _`
  >> strip_tac
  >> mp_tac
       (Q.SPECL
         [`right_upper`,`right_upper_object`,
          `right_lower`,`right_lower_object`,
          `left_upper`,`left_upper_object`,
          `left_lower`,`left_lower_object`]
         (GEN_ALL
           compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_mul_general_exists))
  >> impl_tac >- simp []
  >> disch_then
       (qx_choose_then `result_lower`
         (qx_choose_then `result_upper` assume_tac))
  >> qexists_tac `Pair result_lower result_upper`
  >> conj_tac >- simp []
  >> mp_tac
       (Q.SPECL
         [`result_upper`,`right_upper`,`right_upper_object`,
          `right_lower`,`right_lower_object`,`result_lower`,
          `left_upper`,`left_upper_object`,
          `left_lower`,`left_lower_object`]
         (GEN_ALL
           compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_mul_general_signed_values))
  >> impl_tac >- simp []
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def]
QED

Theorem bounded_object_int_negated_left_product_extrema:
  bounded_object_int_min4
      ((-left_upper) * right_lower) ((-left_upper) * right_upper)
      ((-left_lower) * right_lower) ((-left_lower) * right_upper) =
    -bounded_object_int_max4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) /\
  bounded_object_int_max4
      ((-left_upper) * right_lower) ((-left_upper) * right_upper)
      ((-left_lower) * right_lower) ((-left_lower) * right_upper) =
    -bounded_object_int_min4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper)
Proof
  rw
    [compute_boundedObjectDecimalIntervalTheory.bounded_object_int_min4_def,
     compute_boundedObjectDecimalIntervalTheory.bounded_object_int_max4_def,
     compute_boundedObjectDecimalIntervalTheory.bounded_object_int_min_def,
     compute_boundedObjectDecimalIntervalTheory.bounded_object_int_max_def]
  >> every_case_tac
  >> simp [integerTheory.INT_NEG_MUL2]
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_raw_product_ints_def:
  registered_case10173_raw_product_ints
      (BoundedInterval64 left_lower left_upper)
      (BoundedInterval64 right_lower right_upper) =
    (bounded_object_int_min4
       (bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_lower)
       (bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_upper)
       (bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_lower)
       (bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_upper),
     bounded_object_int_max4
       (bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_lower)
       (bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_upper)
       (bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_lower)
       (bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_upper))
End

Theorem registered_case10173_raw_product_endpoint_values:
  !left right raw_product.
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv left)
        (bounded_interval64_object_cv right) = SOME raw_product ==>
    bounded_object_interval_ints raw_product =
      SOME (registered_case10173_raw_product_ints left right)
Proof
  rpt gen_tac
  >> strip_tac
  >> mp_tac
       (Q.SPECL
         [`bounded_interval64_object_cv left`,
          `bounded_interval64_object_cv right`,
          `bounded_signed64_to_int (bounded_interval64_lower left)`,
          `bounded_signed64_to_int (bounded_interval64_upper left)`,
          `bounded_signed64_to_int (bounded_interval64_lower right)`,
          `bounded_signed64_to_int (bounded_interval64_upper right)`]
         bounded_object_fs_raw_interval_mul_ints_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `computed_raw_product` strip_assume_tac)
  >> gvs []
  >> Cases_on `left`
  >> Cases_on `right`
  >> fs
       [registered_case10173_raw_product_ints_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Theorem registered_case10173_negated_raw_product_endpoint_values:
  !left right raw_product negative_product.
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv left)
        (bounded_interval64_object_cv right) = SOME raw_product /\
    bounded_object_fs_interval_neg raw_product = SOME negative_product ==>
    bounded_object_interval_ints negative_product =
      SOME
        (registered_case10173_raw_product_ints
          (bounded_interval64_neg left) right)
Proof
  rpt gen_tac
  >> strip_tac
  >> imp_res_tac registered_case10173_raw_product_endpoint_values
  >> mp_tac
       (Q.SPECL
         [`raw_product`,
          `FST (registered_case10173_raw_product_ints left right)`,
          `SND (registered_case10173_raw_product_ints left right)`]
         bounded_object_fs_interval_neg_signed_values_exists)
  >> impl_tac >- simp []
  >> disch_then
       (qx_choose_then `computed_negative_product` strip_assume_tac)
  >> gvs []
  >> Cases_on `left`
  >> Cases_on `right`
  >> fs
       [registered_case10173_raw_product_ints_def,
        compute_boundedIntervalAddTheory.bounded_interval64_neg_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_value,
        bounded_object_int_negated_left_product_extrema]
QED

Definition registered_case10173_raw_products_ints_sum_def:
  registered_case10173_raw_products_ints_sum
      ([]:(bounded_interval64 # bounded_interval64) list) = (0:int,0:int) /\
  registered_case10173_raw_products_ints_sum ((left,right)::products) =
    let current = registered_case10173_raw_product_ints left right;
        rest = registered_case10173_raw_products_ints_sum products
    in
      (FST current + FST rest,SND current + SND rest)
End

Theorem bounded_object_fs_raw_interval_add_ints_exists:
  !left right left_lower left_upper right_lower right_upper.
    bounded_object_interval_ints left = SOME (left_lower,left_upper) /\
    bounded_object_interval_ints right = SOME (right_lower,right_upper) ==>
    ?result.
      bounded_object_fs_raw_interval_add left right = SOME result /\
      bounded_object_interval_ints result =
        SOME (left_lower + right_lower,left_upper + right_upper)
Proof
  rpt gen_tac
  >> Cases_on `left`
  >> Cases_on `right`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def]
  >> rename1
       `bounded_object_fs_raw_interval_add
          (Pair left_lower_object left_upper_object)
          (Pair right_lower_object right_upper_object) = _`
  >> strip_tac
  >> mp_tac
       (Q.SPECL
         [`right_upper`,`right_upper_object`,
          `right_lower`,`right_lower_object`,
          `left_upper`,`left_upper_object`,
          `left_lower`,`left_lower_object`]
         (GEN_ALL
           compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_interval_add_signed_values))
  >> impl_tac >- simp []
  >> disch_then
       (qx_choose_then `result_lower`
         (qx_choose_then `result_upper` strip_assume_tac))
  >> qexists_tac `Pair result_lower result_upper`
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def]
QED

Theorem bounded_object_fs_raw_products_acc_endpoint_values:
  !accumulator accumulator_lower accumulator_upper.
    bounded_object_interval_ints accumulator =
      SOME (accumulator_lower,accumulator_upper) ==>
    ?result.
      bounded_object_fs_raw_products_acc products accumulator = SOME result /\
      bounded_object_interval_ints result =
        SOME
          (accumulator_lower +
             FST (registered_case10173_raw_products_ints_sum products),
           accumulator_upper +
             SND (registered_case10173_raw_products_ints_sum products))
Proof
  Induct_on `products`
  >- (rpt gen_tac
      >> strip_tac
      >> qexists_tac `accumulator`
      >> simp
           [compute_boundedObjectDecimalFusedTheory.bounded_object_fs_raw_products_acc_def,
            registered_case10173_raw_products_ints_sum_def])
  >> gen_tac
  >> PairCases_on `h`
  >> rpt gen_tac
  >> strip_tac
  >> mp_tac
       (Q.SPECL
         [`bounded_interval64_object_cv h0`,
          `bounded_interval64_object_cv h1`,
          `bounded_signed64_to_int (bounded_interval64_lower h0)`,
          `bounded_signed64_to_int (bounded_interval64_upper h0)`,
          `bounded_signed64_to_int (bounded_interval64_lower h1)`,
          `bounded_signed64_to_int (bounded_interval64_upper h1)`]
         bounded_object_fs_raw_interval_mul_ints_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `raw_product` strip_assume_tac)
  >> mp_tac
       (Q.SPECL
         [`accumulator`,`raw_product`,
          `accumulator_lower`,`accumulator_upper`,
          `FST (registered_case10173_raw_product_ints h0 h1)`,
          `SND (registered_case10173_raw_product_ints h0 h1)`]
         bounded_object_fs_raw_interval_add_ints_exists)
  >> impl_tac
  >- (simp
       [registered_case10173_raw_product_ints_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
      >> Cases_on `h0`
      >> Cases_on `h1`
      >> fs
           [registered_case10173_raw_product_ints_def,
            compute_boundedIntervalTheory.bounded_interval64_lower_def,
            compute_boundedIntervalTheory.bounded_interval64_upper_def])
  >> disch_then (qx_choose_then `next` strip_assume_tac)
  >> qpat_x_assum
       `!accumulator accumulator_lower accumulator_upper. _`
       (mp_tac o Q.SPECL
         [`next`,
          `accumulator_lower +
             FST (registered_case10173_raw_product_ints h0 h1)`,
          `accumulator_upper +
             SND (registered_case10173_raw_product_ints h0 h1)`])
  >> simp []
  >> disch_then (qx_choose_then `result` strip_assume_tac)
  >> qexists_tac `result`
  >> simp
       [compute_boundedObjectDecimalFusedTheory.bounded_object_fs_raw_products_acc_def,
        registered_case10173_raw_products_ints_sum_def,
        LET_THM]
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_fs_raw_products_endpoint_values:
  !products raw.
    bounded_object_fs_raw_products_acc products
        (Pair (Pair (Num 0) (Num 0)) (Pair (Num 0) (Num 0))) = SOME raw ==>
    bounded_object_interval_ints raw =
      SOME (registered_case10173_raw_products_ints_sum products)
Proof
  rpt gen_tac
  >> strip_tac
  >> mp_tac
       (Q.SPECL
         [`Pair (Pair (Num 0) (Num 0)) (Pair (Num 0) (Num 0))`,
          `0`,`0`]
         (Q.INST [`products` |-> `products`]
            bounded_object_fs_raw_products_acc_endpoint_values))
  >> impl_tac
  >- simp
       [compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> disch_then (qx_choose_then `computed_raw` strip_assume_tac)
  >> gvs []
QED

Theorem bounded_object_fs_raw_interval_round_ints_extensional:
  !raw_left raw_right lower upper denominator.
    bounded_object_interval_ints raw_left = SOME (lower,upper) /\
    bounded_object_interval_ints raw_right = SOME (lower,upper) ==>
    bounded_object_fs_raw_interval_round denominator raw_left =
    bounded_object_fs_raw_interval_round denominator raw_right
Proof
  rpt gen_tac
  >> strip_tac
  >> Cases_on `raw_left`
  >> Cases_on `raw_right`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def]
  >> irule
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_extensional
  >> simp []
QED

Theorem registered_case10173_hist_raw_sum_endpoint_values:
  !x0 x1 x2 x3 x4 x5 linear
   p12 negative_p12 p03 negative_p03 p14 p25 p45 negative_p45 p0l raw.
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv x1)
        (bounded_interval64_object_cv x2) = SOME p12 /\
    bounded_object_fs_interval_neg p12 = SOME negative_p12 /\
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv x0)
        (bounded_interval64_object_cv x3) = SOME p03 /\
    bounded_object_fs_interval_neg p03 = SOME negative_p03 /\
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv x1)
        (bounded_interval64_object_cv x4) = SOME p14 /\
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv x2)
        (bounded_interval64_object_cv x5) = SOME p25 /\
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv x4)
        (bounded_interval64_object_cv x5) = SOME p45 /\
    bounded_object_fs_interval_neg p45 = SOME negative_p45 /\
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv x0)
        (bounded_interval64_object_cv linear) = SOME p0l /\
    registered_case10173_fs_interval_sum_object
        [negative_p12;negative_p03;p14;p25;negative_p45;p0l] = SOME raw ==>
    bounded_object_interval_ints raw =
      SOME
        (registered_case10173_raw_products_ints_sum
          [(bounded_interval64_neg x1,x2);
           (bounded_interval64_neg x0,x3);
           (x1,x4);(x2,x5);
           (bounded_interval64_neg x4,x5);
           (x0,linear)])
Proof
  rpt gen_tac
  >> strip_tac
  >> imp_res_tac
       registered_case10173_negated_raw_product_endpoint_values
  >> imp_res_tac registered_case10173_raw_product_endpoint_values
  >> `registered_case10173_interval_ints_sum
        [negative_p12;negative_p03;p14;p25;negative_p45;p0l] =
      SOME
        (registered_case10173_raw_products_ints_sum
          [(bounded_interval64_neg x1,x2);
           (bounded_interval64_neg x0,x3);
           (x1,x4);(x2,x5);
           (bounded_interval64_neg x4,x5);
           (x0,linear)])` by
       (simp
          [registered_case10173_interval_ints_sum_def,
           registered_case10173_raw_products_ints_sum_def,LET_THM]
        >> Cases_on
             `registered_case10173_raw_product_ints
                (bounded_interval64_neg x1) x2`
        >> Cases_on
             `registered_case10173_raw_product_ints
                (bounded_interval64_neg x0) x3`
        >> Cases_on `registered_case10173_raw_product_ints x1 x4`
        >> Cases_on `registered_case10173_raw_product_ints x2 x5`
        >> Cases_on
             `registered_case10173_raw_product_ints
                (bounded_interval64_neg x4) x5`
        >> Cases_on `registered_case10173_raw_product_ints x0 linear`
        >> simp [])
  >> mp_tac
       (Q.SPECL
         [`FST
             (registered_case10173_raw_products_ints_sum
               [(bounded_interval64_neg x1,x2);
                (bounded_interval64_neg x0,x3);
                (x1,x4);(x2,x5);
                (bounded_interval64_neg x4,x5);
                (x0,linear)])`,
          `SND
             (registered_case10173_raw_products_ints_sum
               [(bounded_interval64_neg x1,x2);
                (bounded_interval64_neg x0,x3);
                (x1,x4);(x2,x5);
                (bounded_interval64_neg x4,x5);
                (x0,linear)])`]
         (Q.INST
           [`values` |->
              `[negative_p12;negative_p03;p14;p25;negative_p45;p0l]`]
           registered_case10173_interval_sum_object_signed_values))
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `computed_raw` strip_assume_tac)
  >> gvs []
QED

val _ = export_theory ();
