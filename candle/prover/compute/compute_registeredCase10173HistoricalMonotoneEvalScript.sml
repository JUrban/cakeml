(*****************************************************************************
 * Registered evaluator semantics for historical monotone box selection.
 *
 * The source selects one endpoint of each box when the corresponding
 * derivative has a known sign, and otherwise preserves the whole interval.
 * This theory proves the literal registered implementation against the typed
 * six-coordinate bounded model used by the genuine second-order checker.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalMonotoneEval
Ancestors
  compute_registeredCase10173HistoricalDeltaX4HessianEval
  compute_registeredCase10173HistoricalUPointsEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_monotone_coordinate_body_def:
  registered_case10173_fs_hist_monotone_coordinate_body =
    Let «box»
      (App «candle_cv_fs_interval_lookup»
        [Var «coordinate»;Var «boxes»])
      (Let «derivative_value»
        (App «candle_cv_fs_interval_lookup»
          [Var «coordinate»;Var «derivatives»])
        (If
          (App «candle_cv_fs_raw_le»
            [App «candle_cv_fs_zero» [];
             Uop Fst (Var «derivative_value»)])
          (App «candle_cv_fs_hist_point»
            [If (Var «upper»)
               (Uop Snd (Var «box»))
               (Uop Fst (Var «box»))])
          (If
            (App «candle_cv_fs_raw_le»
              [Uop Snd (Var «derivative_value»);
               App «candle_cv_fs_zero» []])
            (App «candle_cv_fs_hist_point»
              [If (Var «upper»)
                 (Uop Fst (Var «box»))
                 (Uop Snd (Var «box»))])
            (Var «box»))))
End

Definition registered_case10173_fs_hist_monotone_environment_body_def:
  registered_case10173_fs_hist_monotone_environment_body =
    App «candle_cv_fs_angle_six»
      [App «candle_cv_fs_hist_monotone_coordinate»
        [Num 0;Var «upper»;Var «boxes»;Var «derivatives»];
       App «candle_cv_fs_hist_monotone_coordinate»
        [Num 1;Var «upper»;Var «boxes»;Var «derivatives»];
       App «candle_cv_fs_hist_monotone_coordinate»
        [Num 2;Var «upper»;Var «boxes»;Var «derivatives»];
       App «candle_cv_fs_hist_monotone_coordinate»
        [Num 3;Var «upper»;Var «boxes»;Var «derivatives»];
       App «candle_cv_fs_hist_monotone_coordinate»
        [Num 4;Var «upper»;Var «boxes»;Var «derivatives»];
       App «candle_cv_fs_hist_monotone_coordinate»
        [Num 5;Var «upper»;Var «boxes»;Var «derivatives»]]
End

Theorem registered_case10173_fs_hist_monotone_coordinate_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_monotone_coordinate» =
    SOME
      ([«coordinate»;«upper»;«boxes»;«derivatives»],
       registered_case10173_fs_hist_monotone_coordinate_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_monotone_environment_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_monotone_environment» =
    SOME
      ([«upper»;«boxes»;«derivatives»],
       registered_case10173_fs_hist_monotone_environment_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_monotone_coordinate_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_monotone_coordinate»
        [from_cv coordinate;from_cv upper;from_cv boxes;
         from_cv derivatives]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«coordinate»,from_cv coordinate);
         («upper»,from_cv upper);
         («boxes»,from_cv boxes);
         («derivatives»,from_cv derivatives)]
        registered_case10173_fs_hist_monotone_coordinate_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_fs_hist_monotone_coordinate_lookup]
QED

Theorem registered_case10173_fs_hist_monotone_environment_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_monotone_environment»
        [from_cv upper;from_cv boxes;from_cv derivatives])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«upper»,from_cv upper);
         («boxes»,from_cv boxes);
         («derivatives»,from_cv derivatives)]
        registered_case10173_fs_hist_monotone_environment_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_fs_hist_monotone_environment_lookup]
QED

Theorem registered_case10173_fs_hist_monotone_environment_num_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_monotone_environment»
        [Num (if upper then 1 else 0);from_cv boxes;
         from_cv derivatives]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«upper»,Num (if upper then 1 else 0));
         («boxes»,from_cv boxes);
         («derivatives»,from_cv derivatives)]
        registered_case10173_fs_hist_monotone_environment_body) refs
Proof
  simp_tac std_ss
    [GSYM (CONJUNCT1 compute_execTheory.from_cv_def)]
  >> strip_tac
  >> irule registered_case10173_fs_hist_monotone_environment_unfold
  >> simp []
QED

Theorem registered_case10173_fs_hist_point_selected_endpoint_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_point»
        [If (Num (if select_upper then 1 else 0))
           (Uop Snd (from_cv (Pair lower upper)))
           (Uop Fst (from_cv (Pair lower upper)))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (if select_upper then Pair upper upper else Pair lower lower)),refs)
Proof
  Cases_on `select_upper`
  >- (simp_tac std_ss []
      >> strip_tac
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fs_hist_point» [from_cv upper]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
          >> simp
               [compute_evalTheory.compute_eval_def,
                compute_execTheory.from_cv_def,
                compute_execProofTheory.compute_eval_from_cv,
                compute_evalTheory.do_uop_def,
                compute_evalTheory.do_snd_def,
                ml_monadBaseTheory.st_ex_bind_def,
                ml_monadBaseTheory.st_ex_return_def]
          >> intLib.ARITH_TAC)
      >> irule
           compute_registeredCase10173HistoricalUPointsEvalTheory.registered_case10173_fs_hist_point_object_eval
      >> intLib.ARITH_TAC)
  >> simp_tac std_ss []
  >> strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_point» [from_cv lower]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_execTheory.from_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_fst_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalUPointsEvalTheory.registered_case10173_fs_hist_point_object_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_point_opposite_endpoint_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_point»
        [If (Num (if select_upper then 1 else 0))
           (Uop Fst (from_cv (Pair lower upper)))
           (Uop Snd (from_cv (Pair lower upper)))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (if select_upper then Pair lower lower else Pair upper upper)),refs)
Proof
  Cases_on `select_upper`
  >- (simp_tac std_ss []
      >> strip_tac
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fs_hist_point» [from_cv lower]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
          >> simp
               [compute_evalTheory.compute_eval_def,
                compute_execTheory.from_cv_def,
                compute_execProofTheory.compute_eval_from_cv,
                compute_evalTheory.do_uop_def,
                compute_evalTheory.do_fst_def,
                ml_monadBaseTheory.st_ex_bind_def,
                ml_monadBaseTheory.st_ex_return_def]
          >> intLib.ARITH_TAC)
      >> irule
           compute_registeredCase10173HistoricalUPointsEvalTheory.registered_case10173_fs_hist_point_object_eval
      >> intLib.ARITH_TAC)
  >> simp_tac std_ss []
  >> strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_point» [from_cv upper]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_execTheory.from_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_snd_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalUPointsEvalTheory.registered_case10173_fs_hist_point_object_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_point_selected_typed_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_point»
        [If (Num (if select_upper then 1 else 0))
           (Uop Snd (from_cv (bounded_interval64_object_cv value)))
           (Uop Fst (from_cv (bounded_interval64_object_cv value)))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (if select_upper then bounded_historical_point_upper value
           else bounded_historical_point_lower value))),refs)
Proof
  Cases_on `value`
  >> Cases_on `select_upper`
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_lower_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_upper_def]
  >> simp_tac std_ss
       [GSYM (CONJUNCT2 compute_execTheory.from_cv_def)]
  >> strip_tac
  >> metis_tac [registered_case10173_fs_hist_point_selected_endpoint_eval]
QED

Theorem registered_case10173_fs_hist_point_opposite_typed_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_point»
        [If (Num (if select_upper then 1 else 0))
           (Uop Fst (from_cv (bounded_interval64_object_cv value)))
           (Uop Snd (from_cv (bounded_interval64_object_cv value)))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (if select_upper then bounded_historical_point_lower value
           else bounded_historical_point_upper value))),refs)
Proof
  Cases_on `value`
  >> Cases_on `select_upper`
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_lower_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_upper_def]
  >> simp_tac std_ss
       [GSYM (CONJUNCT2 compute_execTheory.from_cv_def)]
  >> strip_tac
  >> metis_tac [registered_case10173_fs_hist_point_opposite_endpoint_eval]
QED

Theorem registered_case10173_fs_raw_le_zero_interval_lower_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_le»
        [App «candle_cv_fs_zero» [];
         Uop Fst (from_cv (bounded_interval64_object_cv derivative))])
      (refs:hol_refs) =
    (M_success
      (Num
        (if bounded_signed64_nonnegative
              (bounded_interval64_lower derivative) then 1 else 0)),refs)
Proof
  Cases_on `derivative`
  >> strip_tac
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalUPointsEvalTheory.registered_case10173_fs_raw_le_zero_fst_pair_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> once_rewrite_tac
       [GSYM
          (SIMP_RULE (srw_ss()) []
            (Q.SPECL [`F`,`0w`]
              compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def))]
  >> simp
       [compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_le_object_cv,
        compute_boundedObjectHistoricalSecondDecimalTheory.bounded_signed64_zero_le_iff_nonnegative]
QED

Theorem registered_case10173_fs_raw_le_interval_upper_zero_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_le»
        [Uop Snd (from_cv (bounded_interval64_object_cv derivative));
         App «candle_cv_fs_zero» []]) (refs:hol_refs) =
    (M_success
      (Num
        (if bounded_signed64_nonpositive
              (bounded_interval64_upper derivative) then 1 else 0)),refs)
Proof
  Cases_on `derivative`
  >> strip_tac
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalUPointsEvalTheory.registered_case10173_fs_raw_le_snd_pair_zero_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> once_rewrite_tac
       [GSYM
          (SIMP_RULE (srw_ss()) []
            (Q.SPECL [`F`,`0w`]
              compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def))]
  >> simp
       [compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_le_object_cv,
        compute_boundedObjectHistoricalSecondDecimalTheory.bounded_signed64_le_zero_iff_nonpositive]
QED

Theorem registered_case10173_fs_hist_monotone_coordinate_typed_eval:
  index < LENGTH boxes /\
  index < LENGTH derivatives /\
  index + 20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_monotone_coordinate»
        [from_cv (Num index);
         from_cv (Num (if upper then 1 else 0));
         from_cv (bounded_interval64_object_cv_list boxes);
         from_cv (bounded_interval64_object_cv_list derivatives)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (bounded_historical_monotone_coordinate
            (EL index boxes) (EL index derivatives) upper))),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_monotone_coordinate_unfold]
  >> simp
       [registered_case10173_fs_hist_monotone_coordinate_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv (EL index boxes))`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_fs_interval_lookup_num_object_list_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv (EL index derivatives))`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_fs_interval_lookup_num_object_list_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 3)
          registered_case10173_historical_chunk16_ceqs
          (if
             bounded_signed64_nonnegative
               (bounded_interval64_lower (EL index derivatives))
           then
             App «candle_cv_fs_hist_point»
               [If (Num (if upper then 1 else 0))
                  (Uop Snd
                    (from_cv
                      (bounded_interval64_object_cv (EL index boxes))))
                  (Uop Fst
                    (from_cv
                      (bounded_interval64_object_cv (EL index boxes))))]
           else
             If
               (App «candle_cv_fs_raw_le»
                 [Uop Snd
                    (from_cv
                      (bounded_interval64_object_cv
                        (EL index derivatives)));
                  App «candle_cv_fs_zero» []])
               (App «candle_cv_fs_hist_point»
                 [If (Num (if upper then 1 else 0))
                    (Uop Fst
                      (from_cv
                        (bounded_interval64_object_cv (EL index boxes))))
                    (Uop Snd
                      (from_cv
                        (bounded_interval64_object_cv (EL index boxes))))])
               (from_cv
                 (bounded_interval64_object_cv (EL index boxes)))) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_compute_eval_if_bool
      >> irule registered_case10173_fs_raw_le_zero_interval_lower_eval
      >> intLib.ARITH_TAC)
  >> Cases_on
       `bounded_signed64_nonnegative
          (bounded_interval64_lower (EL index derivatives))`
  >- (simp
        [compute_boundedHistoricalDihedralSecondTheory.bounded_historical_monotone_coordinate_def]
      >> irule registered_case10173_fs_hist_point_selected_typed_eval
      >> intLib.ARITH_TAC)
  >> simp []
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 3)
          registered_case10173_historical_chunk16_ceqs
          (if
             bounded_signed64_nonpositive
               (bounded_interval64_upper (EL index derivatives))
           then
             App «candle_cv_fs_hist_point»
               [If (Num (if upper then 1 else 0))
                  (Uop Fst
                    (from_cv
                      (bounded_interval64_object_cv (EL index boxes))))
                  (Uop Snd
                    (from_cv
                      (bounded_interval64_object_cv (EL index boxes))))]
           else
             from_cv
               (bounded_interval64_object_cv (EL index boxes))) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_compute_eval_if_bool
      >> irule registered_case10173_fs_raw_le_interval_upper_zero_eval
      >> intLib.ARITH_TAC)
  >> Cases_on
       `bounded_signed64_nonpositive
          (bounded_interval64_upper (EL index derivatives))`
  >- (simp
        [compute_boundedHistoricalDihedralSecondTheory.bounded_historical_monotone_coordinate_def]
      >> irule registered_case10173_fs_hist_point_opposite_typed_eval
      >> intLib.ARITH_TAC)
  >> simp
       [compute_boundedHistoricalDihedralSecondTheory.bounded_historical_monotone_coordinate_def,
        compute_execProofTheory.compute_eval_from_cv]
QED

Theorem registered_case10173_fs_hist_monotone_coordinate_num_typed_eval:
  index < LENGTH boxes /\
  index < LENGTH derivatives /\
  index + 20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_monotone_coordinate»
        [Num index;Num (if upper then 1 else 0);
         from_cv (bounded_interval64_object_cv_list boxes);
         from_cv (bounded_interval64_object_cv_list derivatives)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (bounded_historical_monotone_coordinate
            (EL index boxes) (EL index derivatives) upper))),refs)
Proof
  rpt strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_monotone_coordinate_typed_eval)
  >> simp []
QED

Theorem registered_case10173_fs_hist_monotone_coordinate_at_typed_eval:
  index < LENGTH boxes /\
  index < LENGTH derivatives /\
  EL index boxes = box /\
  EL index derivatives = derivative /\
  index + 20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_monotone_coordinate»
        [Num index;Num (if upper then 1 else 0);
         from_cv (bounded_interval64_object_cv_list boxes);
         from_cv (bounded_interval64_object_cv_list derivatives)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (bounded_historical_monotone_coordinate
            box derivative upper))),refs)
Proof
  rpt strip_tac
  >> gvs []
  >> irule registered_case10173_fs_hist_monotone_coordinate_num_typed_eval
  >> simp []
QED

Theorem registered_case10173_fs_angle_six_interval_argument_results:
  0 < clock /\
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
      (App «candle_cv_fs_angle_six»
        [argument0;argument1;argument2;
         argument3;argument4;argument5]) refs =
    (M_success
      (from_cv
        (bounded_interval64_object_cv_list
          [r0;r1;r2;r3;r4;r5])),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
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
      >> simp [])
  >> once_rewrite_tac
       [GSYM
          compute_registeredCase10173HistoricalListScaleRefinementTheory.registered_case10173_cv_list_map_bounded_interval64_object_cv]
  >> simp_tac std_ss [listTheory.MAP]
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_monotone_environment_six_typed_eval:
  30 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_monotone_environment»
        [Num (if upper then 1 else 0);
         from_cv
           (bounded_interval64_object_cv_list [b0;b1;b2;b3;b4;b5]);
         from_cv
           (bounded_interval64_object_cv_list [d0;d1;d2;d3;d4;d5])])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv_list
          [bounded_historical_monotone_coordinate b0 d0 upper;
           bounded_historical_monotone_coordinate b1 d1 upper;
           bounded_historical_monotone_coordinate b2 d2 upper;
           bounded_historical_monotone_coordinate b3 d3 upper;
           bounded_historical_monotone_coordinate b4 d4 upper;
           bounded_historical_monotone_coordinate b5 d5 upper])),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_hist_monotone_environment_num_unfold]
  >> simp
       [registered_case10173_fs_hist_monotone_environment_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule registered_case10173_fs_angle_six_interval_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> rpt conj_tac
  >> irule registered_case10173_fs_hist_monotone_coordinate_at_typed_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
