(*****************************************************************************
 * Authenticated evaluator semantics for the generic historical production
 * guard.  This guard is deliberately proved from the accepted decimal packet
 * and its source traces; no closed evaluation of a particular job is used.
 *****************************************************************************)
Theory compute_registeredCase10173ProductionGuardAuthenticatedEval
Ancestors
  compute_registeredCase10173RootRecordAuthenticatedEval
Libs
  bossLib preamble intLib

Definition registered_case10173_hist_positive_interval_body_def:
  registered_case10173_hist_positive_interval_body =
    App «candle_cv_fs_hist_bool_and»
      [Binop Eq (Uop Snd (Uop Fst (Var «value»))) (Num 0);
       App «candle_cv_fs_hist_bool_and»
         [Binop Eq (Uop Snd (Uop Snd (Var «value»))) (Num 0);
          App «candle_cv_fs_hist_bool_and»
            [Binop Less (Num 0) (Uop Fst (Uop Fst (Var «value»)));
             App «candle_cv_fs_hist_num_le»
               [Uop Fst (Uop Fst (Var «value»));
                Uop Fst (Uop Snd (Var «value»))]]]]
End

Theorem registered_case10173_hist_positive_interval_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_positive_interval» =
    SOME ([«value»],registered_case10173_hist_positive_interval_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_positive_interval_eval:
  bounded_interval64_valid value /\
  bounded_signed64_strict_positive (bounded_interval64_lower value) /\
  40 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_interval»
        [from_cv (bounded_interval64_object_cv value)])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  Cases_on `value`
  >> rename1 `BoundedInterval64 lower upper`
  >> Cases_on `lower`
  >> Cases_on `upper`
  >> rename1
       `BoundedInterval64 (BoundedSigned64 lower_negative lower_magnitude)
          (BoundedSigned64 upper_negative upper_magnitude)`
  >> Cases_on `lower_negative`
  >> Cases_on `upper_negative`
  >> rw
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_def]
  >> gvs [wordsTheory.WORD_LO,wordsTheory.w2n_eq_0]
  >> subgoal `0 < w2n lower_magnitude`
  >- simp
       [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,
        wordsTheory.w2n_eq_0]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_hist_positive_interval_lookup,
        registered_case10173_hist_positive_interval_body_def,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_lookup,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_body_def,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_num_le_lookup,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_num_le_body_def,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_not_lookup,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_not_body_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_reln_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Definition registered_case10173_hist_positive_product_body_def:
  registered_case10173_hist_positive_product_body =
    Binop Less (Num 0)
      (Binop Div
        (Binop Mul
          (Uop Fst (Uop Fst (Var «left»)))
          (Uop Fst (Uop Fst (Var «right»))))
        (App «candle_cv_fs_scale» []))
End

Theorem registered_case10173_hist_positive_product_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_positive_product» =
    SOME
      ([«left»;«right»],registered_case10173_hist_positive_product_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_positive_product_eval:
  bounded_signed64_strict_positive (bounded_interval64_lower left) /\
  bounded_signed64_strict_positive (bounded_interval64_lower right) /\
  0 <
    (w2n
       (bounded_signed64_magnitude (bounded_interval64_lower left)) *
     w2n
       (bounded_signed64_magnitude (bounded_interval64_lower right))) DIV
      1000000000000 /\
  15 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_product»
        [from_cv (bounded_interval64_object_cv left);
         from_cv (bounded_interval64_object_cv right)])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  Cases_on `left`
  >> Cases_on `b`
  >> Cases_on `right`
  >> Cases_on `b`
  >> Cases_on `b'`
  >> Cases_on `b''`
  >> rw
       [compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
        wordsTheory.w2n_eq_0]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_hist_positive_product_lookup,
        registered_case10173_hist_positive_product_body_def,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_fs_scale_lookup,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_arith_def,
        compute_evalTheory.do_reln_def,
        compute_syntaxTheory.SAFEDIV_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_positive_product_from_decimal_product:
  bounded_interval64_valid left /\
  bounded_interval64_valid right /\
  bounded_signed64_strict_positive (bounded_interval64_lower left) /\
  bounded_signed64_strict_positive (bounded_interval64_lower right) /\
  bounded_interval64_mul_decimal left right = SOME product /\
  bounded_signed64_strict_positive (bounded_interval64_lower product) ==>
  0 <
    (w2n
       (bounded_signed64_magnitude (bounded_interval64_lower left)) *
     w2n
       (bounded_signed64_magnitude (bounded_interval64_lower right))) DIV
      1000000000000
Proof
  Cases_on `left`
  >> Cases_on `b`
  >> Cases_on `right`
  >> Cases_on `b`
  >> Cases_on `b'`
  >> Cases_on `b''`
  >> Cases_on `product`
  >> Cases_on `b`
  >> Cases_on `b'`
  >> rw
       [compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
        wordsTheory.w2n_eq_0]
  >> fs
       [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_decimal_def,
        compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedIntervalDecimalTheory.bounded_interval64_product_from_pairs_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_value
  >> gvs
       [compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
        wordsTheory.w2n_eq_0,
        arithmeticTheory.NOT_ZERO_LT_ZERO]
  >> metis_tac
       [wordsTheory.w2n_eq_0,arithmeticTheory.NOT_ZERO_LT_ZERO]
QED

Theorem registered_case10173_atan_range_none_endpoint_magnitudes:
  bounded_interval64_atan_range_decimal input NONE NONE = SOME result ==>
  word_lo
    (bounded_signed64_magnitude (bounded_interval64_lower input))
    bounded_atan_scale_decimal /\
  word_lo
    (bounded_signed64_magnitude (bounded_interval64_upper input))
    bounded_atan_scale_decimal
Proof
  Cases_on `input`
  >> simp
       [compute_boundedAtanDecimalTheory.bounded_interval64_atan_range_decimal_def,
        compute_boundedAtanDecimalTheory.bounded_interval64_atan_range_point_decimal_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        LET_THM]
  >> every_case_tac
  >> gvs []
QED

Definition registered_case10173_hist_unit_interval_body_def:
  registered_case10173_hist_unit_interval_body =
    App «candle_cv_fs_hist_bool_and»
      [App «candle_cv_fs_hist_bool_not»
        [App «candle_cv_fs_raw_le»
          [Uop Fst (Var «value»);
           App «candle_cv_fs_raw_neg» [App «candle_cv_fs_one» []]]];
       App «candle_cv_fs_hist_bool_not»
        [App «candle_cv_fs_raw_le»
          [App «candle_cv_fs_one» [];Uop Snd (Var «value»)]]]
End

Theorem registered_case10173_hist_unit_interval_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_unit_interval» =
    SOME ([«value»],registered_case10173_hist_unit_interval_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_unit_interval_eval:
  word_lo
    (bounded_signed64_magnitude (bounded_interval64_lower value))
    bounded_atan_scale_decimal /\
  word_lo
    (bounded_signed64_magnitude (bounded_interval64_upper value))
    bounded_atan_scale_decimal /\
  50 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_unit_interval»
        [from_cv (bounded_interval64_object_cv value)])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  Cases_on `value`
  >> Cases_on `b`
  >> Cases_on `b0`
  >> Cases_on `b'`
  >> Cases_on `b`
  >> rw
       [compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
        compute_boundedAtanDecimalTheory.bounded_atan_scale_decimal_def,
        wordsTheory.WORD_LO]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_hist_unit_interval_lookup,
        registered_case10173_hist_unit_interval_body_def,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_lookup,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_body_def,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_not_lookup,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_not_body_def,
        compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_le_lookup,
        compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_le_body_def,
        compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_neg_lookup,
        compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_neg_body_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_one_lookup,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_one_body_def,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_fs_scale_lookup,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_arith_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Definition registered_case10173_hist_quotient_body_def:
  registered_case10173_hist_quotient_body =
    App «candle_cv_fs_angle_interval_mul»
      [App «candle_cv_fs_interval_neg» [Var «delta_x4_interval»];
       App «candle_cv_fs_hist_positive_inv»
         [App «candle_cv_fs_angle_interval_mul»
           [Var «root_delta»;Var «root_four_x0»]]]
End

Theorem registered_case10173_hist_quotient_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_quotient» =
    SOME
      ([«delta_x4_interval»;«root_delta»;«root_four_x0»],
       registered_case10173_hist_quotient_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_quotient_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_quotient»
        [from_cv delta_x4;from_cv root_delta;from_cv root_four_x0])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«delta_x4_interval»,from_cv delta_x4);
         («root_delta»,from_cv root_delta);
         («root_four_x0»,from_cv root_four_x0)]
        registered_case10173_hist_quotient_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_hist_quotient_lookup]
QED

Theorem registered_case10173_hist_quotient_typed_eval:
  bounded_interval64_mul_decimal root_delta root_four_x0 = SOME product /\
  bounded_interval64_positive_inv_certificate_decimal product reciprocal /\
  bounded_interval64_mul_decimal
    (bounded_interval64_neg delta_x4) reciprocal = SOME quotient /\
  70 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_quotient»
        [from_cv (bounded_interval64_object_cv delta_x4);
         from_cv (bounded_interval64_object_cv root_delta);
         from_cv (bounded_interval64_object_cv root_four_x0)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv quotient)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_hist_quotient_unfold]
  >> simp
       [registered_case10173_hist_quotient_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_mul»
            [from_cv
               (bounded_interval64_object_cv
                 (bounded_interval64_neg delta_x4));
             from_cv (bounded_interval64_object_cv reciprocal)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
          >> conj_tac
          >- intLib.ARITH_TAC
          >> simp
               [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact])
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fs_hist_positive_inv»
                [from_cv (bounded_interval64_object_cv product)]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
          >> conj_tac
          >- intLib.ARITH_TAC
          >> irule
               compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_interval_mul_typed_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> irule
           compute_registeredCase10173HistoricalInverseEvalTheory.registered_case10173_fs_hist_positive_inv_certificate_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_interval_mul_typed_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_zero_le_interval_lookup_lower_eval:
  index < LENGTH values /\
  EL index values = value /\
  ~bounded_signed64_effective_negative
    (bounded_interval64_lower value) /\
  index + 10 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_le»
        [App «candle_cv_fs_zero» [];
         Uop Fst
           (App «candle_cv_fs_interval_lookup»
             [Num index;
              from_cv (bounded_interval64_object_cv_list values)])])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  Cases_on `value`
  >> rpt strip_tac
  >> `bounded_object_fs_raw_le
        (Pair (Num 0) (Num 0))
        (bounded_signed64_object_cv b) = SOME T` by
       (Cases_on `b`
        >> Cases_on `b'`
        >> gvs
             [compute_boundedIntervalTheory.bounded_interval64_lower_def,
              compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
              compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_le_def,
              compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
              wordsTheory.w2n_eq_0])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_le»
            [from_cv (Pair (Num 0) (Num 0));
             from_cv (bounded_signed64_object_cv b)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule
            compute_registeredCase10173TaylorDotEvalTheory.registered_case10173_fs_zero_eval
          >> intLib.ARITH_TAC)
      >> irule
           compute_registeredCase10173HistoricalAtanPointEvalTheory.registered_case10173_compute_eval_uop_fst_argument_result
      >> simp
           [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def]
      >> qexists_tac `bounded_signed64_object_cv b0`
      >> mp_tac
           (Q.SPECL [`index`,`values`,`clock`,`refs`]
             compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_fs_interval_lookup_num_object_list_eval)
      >> simp
           [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def])
  >> mp_tac
       (Q.INST
         [`left` |-> `(Pair (Num 0) (Num 0):cv)`,
          `right` |-> `bounded_signed64_object_cv b`,
          `answer` |-> `T`,
          `clock` |-> `clock`,
          `refs` |-> `refs`]
         compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_le_eval)
  >> simp [compute_execTheory.from_cv_def]
QED

Definition registered_case10173_hist_environment_nonnegative_body_def:
  registered_case10173_hist_environment_nonnegative_body =
    App «candle_cv_fs_hist_bool_and»
      [App «candle_cv_fs_raw_le»
        [App «candle_cv_fs_zero» [];
         Uop Fst
           (App «candle_cv_fs_interval_lookup»
             [Num 0;Var «environment»])];
       App «candle_cv_fs_hist_bool_and»
        [App «candle_cv_fs_raw_le»
          [App «candle_cv_fs_zero» [];
           Uop Fst
             (App «candle_cv_fs_interval_lookup»
               [Num 1;Var «environment»])];
         App «candle_cv_fs_hist_bool_and»
          [App «candle_cv_fs_raw_le»
            [App «candle_cv_fs_zero» [];
             Uop Fst
               (App «candle_cv_fs_interval_lookup»
                 [Num 2;Var «environment»])];
           App «candle_cv_fs_hist_bool_and»
            [App «candle_cv_fs_raw_le»
              [App «candle_cv_fs_zero» [];
               Uop Fst
                 (App «candle_cv_fs_interval_lookup»
                   [Num 4;Var «environment»])];
             App «candle_cv_fs_raw_le»
              [App «candle_cv_fs_zero» [];
               Uop Fst
                 (App «candle_cv_fs_interval_lookup»
                   [Num 5;Var «environment»])]]]]]
End

Theorem registered_case10173_hist_environment_nonnegative_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_environment_nonnegative» =
    SOME
      ([«environment»],
       registered_case10173_hist_environment_nonnegative_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_environment_nonnegative_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_environment_nonnegative»
        [from_cv environment]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«environment»,from_cv environment)]
        registered_case10173_hist_environment_nonnegative_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_hist_environment_nonnegative_lookup]
QED

Theorem registered_case10173_hist_environment_nonnegative_eval:
  bounded_case10173_positive_environment environment /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_environment_nonnegative»
        [from_cv (bounded_interval64_object_cv_list environment)])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  rpt strip_tac
  >> fs
       [compute_boundedCase10173HistoricalCellTheory.bounded_case10173_positive_environment_def]
  >> `?v0 v1 v2 v3 v4 v5.
        environment = [v0;v1;v2;v3;v4;v5]` by
       metis_tac
         [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.length_six_cases]
  >> gvs []
  >> simp [registered_case10173_hist_environment_nonnegative_unfold]
  >> simp
       [registered_case10173_hist_environment_nonnegative_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_zero_le_interval_lookup_lower_eval
      >> fs
           [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_def])
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_zero_le_interval_lookup_lower_eval
      >> fs
           [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_def])
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_zero_le_interval_lookup_lower_eval
      >> fs
           [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_def])
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_zero_le_interval_lookup_lower_eval
      >> fs
           [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_def])
  >> irule registered_case10173_zero_le_interval_lookup_lower_eval
  >> fs
       [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_def]
QED

val _ = export_theory ();
