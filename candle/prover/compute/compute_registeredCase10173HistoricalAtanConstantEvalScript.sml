(*****************************************************************************
 * Registered evaluator semantics for the historical arctangent coefficients.
 *
 * The literal source constructs each directed rational interval from the
 * fixed decimal scale.  This theory first connects that source helper to the
 * ordinary-cv bounded operations, then identifies the six coefficients used
 * by the historical arctangent polynomial with the specialized checker.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalAtanConstantEval
Ancestors
  compute_registeredCase10173HistoricalTupleEval
  compute_boundedAtanDecimal
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_rational_constant_body_def:
  registered_case10173_fs_hist_rational_constant_body =
    Let «numerator»
      (App «candle_cv_fs_raw_scale»
        [App «candle_cv_fs_scale» [];
         Pair (Var «positive») (Var «negative»)])
      (Pair
        (App «candle_cv_fs_floor_div»
          [Var «numerator»;Var «denominator»])
        (App «candle_cv_fs_ceil_div»
          [Var «numerator»;Var «denominator»]))
End

Definition bounded_object_fs_hist_rational_constant_def:
  bounded_object_fs_hist_rational_constant positive negative denominator =
    let numerator =
      (Pair
        (Num (1000000000000 * positive))
        (Num (1000000000000 * negative)) : cv) in
    case bounded_object_fs_floor_div numerator denominator of
    | NONE => NONE
    | SOME lower =>
      case bounded_object_fs_ceil_div numerator denominator of
      | NONE => NONE
      | SOME upper => SOME (Pair lower upper)
End

Theorem registered_case10173_fs_hist_rational_constant_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_rational_constant» =
    SOME
      ([«positive»;«negative»;«denominator»],
       registered_case10173_fs_hist_rational_constant_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_compute_eval_literal_app3:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME ([first_name;second_name;third_name],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv first_argument;from_cv second_argument;
         from_cv third_argument]) (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(first_name,from_cv first_argument);
         (second_name,from_cv second_argument);
         (third_name,from_cv third_argument)] body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_fs_hist_rational_constant_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_rational_constant»
        [from_cv (Num positive);from_cv (Num negative);
         from_cv (Num denominator)]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«positive»,from_cv (Num positive));
         («negative»,from_cv (Num negative));
         («denominator»,from_cv (Num denominator))]
        registered_case10173_fs_hist_rational_constant_body) refs
Proof
  strip_tac
  >> irule registered_case10173_hist_compute_eval_literal_app3
  >> simp [registered_case10173_fs_hist_rational_constant_lookup]
QED

Theorem registered_case10173_fs_hist_rational_constant_object_eval:
  bounded_object_fs_hist_rational_constant
      positive negative denominator = SOME result /\
  0 < denominator /\ 8 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_rational_constant»
        [from_cv (Num positive);from_cv (Num negative);
         from_cv (Num denominator)]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_rational_constant_unfold]
  >> simp
       [registered_case10173_fs_hist_rational_constant_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (Pair
            (Num (1000000000000 * positive))
            (Num (1000000000000 * negative)))`
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_scale»
            [App «candle_cv_fs_scale» [];
             Pair (Num positive) (Num negative)]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_scale»
            [from_cv (Num 1000000000000);
             from_cv (Pair (Num positive) (Num negative))]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> conj_tac >- intLib.ARITH_TAC
        >> simp [compute_execTheory.from_cv_def]
        >> conj_tac
        >- (irule
              compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval
            >> intLib.ARITH_TAC)
        >> simp
             [compute_evalTheory.compute_eval_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def])
      >> rw []
      >> simp [compute_execTheory.from_cv_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_raw_scale_eval)
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execTheory.from_cv_def]
  >> gvs [bounded_object_fs_hist_rational_constant_def]
  >> Cases_on
       `bounded_object_fs_floor_div
          (Pair
            (Num (1000000000000 * positive))
            (Num (1000000000000 * negative))) denominator`
  >> gvs []
  >> Cases_on
       `bounded_object_fs_ceil_div
          (Pair
            (Num (1000000000000 * positive))
            (Num (1000000000000 * negative))) denominator`
  >> gvs []
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`source` |->
               `(Pair
                  (Num (1000000000000 * positive))
                  (Num (1000000000000 * negative)):cv)`]
            compute_registeredCase10173TaylorRoundEvalTheory.registered_case10173_fs_floor_div_eval))
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`source` |->
              `(Pair
                 (Num (1000000000000 * positive))
                 (Num (1000000000000 * negative)):cv)`]
           compute_registeredCase10173TaylorRoundEvalTheory.registered_case10173_fs_ceil_div_eval))
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_rational_neg_eleventh_eval:
  8 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_rational_constant» [Num 0;Num 1;Num 11])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          bounded_atan_neg_eleventh_decimal)),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_rational_constant_object_eval)
  >> simp
       [bounded_object_fs_hist_rational_constant_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        bounded_atan_neg_eleventh_decimal_def]
QED

Theorem registered_case10173_fs_hist_rational_pos_ninth_eval:
  8 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_rational_constant» [Num 1;Num 0;Num 9])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          bounded_atan_pos_ninth_decimal)),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_rational_constant_object_eval)
  >> simp
       [bounded_object_fs_hist_rational_constant_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        bounded_atan_pos_ninth_decimal_def]
QED

Theorem registered_case10173_fs_hist_rational_neg_seventh_eval:
  8 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_rational_constant» [Num 0;Num 1;Num 7])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          bounded_atan_neg_seventh_decimal)),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_rational_constant_object_eval)
  >> simp
       [bounded_object_fs_hist_rational_constant_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        bounded_atan_neg_seventh_decimal_def]
QED

Theorem registered_case10173_fs_hist_rational_pos_fifth_eval:
  8 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_rational_constant» [Num 1;Num 0;Num 5])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          bounded_atan_pos_fifth_decimal)),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_rational_constant_object_eval)
  >> simp
       [bounded_object_fs_hist_rational_constant_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        bounded_atan_pos_fifth_decimal_def]
QED

Theorem registered_case10173_fs_hist_rational_neg_third_eval:
  8 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_rational_constant» [Num 0;Num 1;Num 3])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          bounded_atan_neg_third_decimal)),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_rational_constant_object_eval)
  >> simp
       [bounded_object_fs_hist_rational_constant_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        bounded_atan_neg_third_decimal_def,
        bounded_atan_pos_third_decimal_def,
        compute_boundedIntervalAddTheory.bounded_interval64_neg_def,
        compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_make_def]
QED

Theorem registered_case10173_fs_hist_rational_pos_thirteenth_eval:
  8 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_rational_constant» [Num 1;Num 0;Num 13])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          bounded_atan_pos_thirteenth_decimal)),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_rational_constant_object_eval)
  >> simp
       [bounded_object_fs_hist_rational_constant_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        bounded_atan_pos_thirteenth_decimal_def]
QED

val _ = export_theory ();
