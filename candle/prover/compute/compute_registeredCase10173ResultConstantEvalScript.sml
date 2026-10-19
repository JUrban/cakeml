(*****************************************************************************
 * Registered evaluator refinement for signed rational constant results.
 *
 * Unlike authenticated coordinate boxes, source polynomial constants are
 * signed rationals.  These lemmas check the historical 10^12 outward
 * rounding for both signs, construct the zero gradient/Hessian leaf, and
 * connect the literal source function to the complete object Taylor result.
 * Endpoint lemmas deliberately cover non-normalized signed numerators too.
 *****************************************************************************)
Theory compute_registeredCase10173ResultConstantEval
Ancestors
  compute_registeredCase10173ResultVariableEval
  compute_boundedObjectSignedDecimalQ
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_interval_constant_body_def:
  registered_case10173_fs_interval_constant_body =
    Pair
      (App «candle_cv_fs_of_q_lower» [Var «q»])
      (App «candle_cv_fs_of_q_upper» [Var «q»])
End

Definition registered_case10173_fs_result_constant_body_def:
  registered_case10173_fs_result_constant_body =
    App «candle_cv_fs_result_complete_rounded»
      [Var «radii»;
       Num 1;
       App «candle_cv_fs_first_make»
         [App «candle_cv_fs_interval_constant» [Var «q»];
          App «candle_cv_fs_interval_zeros» [Var «dimensions»]];
       App «candle_cv_fs_interval_zero_matrix»
         [Var «dimensions»;Var «dimensions»]]
End

Theorem registered_case10173_fs_interval_constant_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_constant» =
    SOME ([«q»],registered_case10173_fs_interval_constant_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_constant_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_constant» =
    SOME
      ([«dimensions»;«radii»;«q»],
       registered_case10173_fs_result_constant_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_of_q_lower_signed_eval:
  7 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_lower»
        [from_cv
          (Pair (Pair (Num positive) (Num negative))
            (Num denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (if positive < negative then
         Pair (Num 0)
           (Num
             ((1000000000000 * (negative - positive)) DIV
                (denominator_minus_one + 1) +
              if (1000000000000 * (negative - positive)) MOD
                   (denominator_minus_one + 1) = 0
              then 0 else 1))
       else
         Pair
           (Num
             ((1000000000000 * (positive - negative)) DIV
                (denominator_minus_one + 1)))
           (Num 0)),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_of_q_lower_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_of_q_lower_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_lower_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_lower_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_body_def,
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
        compute_evalTheory.do_arith_def,
        compute_syntaxTheory.SAFEDIV_def,
        compute_syntaxTheory.SAFEMOD_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `positive < negative`
  >> simp []
  >> Cases_on
       `(1000000000000 * (negative - positive)) MOD
          (denominator_minus_one + 1) = 0`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_arith_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val registered_case10173_fs_of_q_lower_signed_raw_eval =
  SIMP_RULE std_ss [compute_execTheory.from_cv_def]
    registered_case10173_fs_of_q_lower_signed_eval;

Theorem registered_case10173_fs_of_q_upper_signed_eval:
  9 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_upper»
        [from_cv
          (Pair (Pair (Num positive) (Num negative))
            (Num denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (if positive < negative then
         Pair (Num 0)
           (Num
             ((1000000000000 * (negative - positive)) DIV
                (denominator_minus_one + 1)))
       else
         Pair
           (Num
             ((1000000000000 * (positive - negative)) DIV
                (denominator_minus_one + 1) +
              if (1000000000000 * (positive - negative)) MOD
                   (denominator_minus_one + 1) = 0
              then 0 else 1))
           (Num 0)),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_of_q_upper_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_of_q_upper_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_upper_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_upper_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_body_def,
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
        compute_evalTheory.do_arith_def,
        compute_syntaxTheory.SAFEDIV_def,
        compute_syntaxTheory.SAFEMOD_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `positive < negative`
  >> simp []
  >> Cases_on
       `(1000000000000 * (positive - negative)) MOD
          (denominator_minus_one + 1) = 0`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_arith_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val registered_case10173_fs_of_q_upper_signed_raw_eval =
  SIMP_RULE std_ss [compute_execTheory.from_cv_def]
    registered_case10173_fs_of_q_upper_signed_eval;

Theorem registered_case10173_fs_of_q_lower_signed_object_eval:
  (* The decoder premise also supplies the word-range side condition. *)
  bounded_object_q_floor64_decimal encoded = SOME endpoint /\
  7 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_lower» [from_cv encoded])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_signed64_object_cv endpoint)),refs)
Proof
  Cases_on `encoded`
  >> fs [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_floor64_decimal_def]
  >> Cases_on `c`
  >> fs [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_floor64_decimal_def]
  >> Cases_on `c'`
  >> fs [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_floor64_decimal_def]
  >> Cases_on `c0'`
  >> fs [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_floor64_decimal_def]
  >> Cases_on `c0`
  >> fs [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_floor64_decimal_def]
  >> Cases_on `n < n'`
  >> fs [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_floor64_decimal_def]
  >> every_case_tac
  >> strip_tac
  >> gvs
       [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_floor64_decimal_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedObjectDecimalQTheory.bounded_decimal_natural_floor64_def,
        compute_boundedObjectDecimalQTheory.bounded_decimal_natural_ceil64_def,
        LET_THM,
        compute_boundedTheory.bounded_word_base_def,
        wordsTheory.w2n_n2w,
        arithmeticTheory.ADD1,
        compute_boundedSignedTheory.bounded_div_ceil,
        registered_case10173_fs_of_q_lower_signed_raw_eval]
QED

Theorem registered_case10173_fs_of_q_upper_signed_object_eval:
  bounded_object_q_ceil64_decimal encoded = SOME endpoint /\
  9 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_upper» [from_cv encoded])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_signed64_object_cv endpoint)),refs)
Proof
  Cases_on `encoded`
  >> fs [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_ceil64_decimal_def]
  >> Cases_on `c`
  >> fs [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_ceil64_decimal_def]
  >> Cases_on `c'`
  >> fs [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_ceil64_decimal_def]
  >> Cases_on `c0'`
  >> fs [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_ceil64_decimal_def]
  >> Cases_on `c0`
  >> fs [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_ceil64_decimal_def]
  >> Cases_on `n < n'`
  >> fs [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_ceil64_decimal_def]
  >> every_case_tac
  >> strip_tac
  >> gvs
       [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_ceil64_decimal_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedObjectDecimalQTheory.bounded_decimal_natural_floor64_def,
        compute_boundedObjectDecimalQTheory.bounded_decimal_natural_ceil64_def,
        LET_THM,
        compute_boundedTheory.bounded_word_base_def,
        wordsTheory.w2n_n2w,
        arithmeticTheory.ADD1,
        compute_boundedSignedTheory.bounded_div_ceil,
        registered_case10173_fs_of_q_upper_signed_raw_eval]
QED

Theorem registered_case10173_fs_interval_constant_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_constant» [from_cv q])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«q»,from_cv q)]
        registered_case10173_fs_interval_constant_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_interval_constant_lookup]
QED

Theorem registered_case10173_fs_interval_constant_object_eval:
  bounded_object_q_constant_interval64_decimal encoded = SOME interval /\
  10 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_constant» [from_cv encoded])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv interval)),refs)
Proof
  strip_tac
  >> fs
       [compute_boundedObjectSignedDecimalQTheory.bounded_object_q_constant_interval64_decimal_def]
  >> every_case_tac
  >> gvs []
  >> simp [registered_case10173_fs_interval_constant_unfold]
  >> simp
       [registered_case10173_fs_interval_constant_body_def,
        compute_evalTheory.subst_def]
  >> `7 < clock - 1 /\ 9 < clock - 1` by intLib.ARITH_TAC
  >> `compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_lower» [from_cv encoded]) refs =
      (M_success (from_cv (bounded_signed64_object_cv lower)),refs)` by
       simp [registered_case10173_fs_of_q_lower_signed_object_eval]
  >> `compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_upper» [from_cv encoded]) refs =
      (M_success (from_cv (bounded_signed64_object_cv upper)),refs)` by
       simp [registered_case10173_fs_of_q_upper_signed_object_eval]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_execTheory.from_cv_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_result_constant_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_constant»
        [from_cv dimensions;from_cv radii;from_cv q])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («q»,from_cv q)]
        registered_case10173_fs_result_constant_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_fs_result_constant_lookup]
QED

Theorem registered_case10173_fs_result_constant_center_eval:
  bounded_object_q_constant_interval64_decimal encoded = SOME value /\
  10 < clock /\
  4 * (LENGTH dimensions + 1) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_make»
        [App «candle_cv_fs_interval_constant» [from_cv encoded];
         App «candle_cv_fs_interval_zeros»
           [from_cv (bounded_interval64_object_cv_list dimensions)]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (bounded_interval64_object_cv value)
          (bounded_interval64_object_cv_list
            (REPLICATE (LENGTH dimensions) bounded_interval64_zero)))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_first_make»
            [from_cv (bounded_interval64_object_cv value);
             from_cv
               (bounded_interval64_object_cv_list
                 (REPLICATE (LENGTH dimensions)
                   bounded_interval64_zero))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- simp [registered_case10173_fs_interval_constant_object_eval]
      >> irule
           compute_registeredCase10173PolynomialShapeEvalTheory.registered_case10173_fs_interval_zeros_object_eval
      >> simp [])
  >> irule
       compute_registeredCase10173HistoricalBasicEvalTheory.registered_case10173_fs_first_make_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_result_constant_object_eval:
  bounded_object_q_constant_interval64_decimal encoded = SOME value /\
  zero_rows =
    REPLICATE (LENGTH dimensions)
      (REPLICATE (LENGTH dimensions) bounded_interval64_zero) /\
  bounded_hessian64_rows (bounded_interval64_zeros 21) =
    SOME zero_rows /\
  bounded_object_fs_taylor_complete radii T value
      (REPLICATE (LENGTH dimensions) bounded_interval64_zero)
      (bounded_interval64_zeros 21) zero_rows = SOME result /\
  2 < clock /\
  10 < clock - 1 /\
  4 * (LENGTH dimensions + 1) < clock - 1 /\
  4 * (2 * LENGTH dimensions + 2) < clock - 1 /\
  256 *
      (2 * LENGTH radii + LENGTH zero_rows + LENGTH dimensions + 2) <
    clock - 1 ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_constant»
        [from_cv (bounded_interval64_object_cv_list dimensions);
         from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv encoded])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> simp
       [registered_case10173_fs_result_constant_unfold,
        registered_case10173_fs_result_constant_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_complete_rounded»
            [from_cv
               (registered_case10173_word64_object_cv_list radii);
             from_cv (bounded_bool_object_cv T);
             from_cv
               (Pair
                 (bounded_interval64_object_cv value)
                 (bounded_interval64_object_cv_list
                   (REPLICATE (LENGTH dimensions)
                     bounded_interval64_zero)));
             from_cv (bounded_interval64_object_cv_matrix zero_rows)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- simp [compute_execProofTheory.compute_eval_from_cv]
      >> conj_tac
      >- (simp_tac std_ss
            [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def,
             compute_execTheory.from_cv_def]
          >> ACCEPT_TAC
               (SIMP_RULE std_ss
                 [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def,
                  compute_execTheory.from_cv_def]
                 (SPECL
                   [``(Num 1:cv)``,``(refs:hol_refs)``,
                    ``(clock - 1:num)``,
                    ``registered_case10173_historical_chunk16_ceqs``]
                   compute_execProofTheory.compute_eval_from_cv)))
      >> conj_tac
      >- (irule registered_case10173_fs_result_constant_center_eval
          >> simp [])
      >> rw []
      >> irule
           compute_registeredCase10173PolynomialShapeEvalTheory.registered_case10173_fs_interval_zero_matrix_object_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173TaylorCompleteObjectEvalTheory.registered_case10173_fs_result_complete_rounded_object_eval
  >> conj_tac
  >- (qpat_x_assum `256 * _ < _` mp_tac
      >> asm_rewrite_tac []
      >> simp []
      >> intLib.ARITH_TAC)
  >> qexists_tac `bounded_interval64_zeros 21`
  >> metis_tac []
QED

val _ = export_theory ();
