(*****************************************************************************
 * Registered source Hessian primitives on the actual Taylor-completed sqrt
 * operand.
 *****************************************************************************)
Theory compute_registeredCase10173ActualSqrtHessianEval
Ancestors
  compute_registeredCase10173ActualSqrtDomainEval
  compute_registeredCase10173SourceSecondDerivativeEval
Libs
  bossLib preamble intLib

Theorem compute_eval_app1_argument_cong:
  0 < clock /\
  compute_eval clock ceqs left (refs:hol_refs) =
    compute_eval clock ceqs right refs ==>
  compute_eval clock ceqs (App function_name [left]) refs =
    compute_eval clock ceqs (App function_name [right]) refs
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
  >> Cases_on `LENGTH q = 1`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_actual_fs_interval_to_q_eval:
  bounded_case10173_positive_interval64_q_cv value_bound = SOME input /\
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_to_q»
        [from_cv (bounded_interval64_object_cv value_bound)])
      (refs:hol_refs) =
    (M_success (from_cv input),refs)
Proof
  strip_tac
  >> Cases_on `value_bound`
  >> Cases_on `b`
  >> Cases_on `b0`
  >> Cases_on `b'`
  >> Cases_on `b`
  >> fs
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_positive_interval64_q_cv_def]
  >> gvs
       [compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_positive_endpoint64_q_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> match_mp_tac
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`lower` |-> `Pair (Num (w2n (c:word64))) (Num 0)`,
            `upper` |-> `Pair (Num (w2n (c':word64))) (Num 0)`]
           compute_registeredCase10173SqrtPrimitiveEvalTheory.registered_case10173_fs_interval_to_q_eval))
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_actual_sqrt_second_derivative_direct_eval:
  bounded_interval64_valid value_bound /\
  bounded_case10173_positive_interval64_q_cv value_bound = SOME input /\
  bounded_object_positive_q_interval64_decimal root = SOME root_decimal /\
  bounded_case10173_source_q_sqrt_certificate_exact input root /\
  bounded_case10173_source_sqrt_dd_interval64_exact
    root input reciprocal /\
  155 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_of_q»
        [App «candle_cv_q_dim_jet_sqrt_dd»
          [from_cv root;from_cv input]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (bounded_interval64_neg reciprocal))),refs)
Proof
  strip_tac
  >> mp_tac
       (compute_boundedPositiveQShapeTheory.bounded_object_positive_q_interval64_decimal_shape
        |> Q.INST [`encoded` |-> `root`, `result` |-> `root_decimal`])
  >> impl_tac >- first_assum ACCEPT_TAC
  >> strip_tac
  >> Cases_on `value_bound`
  >> Cases_on `b`
  >> Cases_on `b0`
  >> Cases_on `b'`
  >> Cases_on `b`
  >> fs
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_positive_interval64_q_cv_def]
  >> gvs
       [compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_positive_endpoint64_q_cv_def,
        compute_boundedCase10173SourceSqrtCertificateTheory.bounded_case10173_source_q_sqrt_certificate_exact_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> Cases_on `upper_value`
  >> fs []
  >> mp_tac
       (Q.INST
         [`root_lower` |-> `lower_value`,
          `root_lower_denominator` |->
            `SUC lower_denominator_minus_one`,
          `root_upper` |-> `SUC n`,
          `root_upper_denominator` |->
            `SUC upper_denominator_minus_one`,
          `input_lower` |-> `w2n (c:word64)`,
          `input_lower_denominator` |-> `1000000000000`,
          `input_upper` |-> `w2n (c':word64)`,
          `input_upper_denominator` |-> `1000000000000`,
          `reciprocal` |-> `reciprocal`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_registeredCase10173SourceSecondDerivativeEvalTheory.registered_case10173_source_sqrt_second_derivative_decimal_eval)
  >> impl_tac
  >- (PURE_REWRITE_TAC [arithmeticTheory.SUC_SUB1]
      >> simp [arithmeticTheory.MULT_COMM]
      >> intLib.ARITH_TAC)
  >> simp
       [arithmeticTheory.SUC_SUB1,
        compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_positive_endpoint64_q_cv_def,
        compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_actual_sqrt_second_derivative_eval:
  bounded_interval64_valid value_bound /\
  bounded_case10173_positive_interval64_q_cv value_bound = SOME input /\
  bounded_object_positive_q_interval64_decimal root = SOME root_decimal /\
  bounded_case10173_source_q_sqrt_certificate_exact input root /\
  bounded_case10173_source_sqrt_dd_interval64_exact
    root input reciprocal /\
  155 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_of_q»
        [App «candle_cv_q_dim_jet_sqrt_dd»
          [from_cv root;
           App «candle_cv_fs_interval_to_q»
             [from_cv (bounded_interval64_object_cv value_bound)]]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (bounded_interval64_neg reciprocal))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_of_q»
            [App «candle_cv_q_dim_jet_sqrt_dd»
              [from_cv root;from_cv input]]) refs`
  >> conj_tac
  >- (irule compute_eval_app1_argument_cong
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule registered_case10173_actual_fs_interval_to_q_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> match_mp_tac
       (Q.INST
         [`value_bound` |-> `value_bound`,
          `root_decimal` |-> `root_decimal`]
         registered_case10173_actual_sqrt_second_derivative_direct_eval)
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
