(*****************************************************************************
 * Registered source-domain check on the actual Taylor-completed operand.
 *****************************************************************************)
Theory compute_registeredCase10173ActualSqrtDomainEval
Ancestors
  compute_boundedCase10173ActualSqrtConversion
  compute_registeredCase10173SqrtDomainPositiveEval
  compute_registeredCase10173SourceSqrtCertificateEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_actual_sqrt_domain_eval:
  bounded_interval64_valid value_bound /\
  bounded_case10173_positive_interval64_q_cv value_bound = SOME input /\
  bounded_object_positive_q_interval64_decimal root = SOME root_decimal /\
  bounded_case10173_source_q_sqrt_certificate_exact input root /\
  144 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_sqrt_domain»
        [from_cv root;
         from_cv (bounded_interval64_object_cv value_bound)])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
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
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_positive_interval64_q_cv_def,
        compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_positive_endpoint64_q_cv_def,
        compute_boundedCase10173SourceSqrtCertificateTheory.bounded_case10173_source_q_sqrt_certificate_exact_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> match_mp_tac
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173SqrtDomainPositiveEvalTheory.registered_case10173_fsn_sqrt_domain_positive_eval)
  >> Cases_on `upper_value`
  >> fs []
  >> PURE_REWRITE_TAC [arithmeticTheory.EXP_2]
  >> PURE_REWRITE_TAC
       [compute_registeredCase10173SourceSqrtCertificateEvalTheory.positive_square_sub_one_add_one]
  >> PURE_REWRITE_TAC [GSYM arithmeticTheory.ADD1]
  >> metis_tac [arithmeticTheory.EXP_2, arithmeticTheory.MULT_COMM]
QED

val _ = export_theory ();
