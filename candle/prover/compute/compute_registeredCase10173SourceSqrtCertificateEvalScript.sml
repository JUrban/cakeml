(*****************************************************************************
 * Authenticated source-rational square-root certificate evaluation.
 *
 * The packet stream checks the certificate inequalities on the unchanged
 * rational source data.  Successful decimal conversion additionally fixes
 * the source rationals to the positive canonical representation expected by
 * the registered evaluator.  This theorem composes those two facts without
 * replaying any closed-cell arithmetic.
 *****************************************************************************)
Theory compute_registeredCase10173SourceSqrtCertificateEval
Ancestors
  compute_boundedPositiveQShape
  compute_boundedCase10173SourceSqrtCertificate
  compute_registeredCase10173SqrtCertificateCompleteEval
Libs
  bossLib preamble intLib

Theorem positive_square_sub_one_add_one:
  (((n:num) + 1) * (n + 1) - 1) + 1 = (n + 1) * (n + 1)
Proof
  `1 <= (n + 1) * (n + 1)` by simp []
  >> metis_tac [arithmeticTheory.SUB_ADD]
QED

Theorem registered_case10173_source_q_sqrt_certificate_exact_eval:
  bounded_object_positive_q_interval64_decimal input = SOME input_decimal /\
  bounded_object_positive_q_interval64_decimal output = SOME output_decimal /\
  bounded_case10173_source_q_sqrt_certificate_exact input output /\
  5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_sqrt_certificate»
        [from_cv input;from_cv output]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> mp_tac
       (compute_boundedPositiveQShapeTheory.bounded_object_positive_q_interval64_decimal_shape
        |> Q.INST [`encoded` |-> `input`, `result` |-> `input_decimal`])
  >> impl_tac >- first_assum ACCEPT_TAC
  >> strip_tac
  >> mp_tac
       (compute_boundedPositiveQShapeTheory.bounded_object_positive_q_interval64_decimal_shape
        |> Q.INST [`encoded` |-> `output`, `result` |-> `output_decimal`])
  >> impl_tac >- first_assum ACCEPT_TAC
  >> strip_tac
  >> PURE_ASM_REWRITE_TAC []
  >> irule
       compute_registeredCase10173SqrtCertificateCompleteEvalTheory.registered_case10173_q_interval_sqrt_certificate_positive_eval
  >> qpat_x_assum
       `bounded_case10173_source_q_sqrt_certificate_exact _ _` mp_tac
  >> PURE_ASM_REWRITE_TAC []
  >> rw
       [compute_boundedCase10173SourceSqrtCertificateTheory.bounded_case10173_source_q_sqrt_certificate_exact_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> PURE_REWRITE_TAC
       [arithmeticTheory.EXP_2, positive_square_sub_one_add_one]
  >> first_assum
       (MATCH_ACCEPT_TAC o
        SIMP_RULE std_ss
          [arithmeticTheory.ADD1, arithmeticTheory.EXP_2])
QED

val _ = export_theory ();
