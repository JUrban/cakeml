(*****************************************************************************
 * Negative exact-rational boundary for one accepted packed analytic result.
 *
 * The executable checker accepts a cell only when the upper endpoint of its
 * scale-2^40 word result is strictly negative.  The object-q refinement
 * relation already proves that the exact rational upper endpoint is no
 * greater than that word endpoint.  This theory makes the resulting exact
 * sign fact explicit for the analytic handoff.
 *****************************************************************************)
Theory compute_boundedPackedAnalyticNegativeBoundary
Ancestors
  compute_boundedPackedAnalyticSoundBoundary
Libs
  bossLib preamble intLib

Definition bounded_object_q_interval_upper_strict_negative_def:
  bounded_object_q_interval_upper_strict_negative encoded <=>
    case bounded_object_q_interval_ints encoded of
    | NONE => F
    | SOME ((lower_numerator,lower_denominator),
            (upper_numerator,upper_denominator)) =>
        0 < lower_denominator /\
        0 < upper_denominator /\
        lower_numerator * upper_denominator <=
          upper_numerator * lower_denominator /\
        upper_numerator < 0
End

Theorem bounded_interval64_covers_object_q_strict_negative_upper:
  bounded_interval64_covers_object_q word_interval encoded /\
  bounded_signed64_strict_negative
    (bounded_interval64_upper word_interval) ==>
  bounded_object_q_interval_upper_strict_negative encoded
Proof
  strip_tac
  >> rw [bounded_object_q_interval_upper_strict_negative_def]
  >> Cases_on `bounded_object_q_interval_ints encoded`
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
  >> PairCases_on `x`
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_correct]
  >> `bounded_word_scale_int > 0` by
       simp
         [compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def]
  >> `x3 * bounded_signed64_to_int
        (bounded_interval64_upper word_interval) < 0` by
       (qsuff_tac
          `0 < x3 *
            -bounded_signed64_to_int (bounded_interval64_upper word_interval)`
        >- intLib.ARITH_TAC
        >> irule
             (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
        >> intLib.ARITH_TAC)
  >> CCONTR_TAC
  >> `0 <= bounded_word_scale_int * x2` by
       (irule integerTheory.INT_LE_MUL
        >> intLib.ARITH_TAC)
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_analytic_result_accepts_object_q_negative:
  bounded_packed_analytic_result_accepts word_result /\
  bounded_taylor64_covers_object_q word_result
    (BoundedObjectQTaylor object_domain object_center_value
      object_center_gradient object_value_bound object_gradient_bounds
      object_hessian) ==>
  object_domain /\
  bounded_object_q_interval_upper_strict_negative object_value_bound
Proof
  Cases_on `word_result`
  >> simp
       [compute_boundedPackedAnalyticCheckTheory.bounded_packed_analytic_result_accepts_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def]
  >> metis_tac
       [bounded_interval64_covers_object_q_strict_negative_upper]
QED

val _ = export_theory ();
