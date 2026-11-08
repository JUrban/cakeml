(*****************************************************************************
 * Bridge the proof-only exact square-root certificate contract to the six
 * production boolean checks.  This is representation-generic; genuine
 * case-16594 source-6 inputs instantiate it after equivalence transport.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSqrtCertificateExactEval
Ancestors
  compute_boundedCase16594ObjectSqrtCertificateEval
  compute_boundedCase16594ObjectSqrtCertificateContract
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_q_le_of_ints:
  bounded_object_q_ints left =
      SOME (left_numerator,left_denominator) /\
  bounded_object_q_ints right =
      SOME (right_numerator,right_denominator) /\
  left_numerator * right_denominator <=
      right_numerator * left_denominator ==>
  bounded_object_q_le_cv left right
Proof
  strip_tac
  >> `bounded_object_q_le_cv left right <=>
        bounded_int_fraction_le
          (left_numerator,left_denominator)
          (right_numerator,right_denominator)` by
       (irule
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct
        >> simp [])
  >> fs
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_case16594_object_q_mul_self_decodes:
  bounded_object_q_ints value = SOME (numerator,denominator) ==>
  bounded_object_q_ints (bounded_object_q_mul_cv value value) =
    SOME (numerator * numerator,denominator * denominator)
Proof
  strip_tac
  >> rewrite_tac
       [GSYM
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def]
  >> irule
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes
  >> simp []
QED

Theorem bounded_case16594_object_q_mul_self_le_of_ints:
  bounded_object_q_ints squared =
      SOME (squared_numerator,squared_denominator) /\
  bounded_object_q_ints bound =
      SOME (bound_numerator,bound_denominator) /\
  squared_numerator * squared_numerator * bound_denominator <=
      bound_numerator * squared_denominator * squared_denominator ==>
  bounded_object_q_le_cv
    (bounded_object_q_mul_cv squared squared) bound
Proof
  strip_tac
  >> `bounded_object_q_le_cv
        (bounded_object_q_mul_cv squared squared) bound <=>
      bounded_int_fraction_le
        (squared_numerator * squared_numerator,
         squared_denominator * squared_denominator)
        (bound_numerator,bound_denominator)` by
       (irule
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct
        >> simp [bounded_case16594_object_q_mul_self_decodes])
  >> fs
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def,
        integerTheory.INT_MUL_ASSOC]
QED

Theorem bounded_case16594_object_q_le_mul_self_of_ints:
  bounded_object_q_ints squared =
      SOME (squared_numerator,squared_denominator) /\
  bounded_object_q_ints bound =
      SOME (bound_numerator,bound_denominator) /\
  bound_numerator * squared_denominator * squared_denominator <=
      squared_numerator * squared_numerator * bound_denominator ==>
  bounded_object_q_le_cv bound
    (bounded_object_q_mul_cv squared squared)
Proof
  strip_tac
  >> `bounded_object_q_le_cv bound
        (bounded_object_q_mul_cv squared squared) <=>
      bounded_int_fraction_le
        (bound_numerator,bound_denominator)
        (squared_numerator * squared_numerator,
         squared_denominator * squared_denominator)` by
       (irule
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct
        >> simp [bounded_case16594_object_q_mul_self_decodes])
  >> fs
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def,
        integerTheory.INT_MUL_ASSOC]
QED

Theorem bounded_case16594_object_q_nonnegative_of_ints:
  bounded_object_q_ints value = SOME (numerator,denominator) /\
  0 <= numerator ==>
  bounded_object_q_le_cv bounded_object_q_zero_cv value
Proof
  strip_tac
  >> `bounded_object_q_le_cv bounded_object_q_zero_cv value <=>
      bounded_int_fraction_le (0,1) (numerator,denominator)` by
       (irule
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct
        >> simp [])
  >> fs
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_case16594_object_sqrt_certificate_exact_conditions:
  bounded_object_q_sqrt_certificate_exact input output ==>
  ?input_lower input_upper output_lower output_upper.
    input = Pair input_lower input_upper /\
    output = Pair output_lower output_upper /\
    bounded_object_q_encoded input_lower /\
    bounded_object_q_encoded input_upper /\
    bounded_object_q_encoded output_lower /\
    bounded_object_q_encoded output_upper /\
    bounded_object_q_le_cv bounded_object_q_zero_cv input_lower /\
    bounded_object_q_le_cv input_lower input_upper /\
    bounded_object_q_le_cv bounded_object_q_zero_cv output_lower /\
    bounded_object_q_le_cv output_lower output_upper /\
    bounded_object_q_le_cv
      (bounded_object_q_mul_cv output_lower output_lower) input_lower /\
    bounded_object_q_le_cv input_upper
      (bounded_object_q_mul_cv output_upper output_upper)
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> simp
       [compute_boundedAnalyticObjectSqrtRefinementTheory.bounded_object_q_sqrt_certificate_exact_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> every_case_tac
  >> gvs []
  >> strip_tac
  >> simp [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> rpt conj_tac
  >> metis_tac
       [bounded_case16594_object_q_le_of_ints,
        bounded_case16594_object_q_mul_self_le_of_ints,
        bounded_case16594_object_q_le_mul_self_of_ints,
        bounded_case16594_object_q_nonnegative_of_ints]
QED

Theorem bounded_case16594_object_q_interval_sqrt_certificate_exact_eval:
  bounded_object_q_sqrt_certificate_exact input output /\
  5 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_sqrt_certificate»
        [from_cv input;from_cv output]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> imp_res_tac bounded_case16594_object_sqrt_certificate_exact_conditions
  >> gvs []
  >> irule
       (REWRITE_RULE
         [compute_execTheory.from_cv_def]
         compute_boundedCase16594ObjectSqrtCertificateEvalTheory.bounded_case16594_object_q_interval_sqrt_certificate_conditions_eval)
  >> simp []
QED

val _ = export_theory ();
