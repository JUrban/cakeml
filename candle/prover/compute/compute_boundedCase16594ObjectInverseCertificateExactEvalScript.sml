(*****************************************************************************
 * Bridge the proof-only exact positive-reciprocal certificate contract to
 * the production inverse-certificate evaluator.  This stays generic over
 * object-q encodings so the genuine case-16594 certificates can instantiate
 * it without re-evaluating their arithmetic in the theorem layer.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectInverseCertificateExactEval
Ancestors
  compute_boundedCase16594ObjectInverseCertificateEval
  compute_boundedCase16594ObjectSqrtCertificateExactEval
  compute_boundedCase16594ObjectSqrtCertificateContract
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_q_le_positive_inv_right_of_ints:
  bounded_object_q_ints left =
      SOME (left_numerator,left_denominator) /\
  bounded_object_q_ints right =
      SOME (right_numerator,right_denominator) /\
  0 < right_numerator /\
  left_numerator * right_numerator <=
      right_denominator * left_denominator ==>
  bounded_object_q_le_cv left
    (bounded_case16594_object_q_positive_inv_cv right)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectSqrtCertificateExactEvalTheory.bounded_case16594_object_q_le_of_ints
  >> qexists_tac `left_denominator`
  >> qexists_tac `left_numerator`
  >> qexists_tac `right_numerator`
  >> qexists_tac `right_denominator`
  >> simp
       [compute_boundedCase16594ObjectInversePrimitiveEvalTheory.bounded_case16594_object_q_positive_inv_cv_decodes]
QED

Theorem bounded_case16594_object_q_positive_inv_le_right_of_ints:
  bounded_object_q_ints left =
      SOME (left_numerator,left_denominator) /\
  bounded_object_q_ints right =
      SOME (right_numerator,right_denominator) /\
  0 < left_numerator /\
  left_denominator * right_denominator <=
      right_numerator * left_numerator ==>
  bounded_object_q_le_cv
    (bounded_case16594_object_q_positive_inv_cv left) right
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectSqrtCertificateExactEvalTheory.bounded_case16594_object_q_le_of_ints
  >> qexists_tac `left_numerator`
  >> qexists_tac `left_denominator`
  >> qexists_tac `right_denominator`
  >> qexists_tac `right_numerator`
  >> simp
       [compute_boundedCase16594ObjectInversePrimitiveEvalTheory.bounded_case16594_object_q_positive_inv_cv_decodes]
QED

Theorem bounded_case16594_object_positive_inv_certificate_exact_conditions:
  bounded_object_q_positive_inv_certificate_exact input output ==>
  ?input_lower input_upper output_lower output_upper
   input_lower_numerator input_lower_denominator
   input_upper_numerator input_upper_denominator
   output_lower_numerator output_lower_denominator
   output_upper_numerator output_upper_denominator.
    input = Pair input_lower input_upper /\
    output = Pair output_lower output_upper /\
    bounded_object_q_ints input_lower =
      SOME (input_lower_numerator,input_lower_denominator) /\
    bounded_object_q_ints input_upper =
      SOME (input_upper_numerator,input_upper_denominator) /\
    bounded_object_q_ints output_lower =
      SOME (output_lower_numerator,output_lower_denominator) /\
    bounded_object_q_ints output_upper =
      SOME (output_upper_numerator,output_upper_denominator) /\
    bounded_object_q_encoded output_lower /\
    bounded_object_q_encoded output_upper /\
    0 < input_lower_numerator /\
    0 < input_upper_numerator /\
    bounded_object_q_le_cv output_lower
      (bounded_case16594_object_q_positive_inv_cv input_upper) /\
    bounded_object_q_le_cv
      (bounded_case16594_object_q_positive_inv_cv input_lower) output_upper
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> simp
       [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_object_q_positive_inv_certificate_exact_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> every_case_tac
  >> gvs []
  >> strip_tac
  >> simp [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> rpt conj_tac
  >> metis_tac
       [bounded_case16594_object_q_le_positive_inv_right_of_ints,
        bounded_case16594_object_q_positive_inv_le_right_of_ints]
QED

Theorem bounded_case16594_object_q_interval_inv_certificate_exact_eval:
  bounded_object_q_positive_inv_certificate_exact input output /\
  4 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [from_cv input;from_cv output]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> imp_res_tac
       bounded_case16594_object_positive_inv_certificate_exact_conditions
  >> gvs []
  >> irule
       (REWRITE_RULE
         [compute_execTheory.from_cv_def]
         compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_q_interval_inv_certificate_conditions_eval)
  >> simp []
QED

val _ = export_theory ();
