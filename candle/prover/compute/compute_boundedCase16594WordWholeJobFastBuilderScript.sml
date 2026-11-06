(*****************************************************************************
 * First-order encoded-job builder for the case-16594 production callback.   *
 *                                                                           *
 * The logical job definition uses MAP followed by a cv-list encoder.  That  *
 * definition is convenient for proofs but leaves a higher-order MAP at the  *
 * CV translation boundary.  This equivalent recursive builder is directly  *
 * translatable and preserves the exact existing payload representation.     *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeJobFastBuilder
Ancestors
  compute_boundedCase16594WordWholeJobProducer
Libs
  bossLib preamble cv_transLib

Definition bounded_case16594_interval64_object_q_cv_list_def:
  bounded_case16594_interval64_object_q_cv_list [] = Num 0 /\
  bounded_case16594_interval64_object_q_cv_list (interval::intervals) =
    Pair (bounded_interval64_object_q_cv interval)
      (bounded_case16594_interval64_object_q_cv_list intervals)
End

Theorem bounded_case16594_interval64_object_q_cv_list_eq:
  bounded_case16594_interval64_object_q_cv_list intervals =
    bounded_object_q_cv_list
      (MAP bounded_interval64_object_q_cv intervals)
Proof
  Induct_on `intervals`
  >> simp
       [bounded_case16594_interval64_object_q_cv_list_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

Definition bounded_case16594_word_whole_job_fast_def:
  bounded_case16594_word_whole_job_fast word_center_boxes word_outer_boxes
      source_box =
    Pair
      (bounded_case16594_interval64_object_q_cv_list word_outer_boxes)
      (Pair
        (bounded_case16594_interval64_object_q_cv_list word_center_boxes)
        source_box)
End

Theorem bounded_case16594_word_whole_job_fast_eq:
  bounded_case16594_word_whole_job_fast word_center_boxes word_outer_boxes
      source_box =
    bounded_case16594_word_whole_job word_center_boxes word_outer_boxes
      source_box
Proof
  rw
    [bounded_case16594_word_whole_job_fast_def,
     compute_boundedCase16594WordWholeJobProducerTheory.bounded_case16594_word_whole_job_def,
     bounded_case16594_interval64_object_q_cv_list_eq]
QED

val _ = cv_trans
  compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def;
val _ = cv_trans
  compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_signed64_object_q_cv_def;
val _ = cv_trans
  compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_object_q_cv_def;
val _ = cv_trans bounded_case16594_interval64_object_q_cv_list_def;
val _ = cv_trans bounded_case16594_word_whole_job_fast_def;

val _ = export_theory ();
