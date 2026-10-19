(*****************************************************************************
 * Concrete discriminator for the exact source-rational square-root check.
 *
 * Keep the genuine-data evaluation separate from the reusable contract so
 * edits to the latter do not repeatedly evaluate the large source fixture.
 *****************************************************************************)
Theory compute_boundedCase10173SourceSqrtCertificateCell0
Ancestors
  compute_boundedCase10173SourceSqrtCertificate
Libs
  bossLib preamble

Theorem bounded_case10173_cell0_first_source_coordinate_sqrts_exact:
  ?object_job root_record.
    bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp =
        SOME (Pair object_job root_record) /\
    bounded_case10173_source_coordinate_sqrts_exact object_job
Proof
  simp
    [compute_boundedCase10173RootBindingTheory.bounded_case10173_checked_call_first_job_root_def,
     compute_boundedCase10173SourceSqrtCertificateTheory.bounded_case10173_source_coordinate_sqrts_exact_def,
     compute_boundedCase10173SourceSqrtCertificateTheory.bounded_case10173_source_q_sqrt_prefix_exact_def,
     compute_boundedCase10173SourceSqrtCertificateTheory.bounded_case10173_source_q_sqrt_certificate_exact_def,
     compute_registeredCase10173CenterEnvironmentObjectTheory.registered_case10173_q_center_environment_positive_def,
     compute_registeredCase10173CenterEnvironmentObjectTheory.registered_case10173_q_midpoint_positive_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
     compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def,
     compute_pureFastTheory.compute_exp_to_cv_def]
  >> EVAL_TAC
QED

val _ = export_theory ();
