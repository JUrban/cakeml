(*****************************************************************************
 * Exact fixed-scale values handed to the unchanged object-q evaluator.     *
 *****************************************************************************)
Theory compute_boundedCase16594WordConversionProg
Ancestors
  compute_evalPureBaseProg
  compute_boundedAnalyticObjectCertificateRefinement
  compute_boundedAnalyticObjectCompleteRefinement
  compute_boundedPackedObjectEntryContract
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_evalPureBaseProg";

val _ = translate
  compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def;
val _ = translate
  compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_signed64_object_q_cv_def;
val _ = translate
  compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_object_q_cv_def;
val _ = translate
  compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_def;
val _ = translate
  compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def;

val _ = export_theory ();
