(*****************************************************************************
 * Reusable cv_compute translations for the case-16594 certificate trees.
 *
 * The two balanced source trees are large but immutable.  Keeping their
 * translations in one prerequisite theory pays the export cost once and lets
 * focused cell experiments evaluate only the short lookup plans they use.
 *****************************************************************************)
Theory compute_boundedCase16594PreparedCertificatesCV
Ancestors
  compute_boundedCase16594PreparedCertificates
Libs
  bossLib preamble cv_transLib

val _ = cv_trans
  compute_boundedCase16594PreparedCertificatesTheory.bounded_case16594_tree_lookup_def;
val _ = cv_trans
  compute_boundedCase16594PreparedCertificatesTheory.bounded_case16594_prepare_raw_interval_def;
val _ = cv_trans
  compute_boundedCase16594AnalyticCertificateDataTheory.bounded_case16594_interval_tree_def;
val _ = cv_trans
  compute_boundedCase16594PreparedCertificatesTheory.bounded_case16594_prepare_interval_def;
val _ = cv_trans
  compute_boundedCase16594PreparedCertificatesTheory.bounded_case16594_prepare_interval_list_def;
val _ = cv_trans
  compute_boundedCase16594PreparedCertificatesTheory.bounded_case16594_prepare_interval_option_def;
val _ = cv_trans
  compute_boundedCase16594AnalyticCertificateDataTheory.bounded_case16594_certificate_tree_def;
val _ = cv_trans
  compute_boundedCase16594PreparedCertificatesTheory.bounded_case16594_prepare_certificate_def;
val _ = cv_trans
  compute_boundedCase16594PreparedCertificatesTheory.bounded_case16594_prepare_certificate_list_def;

val _ = export_theory ();
