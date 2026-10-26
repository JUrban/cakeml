(*****************************************************************************
 * Stable four-payload development interface shared by genuine NL families.
 *
 * Family selection is by complete authenticated source/evidence contracts,
 * never by basename or a caller-supplied family tag.  Adding a proved family
 * may extend the internal disjunction without changing the call shape.
 *****************************************************************************)
Theory compute_registeredNLExternalWitnessedChecker
Ancestors
  compute_registeredCase10173ExternalWitnessedChecker
  compute_registeredCase16594ExternalWitnessedChecker
Libs
  bossLib preamble

Definition registered_nl_external_witnessed_checker_def:
  registered_nl_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots <=>
    registered_case10173_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots \/
    registered_case16594_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots
End

Theorem registered_nl_external_witnessed_checker_case10173:
  registered_case10173_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots ==>
  registered_nl_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots
Proof
  simp [registered_nl_external_witnessed_checker_def]
QED

Theorem registered_nl_external_witnessed_checker_case16594:
  registered_case16594_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots ==>
  registered_nl_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots
Proof
  simp [registered_nl_external_witnessed_checker_def]
QED

val _ = export_theory ();
