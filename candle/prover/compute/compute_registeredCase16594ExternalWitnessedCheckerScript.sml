(*****************************************************************************
 * Four-payload data boundary for the genuine case-16594 checker.
 *
 * The packed byte payload contains the 875 boxes and their typed scalar
 * certificates.  The source payload is independently decoded and must equal
 * the authenticated 167-instruction program.  This family has no separate
 * job or root payload after packing, so both positions must carry the exact
 * empty cv list rather than being ignored.
 *****************************************************************************)
Theory compute_registeredCase16594ExternalWitnessedChecker
Ancestors
  compute_cvPackedBytes
  compute_boundedCase16594SourceCVData
  compute_boundedPackedSequentialCase16594Check
Libs
  bossLib preamble

Definition registered_case16594_external_witnessed_checker_def:
  registered_case16594_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots <=>
    case cv_unpack_byte_tree certificate of
    | NONE => F
    | SOME bytes =>
        bounded_analytic_program_of_cv source_program =
          SOME bounded_case16594_program /\
        encoded_jobs = Num 0 /\
        encoded_roots = Num 0 /\
        bounded_packed_chars_case16594_complete_check bytes
End

Theorem registered_case16594_external_witnessed_checker_contract:
  registered_case16594_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots ==>
  ?bytes.
    cv_unpack_byte_tree certificate = SOME bytes /\
    bounded_analytic_program_of_cv source_program =
      SOME bounded_case16594_program /\
    encoded_jobs = Num 0 /\
    encoded_roots = Num 0 /\
    bounded_packed_chars_case16594_complete_check bytes
Proof
  rw [registered_case16594_external_witnessed_checker_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case16594_external_witnessed_checker_source_ready:
  bounded_analytic_program_of_cv bounded_case16594_source_program_cv =
    SOME bounded_case16594_program
Proof
  ACCEPT_TAC
    compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes
QED

Theorem registered_case16594_external_witnessed_checker_rejects_bad_source:
  bounded_analytic_program_of_cv source_program <>
      SOME bounded_case16594_program ==>
  ~registered_case16594_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots
Proof
  rw [registered_case16594_external_witnessed_checker_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case16594_external_witnessed_checker_rejects_payload_aliases:
  encoded_jobs <> Num 0 \/ encoded_roots <> Num 0 ==>
  ~registered_case16594_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots
Proof
  rw [registered_case16594_external_witnessed_checker_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case16594_external_witnessed_checker_rejects_bad_certificate:
  cv_unpack_byte_tree certificate = NONE ==>
  ~registered_case16594_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots
Proof
  simp [registered_case16594_external_witnessed_checker_def]
QED

val _ = export_theory ();
