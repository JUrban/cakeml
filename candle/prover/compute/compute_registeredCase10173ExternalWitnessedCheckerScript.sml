Theory compute_registeredCase10173ExternalWitnessedChecker
Ancestors
  compute_cvPackedBytes
  compute_registeredCase10173AuthenticatedFastDispatch
Libs
  bossLib preamble

Definition registered_case10173_external_witnessed_checker_def:
  registered_case10173_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots <=>
    case cv_unpack_byte_tree certificate of
    | NONE => F
    | SOME bytes =>
        registered_case10173_decimal_authenticated_fast_checker
          bytes source_program encoded_jobs encoded_roots
End

val _ = export_theory ();
