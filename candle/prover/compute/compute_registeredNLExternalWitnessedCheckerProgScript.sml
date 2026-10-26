(* Translation of the stable four-payload nonlinear checker interface. *)
Theory compute_registeredNLExternalWitnessedCheckerProg
Ancestors
  compute_registeredNLCase16594CheckProg
  compute_cvPackedBytesRuntime
  compute_cvNativeRuntime
  compute_registeredNLExternalWitnessedChecker
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_registeredNLCase16594CheckProg";

(* Compact certificate construction. *)
val _ = translate
  compute_cvPackedBytesTheory.cv_packed_bytes_chunk_limit_def;
val _ = translate cv_pack_byte_chunk_aux_def;
val _ = translate cv_packed_byte_leaf_def;
val _ = translate cv_packed_byte_branch_def;
val _ = translate cv_pack_byte_leaves_aux_def;
val _ = translate cv_pack_byte_tree_round_def;
val _ = translate cv_balance_byte_tree_def;
val _ = translate cv_pack_byte_tree_def;

(* Canonical external cv-data parser. *)
val _ = translate cv_flat_space_def;
val _ = translate cv_flat_skip_space_def;
val _ = translate cv_flat_digit_value_def;
val _ = translate cv_flat_parse_digits_def;
val _ = translate cv_flat_num_result_def;
val _ = translate cv_flat_parse_term_def;
val _ = translate cv_flat_parse_one_def;
val _ = translate cv_flat_parse_list_aux_def;
val _ = translate cv_flat_parse_list_def;

(* The existing compact native cv spelling used by genuine case 16594. *)
val _ = translate cv_native_parse_term_def;
val _ = translate cv_native_parse_one_def;
val _ = translate cv_external_parse_one_def;

(* Certificate decoding and the previously proved case-10173 checker. *)
val _ = translate compute_cvPackedBytesTheory.cv_unpack_byte_chunk_def;
val _ = translate compute_cvPackedBytesTheory.cv_unpack_byte_tree_append_def;
val _ = translate compute_cvPackedBytesTheory.cv_unpack_byte_tree_def;
val _ = translate compute_pureFastTheory.compute_exp_to_cv_def;
val _ = translate
  compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def;
val _ = translate
  compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_source_program_def;
val _ = translate
  compute_registeredCase10173AuthenticatedFastDispatchTheory.registered_case10173_decimal_authenticated_fast_checker_def;
val _ = translate
  compute_registeredCase10173ExternalWitnessedCheckerTheory.registered_case10173_external_witnessed_checker_def;

(* General fail-closed source decoding and the second genuine family. *)
val _ = translate
  compute_boundedAnalyticProgramCVTheory.bounded_rational_of_cv_def;
val _ = translate
  compute_boundedAnalyticProgramCVTheory.bounded_poly_instruction_of_cv_def;
val _ = translate
  compute_boundedAnalyticProgramCVTheory.bounded_poly_program_of_cv_def;
val _ = translate
  compute_boundedAnalyticProgramCVTheory.bounded_sqrt_placeholder_cv_def;
val _ = translate
  compute_boundedAnalyticProgramCVTheory.bounded_analytic_instruction_of_cv_def;
val _ = translate
  compute_boundedAnalyticProgramCVTheory.bounded_analytic_program_of_cv_def;
val _ = translate
  compute_registeredCase16594ExternalWitnessedCheckerTheory.registered_case16594_external_witnessed_checker_def;
val _ = translate
  compute_registeredNLExternalWitnessedCheckerTheory.registered_nl_external_witnessed_checker_def;

val _ = export_theory ();
