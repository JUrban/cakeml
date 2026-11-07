(*****************************************************************************
 * External byte/cv-data input support for the bounded case-16594 G6 probe. *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeExternalInputProg
Ancestors
  compute_boundedCase16594WordWholeCheckerProg
  compute_cvPackedBytesRuntime
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends
  "compute_boundedCase16594WordWholeCheckerProg";

(* Compact certificate construction. *)
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_pack_byte_chunk_aux_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_packed_byte_leaf_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_packed_byte_branch_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_pack_byte_leaves_aux_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_pack_byte_tree_round_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_balance_byte_tree_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_pack_byte_tree_def;

(* Canonical line-oriented cv-data parser. *)
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_space_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_skip_space_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_digit_value_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_parse_digits_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_num_result_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_parse_term_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_parse_one_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_parse_list_aux_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_parse_list_def;

val _ = export_theory ();
