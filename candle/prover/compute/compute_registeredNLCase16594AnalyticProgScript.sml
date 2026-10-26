(* Extend the authenticated case-10173 translation with the generic
 * fixed-scale analytic tail needed by case 16594.  Both branches already
 * share compute_boundedTaylorMulProg; only the definitions after that common
 * boundary are translated here. *)
Theory compute_registeredNLCase16594AnalyticProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedCase10173PackedDecimalAuthenticatedProg
  compute_boundedTaylorBase
  compute_boundedDeltaTaylor
  compute_boundedTaylorProgram
  compute_boundedAnalyticProgram

val _ = translation_extends
  "compute_boundedCase10173PackedDecimalAuthenticatedProg";

val _ = translate
  compute_boundedTaylorBaseTheory.bounded_interval64_zeros_def;
val _ = translate
  compute_boundedTaylorBaseTheory.bounded_interval64_nth_def;
val _ = translate
  compute_boundedTaylorBaseTheory.bounded_interval64_unit_vector_def;
val _ = translate
  compute_boundedTaylorBaseTheory.bounded_taylor64_constant_def;
val _ = translate
  compute_boundedTaylorBaseTheory.bounded_taylor64_variable_def;

val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_interval64_sum_aux_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_interval64_sum_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_interval64_scale4_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_interval64_list_scale4_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_interval64_mul3_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_interval64_sums_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_pair_products_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_signed_terms_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_apply_signed_terms_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_component_from_products_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_components_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_from_products_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_value_six_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_value_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_interval64_list_add_at_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_neg_derivative_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_indices_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_product_hessian_entry_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_product_hessian_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_four_coordinate_def;

val _ = register_type ``:bounded_taylor64_instruction``;
val _ = translate
  compute_boundedTaylorProgramTheory.bounded_taylor64_stack_well_formed_def;
val _ = translate
  compute_boundedTaylorProgramTheory.bounded_taylor64_neg_complete_def;
val _ = translate
  compute_boundedTaylorProgramTheory.bounded_taylor64_add_complete_def;
val _ = translate
  compute_boundedTaylorProgramTheory.bounded_taylor64_program_step_def;
val _ = translate
  compute_boundedTaylorProgramTheory.bounded_taylor64_program_run_def;
val _ = translate
  compute_boundedTaylorProgramTheory.bounded_taylor64_program_eval_def;

val _ = register_type ``:bounded_analytic64_instruction``;
val _ = register_type ``:bounded_analytic64_certificate``;
val _ = translate
  compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def;
val _ = translate
  compute_boundedAnalyticProgramTheory.bounded_analytic64_program_run_def;
val _ = translate
  compute_boundedAnalyticProgramTheory.bounded_analytic64_program_eval_def;

val _ = export_theory ();
