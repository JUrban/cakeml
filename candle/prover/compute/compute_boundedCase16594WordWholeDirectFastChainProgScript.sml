(*****************************************************************************
 * Saved translator boundary for the production direct case-16594 callback. *
 *                                                                           *
 * The complete numerical checker and direct-topology runner are inherited   *
 * from their already proved translation state.  This small suffix adds only *
 * literal/witness dispatch, the sound direct callback, and the ordinary     *
 * pure-evaluator fallback.  A kernel integration can therefore extend this  *
 * state without retranslating the complete checker.                          *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeDirectFastChainProg
Ancestors
  compute_boundedCase16594WordWholeDirectCheckerProg
  compute_boundedCase16594WordWholeDirectFastChain
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends
  "compute_boundedCase16594WordWholeDirectCheckerProg";

val _ = translate
  compute_payloadListFastTheory.compute_literal_payloads_def;
val _ = translate
  compute_payloadListFastTheory.compute_literal_call_payloads_def;

val _ = translate
  compute_witnessedPayloadListFastTheory.compute_literal_witnessed_payloads_def;
val _ = translate
  compute_witnessedPayloadListFastTheory.compute_witnessed_payloads_fast_eval_def;
val _ = translate
  compute_witnessedPayloadListFastTheory.compute_witnessed_payload4_list_checker_def;

fun translate_closed def =
  def |> CONV_RULE (RAND_CONV EVAL) |> translate;

(* The direct-checker state deliberately bypasses the older topology-call
   state, so install its small nine-equation HOL Light suffix and the combined
   approved environment here before closing over it in the callback. *)
val _ = translate_closed
  compute_boundedCase16594Cell0WholeHolLightDataTheory.bounded_case16594_cell0_whole_hol_light_ceqs_def;
val _ = translate
  compute_boundedCase16594Cell0WholeCombinedEntryTheory.bounded_case16594_cell0_whole_combined_ceqs_def;

val _ = translate
  compute_boundedCase16594WordWholeDirectWitnessedFastDispatchTheory.bounded_case16594_word_whole_direct_bounded_checker_def;
val _ = translate
  compute_boundedCase16594WordWholeDirectWitnessedFastDispatchTheory.bounded_case16594_word_whole_direct_witnessed_list_checker_def;
val _ = translate
  compute_boundedCase16594WordWholeDirectWitnessedFastDispatchTheory.bounded_case16594_word_whole_direct_witnessed_fast_eval_def;

val _ = translate compute_pureFastTheory.compute_pure_fast_fuel_def;
val _ = translate compute_pureFastTheory.compute_pure_fast_eval_def;

val _ = translate
  compute_boundedCase16594WordWholeDirectFastChainTheory.compute_case16594_direct_genuine_fast_eval_def;

val _ = export_theory ();
