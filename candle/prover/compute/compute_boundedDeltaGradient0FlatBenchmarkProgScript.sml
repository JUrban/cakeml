(*
  Closed recurring benchmark for the list-free gradient-0 refinement.
*)
Theory compute_boundedDeltaGradient0FlatBenchmarkProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedDeltaGradient0Prog compute_boundedDeltaGradient0Flat

val _ = translation_extends "compute_boundedDeltaGradient0Prog";

val bounded_signed128_option_add_v =
  translate compute_boundedDeltaGradient0FlatTheory.bounded_signed128_option_add_def;
val bounded_signed128_sum11_v =
  translate compute_boundedDeltaGradient0FlatTheory.bounded_signed128_sum11_def;
val bounded_delta_gradient0_flat_coordinates_v =
  translate compute_boundedDeltaGradient0FlatTheory.bounded_delta_gradient0_flat_coordinates_def;
val bounded_delta_gradient0_flat_box_v =
  translate compute_boundedDeltaGradient0FlatTheory.bounded_delta_gradient0_flat_box_def;
val bounded_delta_gradient0_flat_batch_v =
  translate compute_boundedDeltaGradient0FlatTheory.bounded_delta_gradient0_flat_batch_def;
val bounded_delta_gradient0_flat_complete_ok_v =
  translate compute_boundedDeltaGradient0FlatTheory.bounded_delta_gradient0_flat_complete_ok_def;
val bounded_delta_gradient0_flat_repeat_v =
  translate compute_boundedDeltaGradient0FlatTheory.bounded_delta_gradient0_flat_repeat_def;

Quote main = cakeml:
  if bounded_delta_gradient0_flat_repeat 1000 then () else raise Bind;
End

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand;

Definition compute_bounded_delta_gradient0_flat_benchmark_prog_def:
  compute_bounded_delta_gradient0_flat_benchmark_prog = ^prog
End

val _ = export_theory ();
