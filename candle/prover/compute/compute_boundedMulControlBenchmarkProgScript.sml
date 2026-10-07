(*
  Closed verified program for the matched word-XOR recursion control.
*)
Theory compute_boundedMulControlBenchmarkProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedProg

val _ = translation_extends "compute_boundedProg";

val bounded_word64_mul_control_benchmark_v =
  translate compute_boundedTheory.bounded_word64_mul_control_benchmark_def;
val bounded_word64_mul_control_ok_v =
  translate compute_boundedTheory.bounded_word64_mul_control_ok_def;

Quote main = cakeml:
  if bounded_word64_mul_control_ok () then () else raise Bind;
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

Definition compute_bounded_mul_control_benchmark_prog_def:
  compute_bounded_mul_control_benchmark_prog = ^prog
End

val _ = export_theory ();
