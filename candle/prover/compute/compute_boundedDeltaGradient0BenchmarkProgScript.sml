(*
  In-process recurring benchmark for the complete case16594 gradient-0 batch.
  The closed result is checked after every iteration, so the benchmark cannot
  hide a failed or overflowed computation behind its final observation.
*)
Theory compute_boundedDeltaGradient0BenchmarkProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedDeltaGradient0Prog

val _ = translation_extends "compute_boundedDeltaGradient0Prog";

Definition bounded_delta_gradient0_repeat_def:
  bounded_delta_gradient0_repeat 0 = T ∧
  bounded_delta_gradient0_repeat (SUC remaining) =
    (bounded_delta_gradient0_complete_ok () ∧
     bounded_delta_gradient0_repeat remaining)
End

val bounded_delta_gradient0_repeat_v =
  translate bounded_delta_gradient0_repeat_def;

Quote main = cakeml:
  if bounded_delta_gradient0_repeat 1000 then () else raise Bind;
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

Definition compute_bounded_delta_gradient0_benchmark_prog_def:
  compute_bounded_delta_gradient0_benchmark_prog = ^prog
End

val _ = export_theory ();
