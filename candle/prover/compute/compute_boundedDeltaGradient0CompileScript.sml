(* Verified x64 compilation of the complete case16594 gradient-0 batch. *)
Theory compute_boundedDeltaGradient0Compile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedDeltaGradient0Prog

Theorem compute_bounded_delta_gradient0_compiled =
  eval_cake_compile_x64 "delta_gradient0_"
    compute_bounded_delta_gradient0_prog_def
    "compute_bounded_delta_gradient0.S";

val _ = export_theory ();
