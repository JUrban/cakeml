(* Verified x64 compilation of the streaming complete case16594 checker. *)
Theory compute_boundedPackedSequentialCase16594CheckCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedPackedSequentialCase16594CheckProg

Theorem compute_bounded_packed_sequential_case16594_check_compiled =
  eval_cake_compile_x64 "bounded_packed_sequential_case16594_check_"
    compute_bounded_packed_sequential_case16594_check_prog_def
    "compute_bounded_packed_sequential_case16594_check.S";

val _ = export_theory ();
