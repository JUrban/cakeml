(* Verified x64 compilation of the sequential genuine case16594 parser. *)
Theory compute_boundedPackedSequentialInputCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedPackedSequentialInputProg

Theorem compute_bounded_packed_sequential_case16594_compiled =
  eval_cake_compile_x64 "bounded_packed_sequential_case16594_"
    compute_bounded_packed_sequential_case16594_prog_def
    "compute_bounded_packed_sequential_case16594.S";

val _ = export_theory ();
