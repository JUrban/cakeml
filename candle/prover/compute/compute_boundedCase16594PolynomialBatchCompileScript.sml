(* Verified x64 compilation of the genuine case16594 polynomial-only batch. *)
Theory compute_boundedCase16594PolynomialBatchCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedCase16594PolynomialBatchProg

Theorem compute_bounded_case16594_polynomial35_batch_compiled =
  eval_cake_compile_x64 "case16594_polynomial35_batch_"
    compute_bounded_case16594_polynomial35_batch_prog_def
    "compute_bounded_case16594_polynomial35_batch.S";

val _ = export_theory ();
