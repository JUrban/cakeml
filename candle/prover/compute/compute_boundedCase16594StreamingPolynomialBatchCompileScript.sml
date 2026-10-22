(* Verified x64 compilation of the streaming genuine polynomial batch. *)
Theory compute_boundedCase16594StreamingPolynomialBatchCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedCase16594StreamingPolynomialBatchProg

Theorem compute_bounded_case16594_streaming_polynomial35_batch_compiled =
  eval_cake_compile_x64 "case16594_streaming_polynomial35_batch_"
    compute_bounded_case16594_streaming_polynomial35_batch_prog_def
    "compute_bounded_case16594_streaming_polynomial35_batch.S";

val _ = export_theory ();
