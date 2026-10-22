(* Export the verified translator output for the direct executable compiler. *)
Theory compute_boundedMulDivDecimalBenchmarkExport
Libs
  preamble astToSexprLib
Ancestors
  compute_boundedMulDivDecimalBenchmarkProg

val prog =
  rhs (concl
    compute_boundedMulDivDecimalBenchmarkProgTheory.compute_bounded_mul_div_decimal_benchmark_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_bounded_mul_div_decimal_benchmark.sexp" prog;

val _ = export_theory ();
