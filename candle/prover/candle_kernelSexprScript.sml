(* Export the current proved Candle prefix for direct compiler experiments. *)
Theory candle_kernelSexpr
Ancestors
  candle_kernelProg
Libs
  preamble astToSexprLib

val prog = rhs (concl candle_kernelProgTheory.candle_code_def);

val _ = astToSexprLib.write_ast_to_file "candle_kernel.sexp" prog;

val _ = export_theory ();
