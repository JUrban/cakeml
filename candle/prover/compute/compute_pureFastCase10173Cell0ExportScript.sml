(* Export the matched genuine-cell evaluator for direct cake compilation. *)
Theory compute_pureFastCase10173Cell0Export
Ancestors
  compute_pureFastCase10173Cell0Prog
Libs
  preamble astToSexprLib

val prog =
  rhs (concl
    compute_pureFastCase10173Cell0ProgTheory.compute_pure_fast_case10173_cell0_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_pure_fast_case10173_cell0.sexp" prog;

val _ = export_theory ();
