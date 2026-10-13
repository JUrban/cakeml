(* Export the five-call shared-preparation control for direct cake compilation. *)
Theory compute_pureFastCase10173Cell0BatchExport
Ancestors
  compute_pureFastCase10173Cell0BatchProg
Libs
  preamble astToSexprLib

val prog =
  rhs (concl
    compute_pureFastCase10173Cell0BatchProgTheory.compute_pure_fast_case10173_cell0_batch_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_pure_fast_case10173_cell0_batch.sexp" prog;

val _ = export_theory ();
