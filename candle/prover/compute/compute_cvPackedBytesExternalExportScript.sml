(* Development S-expression export for the external fast-NL data path. *)
Theory compute_cvPackedBytesExternalExport
Ancestors
  compute_cvPackedBytesExternalProg
Libs
  preamble astToSexprLib

val prog =
  rhs (concl
    compute_cvPackedBytesExternalProgTheory.compute_cv_packed_bytes_external_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_cv_packed_bytes_external.sexp" prog;

val _ = export_theory ();
