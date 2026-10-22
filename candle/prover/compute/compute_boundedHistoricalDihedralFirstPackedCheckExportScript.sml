(* Development export for compilation by the existing cake executable. *)
Theory compute_boundedHistoricalDihedralFirstPackedCheckExport
Libs
  preamble astToSexprLib
Ancestors
  compute_boundedHistoricalDihedralFirstPackedCheckProg

val prog =
  rhs (concl
    compute_boundedHistoricalDihedralFirstPackedCheckProgTheory.compute_bounded_historical_dihedral_first_check_prog_def);

val _ =
  astToSexprLib.write_ast_to_file
    "compute_bounded_historical_dihedral_first_check.sexp"
    prog;

val _ = export_theory ();
