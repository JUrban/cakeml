(* Development export for compilation by the existing executable `cake`. *)
Theory compute_boundedHistoricalDihedralSecondPackedCheckExport
Libs
  preamble astToSexprLib
Ancestors
  compute_boundedHistoricalDihedralSecondPackedCheckProg

val prog =
  compute_bounded_historical_dihedral_second_check_prog_def
  |> concl
  |> rhs;

val _ =
  astToSexprLib.write_ast_to_file
    "compute_bounded_historical_dihedral_second_check.sexp"
    prog;

val _ = export_theory ();
