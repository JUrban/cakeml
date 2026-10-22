(* Development export for compilation by the existing executable `cake`. *)
Theory compute_boundedHistoricalDihedralSecondStatusExport
Libs
  preamble astToSexprLib
Ancestors
  compute_boundedHistoricalDihedralSecondStatusProg

val prog =
  compute_bounded_historical_dihedral_second_status_prog_def
  |> concl
  |> rhs;

val _ =
  astToSexprLib.write_ast_to_file
    "compute_bounded_historical_dihedral_second_status.sexp"
    prog;

val _ = export_theory ();
