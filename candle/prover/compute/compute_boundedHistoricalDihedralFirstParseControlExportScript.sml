(* Development export for compilation by the existing executable `cake`. *)
Theory compute_boundedHistoricalDihedralFirstParseControlExport
Libs
  preamble astToSexprLib
Ancestors
  compute_boundedHistoricalDihedralFirstParseControlProg

val prog =
  compute_bounded_historical_dihedral_first_parse_control_prog_def
  |> concl
  |> rhs;

val _ =
  astToSexprLib.write_ast_to_file
    "compute_bounded_historical_dihedral_first_parse_control.sexp"
    prog;

val _ = export_theory ();
