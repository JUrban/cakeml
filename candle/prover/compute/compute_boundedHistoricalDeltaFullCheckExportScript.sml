(* Development export for compilation by the existing executable `cake`. *)
Theory compute_boundedHistoricalDeltaFullCheckExport
Libs
  preamble astToSexprLib
Ancestors
  compute_boundedHistoricalDeltaFullCheckProg

val prog =
  compute_bounded_historical_delta_full_check_prog_def
  |> concl
  |> rhs;

val _ =
  astToSexprLib.write_ast_to_file
    "compute_bounded_historical_delta_full_check.sexp"
    prog;

val _ = export_theory ();
