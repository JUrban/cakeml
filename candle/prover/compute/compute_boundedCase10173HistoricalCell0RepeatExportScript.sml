(* Development export of the complete cell repeat harness for direct cake. *)
Theory compute_boundedCase10173HistoricalCell0RepeatExport
Libs
  preamble astToSexprLib
Ancestors
  compute_boundedCase10173HistoricalCell0RepeatProg

val prog =
  rhs (concl
    compute_boundedCase10173HistoricalCell0RepeatProgTheory.compute_bounded_case10173_historical_cell0_repeat_prog_def);

val _ =
  astToSexprLib.write_ast_to_file
    "compute_bounded_case10173_historical_cell0_repeat.sexp"
    prog;

val _ = export_theory ();
