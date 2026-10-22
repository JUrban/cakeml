(* Development export of the genuine complete cell-0 gate for direct cake. *)
Theory compute_boundedCase10173HistoricalCell0SexprExport
Libs
  preamble astToSexprLib
Ancestors
  compute_boundedCase10173HistoricalCell0Prog

val prog =
  rhs (concl
    compute_boundedCase10173HistoricalCell0ProgTheory.compute_bounded_case10173_historical_cell0_prog_def);

val _ =
  astToSexprLib.write_ast_to_file
    "compute_bounded_case10173_historical_cell0.sexp"
    prog;

val _ = export_theory ();
