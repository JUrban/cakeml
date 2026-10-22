(* Verified x64 compilation of the genuine complete cell-0 gate. *)
Theory compute_boundedCase10173HistoricalCell0Export
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedCase10173HistoricalCell0Prog

val _ =
  eval_cake_compile_x64
    "case10173_historical_cell0_"
    compute_boundedCase10173HistoricalCell0ProgTheory.compute_bounded_case10173_historical_cell0_prog_def
    "compute_bounded_case10173_historical_cell0.S";

val _ = export_theory ();
