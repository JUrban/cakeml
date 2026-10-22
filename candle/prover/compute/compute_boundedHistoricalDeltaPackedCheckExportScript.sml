(* Development export of the genuine prefix-128 historical delta gate.

   This serializes the already-translated CakeML AST for use with the
   executable CakeML compiler.  It is intentionally separate from the
   verified CompileTheory: the resulting executable is a fast development
   prototype, not release evidence backed by a fresh compilation theorem. *)
Theory compute_boundedHistoricalDeltaPackedCheckExport
Libs
  preamble astToSexprLib
Ancestors
  compute_boundedHistoricalDeltaPackedCheckProg

val prog =
  compute_bounded_historical_delta_packed_check_prog_def
  |> concl
  |> rhs;

val _ =
  astToSexprLib.write_ast_to_file
    "compute_bounded_historical_delta_packed_check.sexp"
    prog;

val _ = export_theory ();
