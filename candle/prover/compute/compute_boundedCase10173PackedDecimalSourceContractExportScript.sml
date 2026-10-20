(*****************************************************************************
 * Fail-closed development export for the authenticated source contract.
 *
 * A previous version of this target accidentally exported the plain
 * numerical batch main under the source-contract filename.  The translated
 * authenticated checker takes the source jobs and historical roots as
 * explicit arguments; until a closed main supplies those authenticated
 * values, this standalone target must reject rather than silently run the
 * weaker numerical checker.
 *****************************************************************************)
Theory compute_boundedCase10173PackedDecimalSourceContractExport
Ancestors
  compute_boundedCase10173PackedDecimalAuthenticatedProg
Libs
  preamble ml_progLib basis astToSexprLib

val _ = translation_extends
  "compute_boundedCase10173PackedDecimalAuthenticatedProg";

Quote main = cakeml:
  TextIO.print "rejected\n";
End

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand;

Definition compute_bounded_case10173_packed_decimal_source_contract_prog_def:
  compute_bounded_case10173_packed_decimal_source_contract_prog = ^prog
End

val _ = astToSexprLib.write_ast_to_file
  "compute_bounded_case10173_packed_decimal_source_contract.sexp" prog;

val _ = export_theory ();
