Theory compute_registeredNLExternalWitnessedFastExport
Ancestors
  compute_registeredNLExternalWitnessedFastProg
Libs
  preamble astToSexprLib

val prog =
  rhs (concl
    compute_registeredNLExternalWitnessedFastProgTheory.compute_registered_nl_external_witnessed_fast_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_registered_nl_external_witnessed_fast.sexp" prog;

val _ = export_theory ();
