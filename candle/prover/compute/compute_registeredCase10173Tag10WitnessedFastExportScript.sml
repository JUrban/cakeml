Theory compute_registeredCase10173Tag10WitnessedFastExport
Ancestors
  compute_registeredCase10173Tag10WitnessedFastProg
Libs
  preamble astToSexprLib

val prog =
  rhs (concl
    compute_registeredCase10173Tag10WitnessedFastProgTheory.compute_registered_case10173_tag10_witnessed_fast_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_registered_case10173_tag10_witnessed_fast.sexp" prog;

val _ = export_theory ();
