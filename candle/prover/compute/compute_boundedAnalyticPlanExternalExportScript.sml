Theory compute_boundedAnalyticPlanExternalExport
Ancestors
  compute_boundedAnalyticPlanExternalProg
Libs
  preamble astToSexprLib

val prog =
  rhs (concl
    compute_boundedAnalyticPlanExternalProgTheory.compute_bounded_analytic_plan_external_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_bounded_analytic_plan_external.sexp" prog;

val _ = export_theory ();
