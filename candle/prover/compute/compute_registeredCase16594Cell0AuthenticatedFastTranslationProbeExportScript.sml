(******************************************************************************
 * Development export for direct ./cake compilation of the exact callback.   *
 ******************************************************************************)
Theory compute_registeredCase16594Cell0AuthenticatedFastTranslationProbeExport
Ancestors
  compute_registeredCase16594Cell0AuthenticatedFastTranslationProbe
Libs
  preamble astToSexprLib

val prog =
  rhs
    (concl
      compute_registeredCase16594Cell0AuthenticatedFastTranslationProbeTheory.compute_registered_case16594_cell0_authenticated_fast_translation_probe_prog_def);

val _ =
  astToSexprLib.write_ast_to_file
    "compute_registered_case16594_cell0_authenticated_fast_translation_probe.sexp"
    prog;

val _ = export_theory ();
