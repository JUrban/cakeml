Theory compute_boundedCase16594WordWholeDirectProbeExport
Ancestors
  compute_boundedCase16594WordWholeDirectProbeProg
Libs
  preamble astToSexprLib

val prog =
  rhs
    (concl
      compute_boundedCase16594WordWholeDirectProbeProgTheory.compute_bounded_case16594_word_whole_direct_probe_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_bounded_case16594_word_whole_direct_probe.sexp" prog;

val _ = export_theory ();
