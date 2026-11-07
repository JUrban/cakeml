Theory compute_boundedCase16594WordWholeProbeExport
Ancestors
  compute_boundedCase16594WordWholeProbeProg
Libs
  preamble astToSexprLib

val prog =
  rhs
    (concl
      compute_boundedCase16594WordWholeProbeProgTheory.compute_bounded_case16594_word_whole_probe_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_bounded_case16594_word_whole_probe.sexp" prog;

val _ = export_theory ();
