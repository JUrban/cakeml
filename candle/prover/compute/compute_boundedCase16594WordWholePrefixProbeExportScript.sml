Theory compute_boundedCase16594WordWholePrefixProbeExport
Ancestors
  compute_boundedCase16594WordWholePrefixProbeProg
Libs
  preamble astToSexprLib

val prog =
  rhs
    (concl
      compute_boundedCase16594WordWholePrefixProbeProgTheory.compute_bounded_case16594_word_whole_prefix_probe_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_bounded_case16594_word_whole_prefix_probe.sexp" prog;

val _ = export_theory ();
