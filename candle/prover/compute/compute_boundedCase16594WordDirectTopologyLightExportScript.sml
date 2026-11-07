Theory compute_boundedCase16594WordDirectTopologyLightExport
Ancestors
  compute_boundedCase16594WordDirectTopologyLightProg
Libs
  preamble astToSexprLib

val prog =
  rhs
    (concl
      compute_boundedCase16594WordDirectTopologyLightProgTheory.compute_bounded_case16594_word_direct_topology_light_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_bounded_case16594_word_direct_topology_light.sexp" prog;

val _ = export_theory ();
