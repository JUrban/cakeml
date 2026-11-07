(*****************************************************************************
 * Reusable direct-topology translation above the exact numerical runtime.   *
 *****************************************************************************)
Theory compute_boundedCase16594WordDirectTopologyProg
Ancestors
  compute_boundedCase16594WordRuntimeProg
  compute_boundedCase16594WordDirectTopology
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_boundedCase16594WordRuntimeProg";

val _ = translate
  compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_cv_list_length_def;
val _ = translate
  compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_boxes_join_def;
val _ = translate
  compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_boxes_split_exact_from_def;
val _ = translate
  compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_topology_transition_def;
val _ = translate
  compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_topology_run_def;
val _ = translate
  compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_topology_result_def;

val _ = export_theory ();
