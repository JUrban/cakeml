(* CakeML translation of the exact case16594 source-DAG evaluator. *)
Theory compute_boundedCase16594SourceDagEvalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedCase16594PreparedPlanProg
  compute_boundedCase16594SourceDagEval

val _ = translation_extends "compute_boundedCase16594PreparedPlanProg";

val _ = register_type ``:bounded_analytic_dag_node``;

val bounded_analytic_dag_lookup_v =
  translate
    compute_boundedCase16594SourceDagPlanTheory.bounded_analytic_dag_lookup_def;
val bounded_analytic_dag_intern_v =
  translate
    compute_boundedCase16594SourceDagPlanTheory.bounded_analytic_dag_intern_def;
val bounded_analytic_dag_source_node_v =
  translate
    compute_boundedCase16594SourceDagPlanTheory.bounded_analytic_dag_source_node_def;
val bounded_analytic_dag_step_v =
  translate
    compute_boundedCase16594SourceDagPlanTheory.bounded_analytic_dag_step_def;
val bounded_analytic_dag_prepare_v =
  translate
    compute_boundedCase16594SourceDagPlanTheory.bounded_analytic_dag_prepare_def;
val bounded_case16594_source_dag_plan_v =
  translate
    compute_boundedCase16594SourceDagPlanTheory.bounded_case16594_source_dag_plan_def;
val bounded_case16594_source_dag_nodes_v =
  translate
    compute_boundedCase16594SourceDagPlanTheory.bounded_case16594_source_dag_nodes_def;
val bounded_case16594_source_dag_identities_v =
  translate
    compute_boundedCase16594SourceDagPlanTheory.bounded_case16594_source_dag_identities_def;

val bounded_analytic64_instruction_arity_v =
  translate
    compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_instruction_arity_def;
val bounded_analytic64_instruction_uses_certificate_v =
  translate
    compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_instruction_uses_certificate_def;
val bounded_analytic64_current_certificate_v =
  translate
    compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_current_certificate_def;
val bounded_analytic64_reuse_stack_v =
  translate
    compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_reuse_stack_def;
val oEL_v = translate listTheory.oEL_def;
val bounded_analytic64_dag_step_v =
  translate
    compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_dag_step_def;
val bounded_analytic64_dag_run_v =
  translate
    compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_dag_run_def;
val replicate_v = translate REPLICATE;
val bounded_analytic64_dag_eval_v =
  translate
    compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_dag_eval_def;
val bounded_case16594_source_dag_eval_fast_v =
  translate
    compute_boundedCase16594SourceDagEvalTheory.bounded_case16594_source_dag_eval_fast_def;

val _ = export_theory ();
