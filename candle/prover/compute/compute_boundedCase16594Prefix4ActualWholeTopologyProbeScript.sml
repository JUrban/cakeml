(*****************************************************************************
 * Genuine four-leaf topology through the actual production job payloads.   *
 *                                                                           *
 * The preceding topology discriminator used dummy numerical fields because *
 * the logical job builder contains a higher-order MAP that cv_trans cannot  *
 * specialize.  The proved-equivalent first-order builder removes that       *
 * translation obstacle.  This theory therefore runs the same genuine        *
 * seven-token topology on the exact four encoded numerical jobs.             *
 *****************************************************************************)
Theory compute_boundedCase16594Prefix4ActualWholeTopologyProbe
Ancestors
  compute_boundedCase16594WordWholeJobFastBuilder
  compute_boundedCase16594Prefix4WholeTopologyProbe
Libs
  bossLib preamble cv_transLib

Definition bounded_case16594_prefix4_actual_whole_jobs_fast_def:
  bounded_case16594_prefix4_actual_whole_jobs_fast =
    Pair
      (bounded_case16594_word_whole_job_fast
        bounded_case16594_cell0_source_word_center_environment
        bounded_case16594_cell0_authenticated_word_box_environment
        bounded_case16594_prefix4_source_box0)
    (Pair
      (bounded_case16594_word_whole_job_fast
        bounded_case16594_prefix4_cell1_word_center_boxes
        bounded_case16594_prefix4_cell1_word_outer_boxes
        bounded_case16594_prefix4_source_box1)
    (Pair
      (bounded_case16594_word_whole_job_fast
        bounded_case16594_prefix4_cell2_word_center_boxes
        bounded_case16594_prefix4_cell2_word_outer_boxes
        bounded_case16594_prefix4_source_box2)
    (Pair
      (bounded_case16594_word_whole_job_fast
        bounded_case16594_prefix4_cell3_word_center_boxes
        bounded_case16594_prefix4_cell3_word_outer_boxes
        bounded_case16594_prefix4_source_box3)
      (Num 0))))
End

Theorem bounded_case16594_prefix4_actual_whole_jobs_fast_eq:
  bounded_case16594_prefix4_actual_whole_jobs_fast =
    bounded_case16594_prefix4_whole_jobs
Proof
  rw
    [bounded_case16594_prefix4_actual_whole_jobs_fast_def,
     compute_boundedCase16594Prefix4WholeTopologyProbeTheory.bounded_case16594_prefix4_whole_jobs_def,
     compute_boundedCase16594WordWholeJobFastBuilderTheory.bounded_case16594_word_whole_job_fast_eq]
QED

(* Translate each closed input once.  The generic recursive encoders and job
   constructor were translated by the fast-builder ancestor. *)
val _ = cv_trans
  compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_environment_def;
val _ = cv_trans
  compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_environment_def;
val _ = cv_trans
  compute_boundedCase16594Prefix4WordConvertedEntryEvalTheory.bounded_case16594_prefix4_cell1_word_center_boxes_def;
val _ = cv_trans
  compute_boundedCase16594Prefix4WordConvertedEntryEvalTheory.bounded_case16594_prefix4_cell1_word_outer_boxes_def;
val _ = cv_trans
  compute_boundedCase16594Prefix4WordConvertedEntryEvalTheory.bounded_case16594_prefix4_cell2_word_center_boxes_def;
val _ = cv_trans
  compute_boundedCase16594Prefix4WordConvertedEntryEvalTheory.bounded_case16594_prefix4_cell2_word_outer_boxes_def;
val _ = cv_trans
  compute_boundedCase16594Prefix4WordConvertedEntryEvalTheory.bounded_case16594_prefix4_cell3_word_center_boxes_def;
val _ = cv_trans
  compute_boundedCase16594Prefix4WordConvertedEntryEvalTheory.bounded_case16594_prefix4_cell3_word_outer_boxes_def;
val _ = cv_trans
  compute_boundedCase16594Prefix4WholeTopologyProbeTheory.bounded_case16594_prefix4_source_q_def;
val _ = cv_trans
  compute_boundedCase16594Prefix4WholeTopologyProbeTheory.bounded_case16594_prefix4_source_interval_def;
val _ = cv_trans
  compute_boundedCase16594Prefix4WholeTopologyProbeTheory.bounded_case16594_prefix4_source_box0_def;
val _ = cv_trans
  compute_boundedCase16594Prefix4WholeTopologyProbeTheory.bounded_case16594_prefix4_source_box1_def;
val _ = cv_trans
  compute_boundedCase16594Prefix4WholeTopologyProbeTheory.bounded_case16594_prefix4_source_box2_def;
val _ = cv_trans
  compute_boundedCase16594Prefix4WholeTopologyProbeTheory.bounded_case16594_prefix4_source_box3_def;
val _ = cv_trans bounded_case16594_prefix4_actual_whole_jobs_fast_def;

val bounded_case16594_prefix4_actual_whole_jobs_fast_literal =
  time cv_eval ``bounded_case16594_prefix4_actual_whole_jobs_fast``;

val bounded_case16594_prefix4_whole_tokens_literal =
  REWRITE_CONV
    [compute_boundedCase16594Prefix4WholeTopologyProbeTheory.bounded_case16594_prefix4_whole_tokens_def]
    ``bounded_case16594_prefix4_whole_tokens``;

val bounded_case16594_prefix4_actual_topology_call =
  ``compute_eval_pure 4096 bounded_case16594_cell0_whole_combined_ceqs
      (App
        «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
        [from_cv (Num 6);
         from_cv bounded_case16594_prefix4_whole_tokens;
         from_cv bounded_case16594_prefix4_actual_whole_jobs_fast;
         from_cv (Num 0)])``;

val bounded_case16594_prefix4_actual_topology_literal_call =
  rhs
    (concl
      (REWRITE_CONV
        [bounded_case16594_prefix4_whole_tokens_literal,
         bounded_case16594_prefix4_actual_whole_jobs_fast_literal]
        bounded_case16594_prefix4_actual_topology_call));

val bounded_case16594_prefix4_actual_topology_pure_eval =
  time cv_eval bounded_case16594_prefix4_actual_topology_literal_call;

val _ = save_thm
  ("bounded_case16594_prefix4_actual_topology_pure_eval",
   bounded_case16594_prefix4_actual_topology_pure_eval);

Theorem bounded_case16594_prefix4_actual_topology_pure_eval_value:
  compute_eval_pure 4096 bounded_case16594_cell0_whole_combined_ceqs
      (App
        «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
        [from_cv (Num 6);
         from_cv bounded_case16594_prefix4_whole_tokens;
         from_cv bounded_case16594_prefix4_actual_whole_jobs_fast;
         from_cv (Num 0)]) =
    SOME
      (from_cv
        (Pair (Num 1)
          (Pair (Num 0)
            (Pair bounded_case16594_prefix4_root_box (Num 0)))))
Proof
  PURE_REWRITE_TAC
    [compute_boundedCase16594Prefix4WholeTopologyProbeTheory.bounded_case16594_prefix4_whole_tokens_def,
     bounded_case16594_prefix4_actual_whole_jobs_fast_literal,
     compute_boundedCase16594Prefix4WholeTopologyProbeTheory.bounded_case16594_prefix4_root_box_def,
     compute_boundedCase16594Prefix4WholeTopologyProbeTheory.bounded_case16594_prefix4_source_interval_def,
     compute_boundedCase16594Prefix4WholeTopologyProbeTheory.bounded_case16594_prefix4_source_q_def]
  >> simp [bounded_case16594_prefix4_actual_topology_pure_eval]
QED

Theorem bounded_case16594_prefix4_actual_topology_eval:
  4096 <= clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App
        «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
        [from_cv (Num 6);
         from_cv bounded_case16594_prefix4_whole_tokens;
         from_cv bounded_case16594_prefix4_actual_whole_jobs_fast;
         from_cv (Num 0)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Num 0)
            (Pair bounded_case16594_prefix4_root_box (Num 0))))),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> simp [bounded_case16594_prefix4_actual_topology_pure_eval_value]
QED

val _ = export_theory ();
