(*****************************************************************************
 * Semantic handoff from the accepted case-16594 source payload to the
 * ordinary source Taylor-completion evaluator.
 *
 * This layer is deliberately generic in the cell data.  It extracts the
 * transient 6-by-6 Hessian rows from the accepted compact 21-entry Hessian
 * and invokes the proved exact-rational completion evaluator.  It performs
 * no closed-data evaluation and makes no final inequality claim.
 *****************************************************************************)
Theory compute_boundedCase16594SourceCompletionBridge
Ancestors
  compute_boundedCase16594FullSourceContract
  compute_boundedPackedSourceTaylorArithmeticEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_source_accept6_hessian_rows:
  bounded_packed_object_source_accept6 radii center_value center_gradient
      hessian ==>
  ?rows.
    bounded_hessian64_rows hessian = SOME rows /\
    EVERY (EVERY bounded_packed_q_interval_encoded) rows /\
    LENGTH rows = 6 /\
    EVERY (\row. LENGTH row = 6) rows /\
    LENGTH center_gradient = LENGTH rows
Proof
  rw
    [compute_boundedPackedObjectEntryRefinementTheory.bounded_packed_object_source_accept6_def]
  >> fs
       [listTheory.LENGTH_EQ_NUM_compute,
        compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> gvs [listTheory.EVERY_DEF]
QED

Theorem bounded_case16594_six_by_six_row_sum:
  LENGTH rows = 6 /\
  EVERY (\row. LENGTH row = 6) rows ==>
  SUM (MAP LENGTH rows) = 36
Proof
  rw [listTheory.LENGTH_EQ_NUM_compute]
  >> gvs [listTheory.EVERY_DEF]
QED

Theorem bounded_case16594_source_accept6_completion_eval:
  bounded_packed_object_source_accept6 radii center_value center_gradient
      hessian /\
  61200 < clock ==>
  ?rows value_bound gradient_bounds.
    bounded_hessian64_rows hessian = SOME rows /\
    compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_dim_taylor_model_result_complete»
          [from_cv (bounded_object_q_cv_list radii);
           from_cv domain_cv;
           from_cv
             (Pair center_value
               (bounded_object_q_cv_list center_gradient));
           from_cv (bounded_packed_source_q_cv_matrix rows)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_packed_source_q_taylor_result_cv domain_cv
            (Pair
              (bounded_packed_source_q_fixed_interval_round_cv center_value)
              (bounded_object_q_cv_list
                (MAP bounded_packed_source_q_fixed_interval_round_cv
                  center_gradient)))
            (bounded_packed_source_q_fixed_interval_round_cv value_bound)
            (bounded_object_q_cv_list
              (MAP bounded_packed_source_q_fixed_interval_round_cv
                gradient_bounds))
            (bounded_packed_source_q_cv_matrix
              (MAP
                (MAP bounded_packed_source_q_fixed_interval_round_cv)
                rows)))),refs) /\
    bounded_packed_source_q_interval_cv_equiv value_bound
      (bounded_packed_source_q_taylor_model_value_cv
        (bounded_packed_source_q_fixed_interval_round_cv center_value)
        radii
        (MAP bounded_packed_source_q_fixed_interval_round_cv
          center_gradient)
        (MAP
          (MAP bounded_packed_source_q_fixed_interval_round_cv)
          rows)) /\
    LIST_REL bounded_packed_source_q_interval_cv_equiv gradient_bounds
      (bounded_packed_source_q_taylor_model_gradient_cv radii
        (MAP bounded_packed_source_q_fixed_interval_round_cv
          center_gradient)
        (MAP
          (MAP bounded_packed_source_q_fixed_interval_round_cv)
          rows))
Proof
  strip_tac
  >> drule bounded_case16594_source_accept6_hessian_rows
  >> disch_then (qx_choose_then `rows` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`radii` |-> `radii`, `center_value` |-> `center_value`,
          `gradient` |-> `center_gradient`, `hessian` |-> `rows`,
          `clock` |-> `clock`, `domain_cv` |-> `domain_cv`,
          `refs` |-> `refs`]
         bounded_packed_source_q_result_complete_relation_eval)
  >> impl_tac
  >- (`SUM (MAP LENGTH rows) = 36` by
        metis_tac [bounded_case16594_six_by_six_row_sum]
      >> fs
           [compute_boundedPackedObjectEntryRefinementTheory.bounded_packed_object_source_accept6_def])
  >> disch_then
       (qx_choose_then `value_bound`
         (qx_choose_then `gradient_bounds` strip_assume_tac))
  >> qexists_tac `rows`
  >> qexists_tac `value_bound`
  >> qexists_tac `gradient_bounds`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
