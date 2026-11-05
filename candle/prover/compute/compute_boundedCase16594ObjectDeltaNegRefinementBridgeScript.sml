(*****************************************************************************
 * Production-state refinement for arbitrary -d(delta)/dx_i inputs.
 *
 * This theory joins the exact source-state evaluator representation to the
 * general object-q negative-delta semantics.  It is deliberately independent
 * of any genuine case-16594 fixture or whole-program callback.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaNegRefinementBridge
Ancestors
  compute_boundedCase16594ObjectDeltaNegSemanticBridge
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_delta_neg_semantic_environment:
  coordinate < 6 /\
  LENGTH center_boxes = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights ==>
  bounded_object_q_delta_neg_derivative_cv semantic_radii center_boxes
      coordinate =
    SOME
      (bounded_object_q_taylor_complete_cv semantic_radii weights T
        (bounded_case16594_object_delta_neg_center_value_environment_cv
          center_boxes coordinate)
        (bounded_case16594_object_delta_neg_center_gradient_environment_cv
          center_boxes coordinate)
        (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate))
Proof
  strip_tac
  >> `center_boxes =
      [EL 0 center_boxes;EL 1 center_boxes;EL 2 center_boxes;
       EL 3 center_boxes;EL 4 center_boxes;EL 5 center_boxes]` by
       (rw [LIST_EQ_REWRITE]
        >> `x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5` by
             intLib.ARITH_TAC
        >> fs [])
  >> mp_tac
       (Q.INST
         [`radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `x0` |-> `EL 0 center_boxes`,
          `x1` |-> `EL 1 center_boxes`,
          `x2` |-> `EL 2 center_boxes`,
          `x3` |-> `EL 3 center_boxes`,
          `x4` |-> `EL 4 center_boxes`,
          `x5` |-> `EL 5 center_boxes`,
          `coordinate` |-> `coordinate`]
         bounded_case16594_object_delta_neg_semantic_trace_six)
  >> impl_tac >- simp []
  >> strip_tac
  >> metis_tac
       [compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_center_value_environment_cv_def,
        compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_center_gradient_environment_cv_def]
QED

Theorem bounded_case16594_object_delta_neg_source_state_semantic:
  coordinate < 6 /\
  LENGTH center_boxes = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_neg_center_value_environment_cv
      center_boxes coordinate) /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_neg_center_gradient_environment_cv
      center_boxes coordinate) /\
  LENGTH
    (bounded_case16594_object_delta_neg_center_gradient_environment_cv
      center_boxes coordinate) = 6 /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) /\
  LENGTH
    (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) = 21 ==>
  ?object_result.
    bounded_object_q_delta_neg_derivative_cv semantic_radii center_boxes
      coordinate = SOME object_result /\
    bounded_object_q_taylor_runtime_equiv
      (bounded_case16594_object_delta_neg_source_state_cv
        (MAP bounded_word64_object_q_cv semantic_radii)
        center_boxes coordinate)
      object_result
Proof
  strip_tac
  >> qexists_tac
       `bounded_object_q_taylor_complete_cv semantic_radii weights T
          (bounded_case16594_object_delta_neg_center_value_environment_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_neg_center_gradient_environment_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate)`
  >> conj_tac
  >- (irule bounded_case16594_object_delta_neg_semantic_environment
      >> simp [])
  >> PURE_REWRITE_TAC
       [compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_source_state_cv_def,
        LET_THM]
  >> BETA_TAC
  >> PURE_REWRITE_TAC
       [compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_taylor_complete_cv_def]
  >> irule
       (SIMP_RULE std_ss []
         (Q.SPEC `T`
           compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_case16594_object_recomplete_word_semantic_equiv))
  >> simp []
QED

Theorem bounded_case16594_object_delta_neg_source_state_eval_semantic:
  coordinate < 6 /\
  EVERY bounded_packed_q_interval_valid_cv center_boxes /\
  LENGTH center_boxes = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_neg_center_value_environment_cv
      center_boxes coordinate) /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_neg_center_gradient_environment_cv
      center_boxes coordinate) /\
  LENGTH
    (bounded_case16594_object_delta_neg_center_gradient_environment_cv
      center_boxes coordinate) = 6 /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) /\
  LENGTH
    (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) = 21 /\
  262500 < clock ==>
  ?object_result.
    bounded_object_q_delta_neg_derivative_cv semantic_radii center_boxes
      coordinate = SOME object_result /\
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv
          (bounded_object_q_cv_list
            (MAP bounded_word64_object_q_cv semantic_radii));
         from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (Num coordinate)]) (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_case16594_object_delta_neg_source_state_cv
            (MAP bounded_word64_object_q_cv semantic_radii)
            center_boxes coordinate)),refs) /\
    bounded_object_q_taylor_runtime_equiv
      (bounded_case16594_object_delta_neg_source_state_cv
        (MAP bounded_word64_object_q_cv semantic_radii)
        center_boxes coordinate)
      object_result
Proof
  strip_tac
  >> `?object_result.
        bounded_object_q_delta_neg_derivative_cv semantic_radii center_boxes
          coordinate = SOME object_result /\
        bounded_object_q_taylor_runtime_equiv
          (bounded_case16594_object_delta_neg_source_state_cv
            (MAP bounded_word64_object_q_cv semantic_radii)
            center_boxes coordinate)
          object_result` by
       (irule bounded_case16594_object_delta_neg_source_state_semantic
        >> simp [])
  >> qexists_tac `object_result`
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_source_state_eval
      >> simp
           [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_list_encoded,
            listTheory.EVERY_MAP,
            compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded]
      >> metis_tac
           [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths])
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_delta_neg_source_state_eval_refines_word:
  coordinate < 6 /\
  LENGTH center_boxes = 6 /\
  LIST_REL bounded_interval64_covers_object_q
    word_environment center_boxes /\
  bounded_delta64_neg_derivative semantic_radii word_environment coordinate =
    SOME word_result /\
  262500 < clock ==>
  ?weights object_result.
    bounded_taylor_radius_pairs semantic_radii = SOME weights /\
    bounded_object_q_delta_neg_derivative_cv semantic_radii center_boxes
      coordinate = SOME object_result /\
    bounded_taylor64_covers_object_q word_result object_result /\
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv
          (bounded_object_q_cv_list
            (MAP bounded_word64_object_q_cv semantic_radii));
         from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (Num coordinate)]) (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_case16594_object_delta_neg_source_state_cv
            (MAP bounded_word64_object_q_cv semantic_radii)
            center_boxes coordinate)),refs) /\
    bounded_object_q_taylor_runtime_equiv
      (bounded_case16594_object_delta_neg_source_state_cv
        (MAP bounded_word64_object_q_cv semantic_radii)
        center_boxes coordinate)
      object_result
Proof
  strip_tac
  >> drule
       compute_boundedAnalyticObjectDeltaNegDerivativeRefinementTheory.bounded_delta64_neg_derivative_trace
  >> strip_tac
  >> drule
       compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_taylor64_complete_radius_pairs
  >> strip_tac
  >> drule_all
       compute_boundedAnalyticObjectDeltaNegDerivativeRefinementTheory.bounded_delta64_neg_derivative_covers_object_q
  >> strip_tac
  >> `bounded_object_q_delta_neg_derivative_cv semantic_radii center_boxes
        coordinate =
      SOME
        (bounded_object_q_taylor_complete_cv semantic_radii weights T
          (bounded_case16594_object_delta_neg_center_value_environment_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_neg_center_gradient_environment_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_neg_hessian_six_list_cv
            coordinate))` by
       (irule bounded_case16594_object_delta_neg_semantic_environment
        >> simp [])
  >> gvs []
  >> `EVERY bounded_packed_q_interval_valid_cv center_boxes` by
       metis_tac
         [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_interval64_list_covers_packed_q_interval_valid_cv]
  >> `bounded_packed_q_interval_valid_cv
        (bounded_case16594_object_delta_neg_center_value_environment_cv
          center_boxes coordinate) /\
      EVERY bounded_packed_q_interval_valid_cv
        (bounded_case16594_object_delta_neg_center_gradient_environment_cv
          center_boxes coordinate) /\
      EVERY bounded_packed_q_interval_valid_cv
        (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate)` by
       (Cases_on `word_result`
        >> fs
             [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def,
              compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def,
              compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_taylor_complete_cv_def]
        >> metis_tac
             [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_interval64_covers_packed_q_interval_valid_cv,
              compute_boundedPackedObjectSourceContractRefinementTheory.bounded_interval64_list_covers_packed_q_interval_valid_cv])
  >> `EVERY bounded_packed_q_interval_encoded center_boxes` by
       metis_tac
         [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_list_encoded]
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 center_boxes;EL 1 center_boxes;EL 2 center_boxes;
         EL 3 center_boxes;EL 4 center_boxes;EL 5 center_boxes]` by
       fs [listTheory.EVERY_EL]
  >> `LENGTH
        (bounded_case16594_object_delta_neg_center_gradient_environment_cv
          center_boxes coordinate) = 6` by
       (PURE_REWRITE_TAC
          [compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_center_gradient_environment_cv_def]
        >> metis_tac
             [compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_center_components_encoded])
  >> `LENGTH
        (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) =
      21` by
       simp
         [compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_hessian_six_encoded_length]
  >> mp_tac bounded_case16594_object_delta_neg_source_state_eval_semantic
  >> impl_tac >- fs []
  >> strip_tac
  >> gvs [compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
