(*****************************************************************************
 * Generic production evaluation of object-state negation.
 *
 * Keep the state fields symbolic.  The proof composes the authenticated
 * selectors, encoded interval/list negation, and the complete production
 * recompleter; it does not expand a genuine certificate or numerical trace.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectNegEval
Ancestors
  compute_boundedCase16594ObjectNegRelation
  compute_boundedCase16594ObjectStateNegEval
Libs
  bossLib preamble intLib

Theorem bounded_object_q_interval_neg_cv_encoded:
  bounded_object_q_interval_encoded value ==>
  bounded_object_q_interval_encoded
    (bounded_object_q_interval_neg_cv value)
Proof
  rw
    [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
  >> qexists_tac `bounded_object_q_interval_neg_ints decoded`
  >> metis_tac
       [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_neg_cv_decodes]
QED

Theorem bounded_object_q_interval_map_neg_encoded:
  !values.
    EVERY bounded_object_q_interval_encoded values ==>
    EVERY bounded_object_q_interval_encoded
      (MAP bounded_object_q_interval_neg_cv values)
Proof
  Induct
  >> simp [bounded_object_q_interval_neg_cv_encoded]
QED

Theorem bounded_object_q_interval_encoded_packed:
  bounded_object_q_interval_encoded value ==>
  bounded_packed_q_interval_encoded value
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape
  >> simp
       [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
QED

Theorem bounded_object_q_interval_map_neg_packed_encoded:
  !values.
    EVERY bounded_object_q_interval_encoded values ==>
    EVERY bounded_packed_q_interval_encoded
      (MAP bounded_object_q_interval_neg_cv values)
Proof
  Induct
  >> simp
       [bounded_object_q_interval_neg_cv_encoded,
        bounded_object_q_interval_encoded_packed]
QED

Theorem bounded_case16594_object_state_center_neg_eval:
  bounded_object_q_interval_encoded center_value /\
  2 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_neg»
        [App «candle_cv_q_packed_object_state_center_value»
          [from_cv
            (bounded_case16594_object_state_cv domain_cv center_value
              center_gradient value_bound gradient_bounds packed_hessian)]])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_neg_cv center_value)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_neg» [from_cv center_value]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_value_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_interval_neg_encoded_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_center_gradient_neg_eval:
  EVERY bounded_object_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  10 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg»
        [App «candle_cv_q_packed_object_state_center_gradient»
          [from_cv
            (bounded_case16594_object_state_cv domain_cv center_value
              (bounded_object_q_cv_list center_gradient)
              value_bound gradient_bounds packed_hessian)]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (MAP bounded_object_q_interval_neg_cv center_gradient))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_dim_interval_list_neg»
            [from_cv (bounded_object_q_cv_list center_gradient)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_gradient_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_interval_list_neg_encoded_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_hessian_neg_eval:
  EVERY bounded_object_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  25 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg»
        [App «candle_cv_q_packed_object_state_packed_hessian»
          [from_cv
            (bounded_case16594_object_state_cv domain_cv center_value
              center_gradient value_bound gradient_bounds
              (bounded_object_q_cv_list packed_hessian))]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (MAP bounded_object_q_interval_neg_cv packed_hessian))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_dim_interval_list_neg»
            [from_cv (bounded_object_q_cv_list packed_hessian)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_packed_hessian_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_interval_list_neg_encoded_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_recomplete_after_neg_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_object_q_interval_encoded center_value /\
  EVERY bounded_object_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_object_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  4101 < clock ==>
  compute_eval (clock - 4) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_recomplete»
        [from_cv (bounded_object_q_cv_list radii);
         App «candle_cv_q_packed_object_state_domain»
           [from_cv
             (bounded_case16594_object_state_cv domain_cv center_value
               (bounded_object_q_cv_list center_gradient)
               value_bound gradient_bounds
               (bounded_object_q_cv_list packed_hessian))];
         from_cv (bounded_object_q_interval_neg_cv center_value);
         from_cv
           (bounded_object_q_cv_list
             (MAP bounded_object_q_interval_neg_cv center_gradient));
         from_cv
           (bounded_object_q_cv_list
             (MAP bounded_object_q_interval_neg_cv packed_hessian))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_state_cv domain_cv
          (bounded_object_q_interval_neg_cv center_value)
          (bounded_object_q_cv_list
            (MAP bounded_object_q_interval_neg_cv center_gradient))
          (bounded_packed_q_source_value_bound6_cv radii
            (bounded_object_q_interval_neg_cv center_value)
            (MAP bounded_object_q_interval_neg_cv center_gradient)
            (MAP bounded_object_q_interval_neg_cv packed_hessian))
          (bounded_object_q_cv_list
            (bounded_packed_q_source_gradient_complete6_cv radii
              (MAP bounded_object_q_interval_neg_cv center_gradient)
              (MAP bounded_object_q_interval_neg_cv packed_hessian)))
          (bounded_object_q_cv_list
            (MAP bounded_object_q_interval_neg_cv packed_hessian)))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 4)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_recomplete»
            [from_cv (bounded_object_q_cv_list radii);from_cv domain_cv;
             from_cv (bounded_object_q_interval_neg_cv center_value);
             from_cv
               (bounded_object_q_cv_list
                 (MAP bounded_object_q_interval_neg_cv center_gradient));
             from_cv
               (bounded_object_q_cv_list
                 (MAP bounded_object_q_interval_neg_cv packed_hessian))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateNegEvalTheory.bounded_case16594_object_compute_eval_app5_argument_results_for_neg
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac >- MATCH_ACCEPT_TAC compute_execProofTheory.compute_eval_from_cv
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_domain_eval
          >> intLib.ARITH_TAC)
      >> conj_tac >- MATCH_ACCEPT_TAC compute_execProofTheory.compute_eval_from_cv
      >> conj_tac >- MATCH_ACCEPT_TAC compute_execProofTheory.compute_eval_from_cv
      >> MATCH_ACCEPT_TAC compute_execProofTheory.compute_eval_from_cv)
  >> irule
       compute_boundedCase16594ObjectStateRecompleteEvalTheory.bounded_case16594_object_state_recomplete_eval
  >> simp
        [bounded_object_q_interval_neg_cv_encoded,
        bounded_object_q_interval_map_neg_encoded,
        bounded_object_q_interval_encoded_packed,
        bounded_object_q_interval_map_neg_packed_encoded]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_neg_complete_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_object_q_interval_encoded center_value /\
  EVERY bounded_object_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_object_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  4101 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_neg»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv
           (bounded_case16594_object_state_cv domain_cv center_value
             (bounded_object_q_cv_list center_gradient)
             value_bound gradient_bounds
             (bounded_object_q_cv_list packed_hessian))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_state_cv domain_cv
          (bounded_object_q_interval_neg_cv center_value)
          (bounded_object_q_cv_list
            (MAP bounded_object_q_interval_neg_cv center_gradient))
          (bounded_packed_q_source_value_bound6_cv radii
            (bounded_object_q_interval_neg_cv center_value)
            (MAP bounded_object_q_interval_neg_cv center_gradient)
            (MAP bounded_object_q_interval_neg_cv packed_hessian))
          (bounded_object_q_cv_list
            (bounded_packed_q_source_gradient_complete6_cv radii
              (MAP bounded_object_q_interval_neg_cv center_gradient)
              (MAP bounded_object_q_interval_neg_cv packed_hessian)))
          (bounded_object_q_cv_list
            (MAP bounded_object_q_interval_neg_cv packed_hessian)))),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_state_neg_eval_from_components
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_cv_list
          (MAP bounded_object_q_interval_neg_cv center_gradient)`
  >> qexists_tac `bounded_object_q_interval_neg_cv center_value`
  >> qexists_tac
       `bounded_object_q_cv_list
          (MAP bounded_object_q_interval_neg_cv packed_hessian)`
  >> conj_tac
  >- (irule bounded_case16594_object_state_center_neg_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule bounded_case16594_object_state_hessian_neg_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule bounded_case16594_object_state_center_gradient_neg_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_state_recomplete_after_neg_eval
  >> simp []
QED

Theorem bounded_case16594_object_state_neg_eval_semantic:
  !domain_flag.
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_object_q_interval_encoded runtime_center /\
  EVERY bounded_object_q_interval_encoded runtime_center_gradient /\
  LENGTH runtime_center_gradient = 6 /\
  EVERY bounded_object_q_interval_encoded runtime_hessian /\
  LENGTH runtime_hessian = 21 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_interval_cv_equiv runtime_center semantic_center /\
  bounded_packed_q_interval_valid_cv semantic_center /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_center_gradient semantic_center_gradient /\
  EVERY bounded_packed_q_interval_valid_cv semantic_center_gradient /\
  LENGTH semantic_center_gradient = 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_hessian semantic_hessian /\
  EVERY bounded_packed_q_interval_valid_cv semantic_hessian /\
  LENGTH semantic_hessian = 21 /\
  4101 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_state_neg»
          [from_cv (bounded_object_q_cv_list runtime_radii);
           from_cv
             (bounded_case16594_object_state_cv
               (if domain_flag then Num 1 else Num 0)
               runtime_center
               (bounded_object_q_cv_list runtime_center_gradient)
               runtime_value runtime_gradient_bounds
               (bounded_object_q_cv_list runtime_hessian))])
        (refs:hol_refs) =
      (M_success (from_cv result_state),refs) /\
    bounded_object_q_taylor_runtime_equiv result_state
      (bounded_object_q_taylor_neg semantic_radii weights
        (BoundedObjectQTaylor domain_flag semantic_center
          semantic_center_gradient semantic_value semantic_gradient_bounds
          semantic_hessian))
Proof
  gen_tac
  >> strip_tac
  >> qexists_tac
       `bounded_case16594_object_state_cv
          (if domain_flag then Num 1 else Num 0)
          (bounded_object_q_interval_neg_cv runtime_center)
          (bounded_object_q_cv_list
            (MAP bounded_object_q_interval_neg_cv runtime_center_gradient))
          (bounded_packed_q_source_value_bound6_cv runtime_radii
            (bounded_object_q_interval_neg_cv runtime_center)
            (MAP bounded_object_q_interval_neg_cv runtime_center_gradient)
            (MAP bounded_object_q_interval_neg_cv runtime_hessian))
          (bounded_object_q_cv_list
            (bounded_packed_q_source_gradient_complete6_cv runtime_radii
              (MAP bounded_object_q_interval_neg_cv
                runtime_center_gradient)
              (MAP bounded_object_q_interval_neg_cv runtime_hessian)))
          (bounded_object_q_cv_list
            (MAP bounded_object_q_interval_neg_cv runtime_hessian))`
  >> conj_tac
  >- (irule bounded_case16594_object_state_neg_complete_eval
      >> simp [])
  >> irule
       compute_boundedCase16594ObjectNegRelationTheory.bounded_case16594_object_neg_recomplete_runtime_semantic_equiv
  >> simp []
QED

val _ = export_theory ();
