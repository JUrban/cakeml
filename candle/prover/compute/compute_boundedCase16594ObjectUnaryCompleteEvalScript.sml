(*****************************************************************************
 * Complete production evaluator semantics for the shared object unary step.
 *
 * The theorem composes the authenticated state accessors, list scaling,
 * unary Hessian construction, and source recompletion.  Sqrt, inverse, and
 * atan can therefore supply only their scalar interval certificates.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectUnaryCompleteEval
Ancestors
  compute_boundedCase16594ObjectUnaryCoreEval
  compute_boundedCase16594ObjectUnaryControlEval
  compute_boundedCase16594ObjectStateRecompleteEval
  compute_boundedCase16594ObjectAddCompleteEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_state_unary_cv_def:
  bounded_case16594_object_state_unary_cv radii domain_cv result_interval
      center_first box_first box_second center_gradient gradient_bounds
      packed_hessian =
    let next_center_gradient =
          bounded_object_q_interval_list_scale_cv
            center_first center_gradient;
        next_packed_hessian =
          bounded_object_q_taylor_unary_hessian_cv
            box_first box_second gradient_bounds packed_hessian
    in
      bounded_case16594_object_state_cv
        domain_cv result_interval
        (bounded_object_q_cv_list next_center_gradient)
        (bounded_packed_q_source_value_bound6_cv
          radii result_interval next_center_gradient next_packed_hessian)
        (bounded_object_q_cv_list
          (bounded_packed_q_source_gradient_complete6_cv
            radii next_center_gradient next_packed_hessian))
        (bounded_object_q_cv_list next_packed_hessian)
End

Theorem bounded_case16594_object_state_unary_cv_unfold:
  bounded_case16594_object_state_unary_cv radii domain_cv result_interval
      center_first box_first box_second center_gradient gradient_bounds
      packed_hessian =
    bounded_case16594_object_state_cv
      domain_cv result_interval
      (bounded_object_q_cv_list
        (bounded_object_q_interval_list_scale_cv
          center_first center_gradient))
      (bounded_packed_q_source_value_bound6_cv
        radii result_interval
        (bounded_object_q_interval_list_scale_cv
          center_first center_gradient)
        (bounded_object_q_taylor_unary_hessian_cv
          box_first box_second gradient_bounds packed_hessian))
      (bounded_object_q_cv_list
        (bounded_packed_q_source_gradient_complete6_cv
          radii
          (bounded_object_q_interval_list_scale_cv
            center_first center_gradient)
          (bounded_object_q_taylor_unary_hessian_cv
            box_first box_second gradient_bounds packed_hessian)))
      (bounded_object_q_cv_list
        (bounded_object_q_taylor_unary_hessian_cv
          box_first box_second gradient_bounds packed_hessian))
Proof
  simp [bounded_case16594_object_state_unary_cv_def]
QED

Theorem bounded_case16594_object_unary_components_shape:
  bounded_packed_q_interval_encoded center_first /\
  bounded_packed_q_interval_encoded box_first /\
  bounded_packed_q_interval_encoded box_second /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded gradient_bounds /\
  LENGTH gradient_bounds = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 ==>
  EVERY bounded_packed_q_interval_encoded
    (bounded_object_q_interval_list_scale_cv
      center_first center_gradient) /\
  LENGTH
    (bounded_object_q_interval_list_scale_cv
      center_first center_gradient) = 6 /\
  EVERY bounded_packed_q_interval_encoded
    (bounded_object_q_taylor_unary_hessian_cv
      box_first box_second gradient_bounds packed_hessian) /\
  LENGTH
    (bounded_object_q_taylor_unary_hessian_cv
      box_first box_second gradient_bounds packed_hessian) = 21
Proof
  strip_tac
  >> simp
       [compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_interval_list_scale_packed_encoded,
        compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_interval_list_scale_length]
  >> rewrite_tac
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_taylor_unary_hessian_cv_def]
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectAddCompleteEvalTheory.bounded_case16594_object_interval_list_add_packed_encoded
      >> simp
           [compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_interval_list_scale_packed_encoded,
            compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_interval_self_outer_packed_encoded,
            compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_interval_list_scale_length,
            compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_self_outer_length6])
  >> simp
       [compute_boundedCase16594ObjectAddRelationTheory.bounded_case16594_object_interval_list_add_cv_length,
        compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_interval_list_scale_length,
        compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_self_outer_length6]
QED

Theorem bounded_case16594_object_state_unary_center_gradient_eval:
  bounded_packed_q_interval_encoded center_first /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  512 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_scale»
        [from_cv center_first;
         App «candle_cv_q_packed_object_state_center_gradient»
           [from_cv
             (bounded_case16594_object_state_cv domain_cv center_value
               (bounded_object_q_cv_list center_gradient) value_bound
               (bounded_object_q_cv_list gradient_bounds)
               (bounded_object_q_cv_list packed_hessian))]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_object_q_interval_list_scale_cv
            center_first center_gradient))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_interval_list_scale»
            [from_cv center_first;
             from_cv (bounded_object_q_cv_list center_gradient)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_gradient_eval]
      >> intLib.ARITH_TAC)
  >> rewrite_tac
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
  >> irule
       compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_interval_list_scale_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_unary_hessian_eval:
  bounded_packed_q_interval_encoded box_first /\
  bounded_packed_q_interval_encoded box_second /\
  EVERY bounded_packed_q_interval_encoded gradient_bounds /\
  LENGTH gradient_bounds = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  1024 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_unary_hessian6»
        [from_cv box_first;from_cv box_second;
         App «candle_cv_q_packed_object_state_gradient_bounds»
           [from_cv
             (bounded_case16594_object_state_cv domain_cv center_value
               center_gradient value_bound
               (bounded_object_q_cv_list gradient_bounds)
               (bounded_object_q_cv_list packed_hessian))];
         App «candle_cv_q_packed_object_state_packed_hessian»
           [from_cv
             (bounded_case16594_object_state_cv domain_cv center_value
               center_gradient value_bound
               (bounded_object_q_cv_list gradient_bounds)
               (bounded_object_q_cv_list packed_hessian))]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_object_q_taylor_unary_hessian_cv
            box_first box_second gradient_bounds packed_hessian))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_unary_hessian6»
            [from_cv box_first;from_cv box_second;
             from_cv (bounded_object_q_cv_list gradient_bounds);
             from_cv (bounded_object_q_cv_list packed_hessian)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectQuadraticTermAtEvalTheory.bounded_packed_compute_eval_app4_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_gradient_bounds_eval,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_packed_hessian_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_unary_hessian6_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_unary_recomplete_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded result_interval /\
  EVERY bounded_packed_q_interval_encoded next_center_gradient /\
  LENGTH next_center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded next_packed_hessian /\
  LENGTH next_packed_hessian = 21 /\
  4098 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_recomplete»
        [from_cv (bounded_object_q_cv_list radii);
         App «candle_cv_q_packed_object_state_domain»
           [from_cv
             (bounded_case16594_object_state_cv domain_cv center_value
               center_gradient value_bound gradient_bounds packed_hessian)];
         from_cv result_interval;
         from_cv (bounded_object_q_cv_list next_center_gradient);
         from_cv (bounded_object_q_cv_list next_packed_hessian)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_state_cv domain_cv result_interval
          (bounded_object_q_cv_list next_center_gradient)
          (bounded_packed_q_source_value_bound6_cv
            radii result_interval next_center_gradient next_packed_hessian)
          (bounded_object_q_cv_list
            (bounded_packed_q_source_gradient_complete6_cv
              radii next_center_gradient next_packed_hessian))
          (bounded_object_q_cv_list next_packed_hessian))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_recomplete»
            [from_cv (bounded_object_q_cv_list radii);from_cv domain_cv;
             from_cv result_interval;
             from_cv (bounded_object_q_cv_list next_center_gradient);
             from_cv (bounded_object_q_cv_list next_packed_hessian)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyTraceEvalTheory.bounded_case16594_object_compute_eval_app5_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_domain_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectStateRecompleteEvalTheory.bounded_case16594_object_state_recomplete_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_unary_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded result_interval /\
  bounded_packed_q_interval_encoded center_first /\
  bounded_packed_q_interval_encoded box_first /\
  bounded_packed_q_interval_encoded box_second /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded gradient_bounds /\
  LENGTH gradient_bounds = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  8192 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_unary»
        [from_cv (bounded_object_q_cv_list radii);from_cv result_interval;
         from_cv center_first;from_cv box_first;from_cv box_second;
         from_cv
           (bounded_case16594_object_state_cv domain_cv center_value
             (bounded_object_q_cv_list center_gradient) value_bound
             (bounded_object_q_cv_list gradient_bounds)
             (bounded_object_q_cv_list packed_hessian))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_state_unary_cv
          radii domain_cv result_interval center_first box_first box_second
          center_gradient gradient_bounds packed_hessian)),refs)
Proof
  strip_tac
  >> rewrite_tac [bounded_case16594_object_state_unary_cv_unfold]
  >> irule
       compute_boundedCase16594ObjectUnaryControlEvalTheory.bounded_case16594_object_state_unary_eval_from_components
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_cv_list
          (bounded_object_q_interval_list_scale_cv
            center_first center_gradient)`
  >> qexists_tac
       `bounded_object_q_cv_list
          (bounded_object_q_taylor_unary_hessian_cv
            box_first box_second gradient_bounds packed_hessian)`
  >> conj_tac
  >- (irule bounded_case16594_object_state_unary_center_gradient_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule bounded_case16594_object_state_unary_recomplete_eval
      >> simp []
      >> metis_tac [bounded_case16594_object_unary_components_shape])
  >> irule bounded_case16594_object_state_unary_hessian_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
