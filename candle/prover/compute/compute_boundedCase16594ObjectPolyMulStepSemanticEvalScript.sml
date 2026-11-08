(*****************************************************************************
 * Semantic/evaluator bridge for one production polynomial multiplication
 * instruction.  This composes the generic state-multiplication theorem with
 * the authenticated instruction decoder and stack control.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPolyMulStepSemanticEval
Ancestors
  compute_boundedCase16594ObjectMulCompleteEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_poly_step_mul_eval_semantic:
  !left_domain right_domain.
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_object_q_interval_encoded runtime_left_center /\
  EVERY bounded_object_q_interval_encoded runtime_left_center_gradient /\
  LENGTH runtime_left_center_gradient = 6 /\
  bounded_object_q_interval_encoded runtime_left_value /\
  EVERY bounded_object_q_interval_encoded runtime_left_gradient_bounds /\
  LENGTH runtime_left_gradient_bounds = 6 /\
  EVERY bounded_object_q_interval_encoded runtime_left_hessian /\
  LENGTH runtime_left_hessian = 21 /\
  bounded_object_q_interval_encoded runtime_right_center /\
  EVERY bounded_object_q_interval_encoded runtime_right_center_gradient /\
  LENGTH runtime_right_center_gradient = 6 /\
  bounded_object_q_interval_encoded runtime_right_value /\
  EVERY bounded_object_q_interval_encoded runtime_right_gradient_bounds /\
  LENGTH runtime_right_gradient_bounds = 6 /\
  EVERY bounded_object_q_interval_encoded runtime_right_hessian /\
  LENGTH runtime_right_hessian = 21 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_interval_cv_equiv
    runtime_left_center semantic_left_center /\
  bounded_packed_q_interval_valid_cv semantic_left_center /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_left_center_gradient semantic_left_center_gradient /\
  EVERY bounded_packed_q_interval_valid_cv semantic_left_center_gradient /\
  LENGTH semantic_left_center_gradient = 6 /\
  bounded_object_q_interval_cv_equiv
    runtime_left_value semantic_left_value /\
  bounded_packed_q_interval_valid_cv semantic_left_value /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_left_gradient_bounds semantic_left_gradient_bounds /\
  EVERY bounded_packed_q_interval_valid_cv semantic_left_gradient_bounds /\
  LENGTH semantic_left_gradient_bounds = 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_left_hessian semantic_left_hessian /\
  EVERY bounded_packed_q_interval_valid_cv semantic_left_hessian /\
  LENGTH semantic_left_hessian = 21 /\
  bounded_object_q_interval_cv_equiv
    runtime_right_center semantic_right_center /\
  bounded_packed_q_interval_valid_cv semantic_right_center /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_right_center_gradient semantic_right_center_gradient /\
  EVERY bounded_packed_q_interval_valid_cv semantic_right_center_gradient /\
  LENGTH semantic_right_center_gradient = 6 /\
  bounded_object_q_interval_cv_equiv
    runtime_right_value semantic_right_value /\
  bounded_packed_q_interval_valid_cv semantic_right_value /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_right_gradient_bounds semantic_right_gradient_bounds /\
  EVERY bounded_packed_q_interval_valid_cv semantic_right_gradient_bounds /\
  LENGTH semantic_right_gradient_bounds = 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_right_hessian semantic_right_hessian /\
  EVERY bounded_packed_q_interval_valid_cv semantic_right_hessian /\
  LENGTH semantic_right_hessian = 21 /\ 4102 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (compute_exec$Num 4);
         from_cv
           (Pair
             (bounded_case16594_object_state_cv
               (if right_domain then compute_exec$Num 1
                else compute_exec$Num 0)
               runtime_right_center
               (bounded_object_q_cv_list runtime_right_center_gradient)
               runtime_right_value
               (bounded_object_q_cv_list runtime_right_gradient_bounds)
               (bounded_object_q_cv_list runtime_right_hessian))
             (Pair
               (bounded_case16594_object_state_cv
                 (if left_domain then compute_exec$Num 1
                  else compute_exec$Num 0)
                 runtime_left_center
                 (bounded_object_q_cv_list runtime_left_center_gradient)
                 runtime_left_value
                 (bounded_object_q_cv_list runtime_left_gradient_bounds)
                 (bounded_object_q_cv_list runtime_left_hessian))
               rest))]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (compute_exec$Num 1) (Pair result_state rest))),refs) /\
    bounded_object_q_taylor_runtime_equiv result_state
      (bounded_object_q_taylor_mul semantic_radii weights
        (BoundedObjectQTaylor left_domain semantic_left_center
          semantic_left_center_gradient semantic_left_value
          semantic_left_gradient_bounds semantic_left_hessian)
        (BoundedObjectQTaylor right_domain semantic_right_center
          semantic_right_center_gradient semantic_right_value
          semantic_right_gradient_bounds semantic_right_hessian))
Proof
  rpt gen_tac
  >> strip_tac
  >> `?result_state.
        compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_mul»
            [from_cv (bounded_object_q_cv_list runtime_radii);
             from_cv (bounded_case16594_object_state_cv
               (if left_domain then compute_exec$Num 1
                else compute_exec$Num 0)
               runtime_left_center
               (bounded_object_q_cv_list runtime_left_center_gradient)
               runtime_left_value
               (bounded_object_q_cv_list runtime_left_gradient_bounds)
               (bounded_object_q_cv_list runtime_left_hessian));
             from_cv (bounded_case16594_object_state_cv
               (if right_domain then compute_exec$Num 1
                else compute_exec$Num 0)
               runtime_right_center
               (bounded_object_q_cv_list runtime_right_center_gradient)
               runtime_right_value
               (bounded_object_q_cv_list runtime_right_gradient_bounds)
               (bounded_object_q_cv_list runtime_right_hessian))]) refs =
          (M_success (from_cv result_state),refs) /\
        bounded_object_q_taylor_runtime_equiv result_state
          (bounded_object_q_taylor_mul semantic_radii weights
            (BoundedObjectQTaylor left_domain semantic_left_center
              semantic_left_center_gradient semantic_left_value
              semantic_left_gradient_bounds semantic_left_hessian)
            (BoundedObjectQTaylor right_domain semantic_right_center
              semantic_right_center_gradient semantic_right_value
              semantic_right_gradient_bounds semantic_right_hessian))` by
       (irule bounded_case16594_object_state_mul_eval_semantic
        >> simp []
        >> intLib.ARITH_TAC)
  >> pop_assum strip_assume_tac
  >> qexists_tac `result_state`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_poly_step_mul_eval_from_state
      >> simp []
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
