(*****************************************************************************
 * Semantic/evaluator bridges for the production polynomial constant and
 * negation instructions.  Together with the multiplication-step bridge,
 * these cover the first authenticated case-16594 polynomial program.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPolyBaseStepSemanticEval
Ancestors
  compute_boundedCase16594ObjectPolyMulStepSemanticEval
  compute_boundedCase16594ObjectNegEval
  compute_boundedCase16594ObjectRuntimePreservation
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_poly_step_constant_eval_semantic:
  2 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_poly_step»
      [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
       from_cv
         (Pair (compute_exec$Num 0)
           (bounded_analytic_source_q_cv positive negative
             denominator_predecessor));
       from_cv stack]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (compute_exec$Num 1)
          (Pair
            (bounded_case16594_object_constant_state_cv
              (bounded_analytic_source_q_cv positive negative
                denominator_predecessor))
            stack))),refs) /\
  bounded_object_q_taylor_runtime_equiv
    (bounded_case16594_object_constant_state_cv
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor))
    (bounded_object_q_taylor_constant positive negative
      denominator_predecessor)
Proof
  strip_tac
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_poly_step_constant_eval
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_constant_runtime_semantic_equiv
QED

Theorem bounded_case16594_object_poly_step_neg_eval_semantic:
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
  LENGTH semantic_hessian = 21 /\ 4102 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (compute_exec$Num 2);
         from_cv
           (Pair
             (bounded_case16594_object_state_cv
               (if domain_flag then compute_exec$Num 1
                else compute_exec$Num 0)
               runtime_center
               (bounded_object_q_cv_list runtime_center_gradient)
               runtime_value runtime_gradient_bounds
               (bounded_object_q_cv_list runtime_hessian))
             rest)]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (compute_exec$Num 1) (Pair result_state rest))),refs) /\
    bounded_object_q_taylor_runtime_equiv result_state
      (bounded_object_q_taylor_neg semantic_radii weights
        (BoundedObjectQTaylor domain_flag semantic_center
          semantic_center_gradient semantic_value semantic_gradient_bounds
          semantic_hessian))
Proof
  gen_tac
  >> strip_tac
  >> `?result_state.
        compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_neg»
            [from_cv (bounded_object_q_cv_list runtime_radii);
             from_cv
               (bounded_case16594_object_state_cv
                 (if domain_flag then compute_exec$Num 1
                  else compute_exec$Num 0)
                 runtime_center
                 (bounded_object_q_cv_list runtime_center_gradient)
                 runtime_value runtime_gradient_bounds
                 (bounded_object_q_cv_list runtime_hessian))]) refs =
          (M_success (from_cv result_state),refs) /\
        bounded_object_q_taylor_runtime_equiv result_state
          (bounded_object_q_taylor_neg semantic_radii weights
            (BoundedObjectQTaylor domain_flag semantic_center
              semantic_center_gradient semantic_value
              semantic_gradient_bounds semantic_hessian))` by
       (irule
          compute_boundedCase16594ObjectNegEvalTheory.bounded_case16594_object_state_neg_eval_semantic
        >> simp []
        >> intLib.ARITH_TAC)
  >> pop_assum strip_assume_tac
  >> qexists_tac `result_state`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_poly_step_neg_eval_from_state
      >> simp []
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
