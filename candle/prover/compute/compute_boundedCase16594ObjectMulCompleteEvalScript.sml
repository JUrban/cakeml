(*****************************************************************************
 * Complete production evaluator and semantic bridge for object-state
 * multiplication.  Numerical fields remain symbolic: the proof composes
 * center, gradient, packed-Hessian, domain, and recompletion contracts.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectMulCompleteEval
Ancestors
  compute_boundedCase16594ObjectMulHessianCompleteEval
  compute_boundedCase16594ObjectStateRecompleteEval
  compute_boundedCase16594ObjectStateNegEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_interval_products_sum_acc_packed_encoded:
  !inputs accumulator.
    EVERY (\input. bounded_packed_q_interval_encoded (FST input) /\
                    bounded_packed_q_interval_encoded (SND input)) inputs /\
    bounded_packed_q_interval_encoded accumulator ==>
    bounded_packed_q_interval_encoded
      (bounded_object_q_interval_products_sum_acc_cv inputs accumulator)
Proof
  Induct
  >- simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_products_sum_acc_cv_def]
  >> Cases_on `h`
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_products_sum_acc_cv_def]
  >> metis_tac
       [compute_boundedCase16594ObjectMulHessianEvalTheory.bounded_case16594_packed_interval_add_encoded,
        compute_boundedCase16594ObjectMulHessianEvalTheory.bounded_case16594_packed_interval_mul_encoded]
QED

Theorem bounded_case16594_object_fused_scale_add_packed_encoded:
  !left right.
    bounded_packed_q_interval_encoded left_scale /\
    EVERY bounded_packed_q_interval_encoded left /\
    bounded_packed_q_interval_encoded right_scale /\
    EVERY bounded_packed_q_interval_encoded right ==>
    EVERY bounded_packed_q_interval_encoded
      (bounded_object_q_interval_fused_scale_add_cv
        left_scale left right_scale right)
Proof
  Induct
  >> Cases_on `right`
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_scale_add_cv_def]
  >> rpt strip_tac
  >> irule bounded_case16594_object_interval_products_sum_acc_packed_encoded
  >> simp []
QED

Definition bounded_case16594_object_symmetric_pair_packed_encoded_def:
  bounded_case16594_object_symmetric_pair_packed_encoded outer <=>
    bounded_packed_q_interval_encoded (FST (FST outer)) /\
    bounded_packed_q_interval_encoded (SND (FST outer)) /\
    bounded_packed_q_interval_encoded (FST (SND outer)) /\
    bounded_packed_q_interval_encoded (SND (SND outer))
End

Theorem bounded_case16594_object_symmetric_product_pairs_row_packed_encoded:
  !left right.
    bounded_packed_q_interval_encoded fixed_left /\
    bounded_packed_q_interval_encoded fixed_right /\
    EVERY bounded_packed_q_interval_encoded left /\
    EVERY bounded_packed_q_interval_encoded right ==>
    EVERY bounded_case16594_object_symmetric_pair_packed_encoded
      (bounded_object_q_symmetric_product_pairs_row_cv
        fixed_left fixed_right left right)
Proof
  Induct
  >> Cases_on `right`
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_row_cv_def,
        bounded_case16594_object_symmetric_pair_packed_encoded_def]
QED

Theorem bounded_case16594_object_symmetric_product_pairs_packed_encoded:
  !left right.
    EVERY bounded_packed_q_interval_encoded left /\
    EVERY bounded_packed_q_interval_encoded right ==>
    EVERY bounded_case16594_object_symmetric_pair_packed_encoded
      (bounded_object_q_symmetric_product_pairs_cv left right)
Proof
  Induct
  >> Cases_on `right`
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_cv_def]
  >> rpt strip_tac
  >> irule bounded_case16594_object_symmetric_product_pairs_row_packed_encoded
  >> simp []
QED

Theorem bounded_case16594_object_fused_hessian_packed_encoded:
  !left_hessian right_hessian outer.
    bounded_packed_q_interval_encoded left_value /\
    bounded_packed_q_interval_encoded right_value /\
    EVERY bounded_packed_q_interval_encoded left_hessian /\
    EVERY bounded_packed_q_interval_encoded right_hessian /\
    EVERY bounded_case16594_object_symmetric_pair_packed_encoded outer ==>
    EVERY bounded_packed_q_interval_encoded
      (bounded_object_q_interval_fused_hessian_cv
        left_value right_value left_hessian right_hessian outer)
Proof
  Induct
  >> Cases_on `right_hessian`
  >> Cases_on `outer`
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_hessian_cv_def,
        bounded_case16594_object_symmetric_pair_packed_encoded_def]
  >> rpt strip_tac
  >> irule bounded_case16594_object_interval_products_sum_acc_packed_encoded
  >> simp []
QED

Theorem bounded_case16594_object_interval_list_packed_encoded:
  !values.
    EVERY bounded_object_q_interval_encoded values ==>
    EVERY bounded_packed_q_interval_encoded values
Proof
  Induct
  >> simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded]
QED

Theorem bounded_case16594_object_state_center_mul_eval:
  bounded_object_q_interval_encoded left_center /\
  bounded_object_q_interval_encoded right_center /\
  10 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_interval_mul»
      [App «candle_cv_q_packed_object_state_center_value»
        [from_cv (bounded_case16594_object_state_cv left_domain left_center
          left_center_gradient left_value left_gradient_bounds left_hessian)];
       App «candle_cv_q_packed_object_state_center_value»
        [from_cv (bounded_case16594_object_state_cv right_domain right_center
          right_center_gradient right_value right_gradient_bounds right_hessian)]])
    (refs:hol_refs) =
  (M_success
    (from_cv (bounded_object_q_interval_mul_cv left_center right_center)),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_mul_argument_results
  >> simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded,
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_value_eval]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_bool_and_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs «candle_cv_bool_and» =
    SOME ([«a»;«b»],If (Var «a») (Var «b») (compute_syntax$Num 0))
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_bool_and_flags_eval:
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_bool_and»
      [from_cv (if left_domain then compute_exec$Num 1 else compute_exec$Num 0);
       from_cv (if right_domain then compute_exec$Num 1 else compute_exec$Num 0)])
    (refs:hol_refs) =
  (M_success
    (from_cv (if left_domain /\ right_domain then compute_exec$Num 1
              else compute_exec$Num 0)),refs)
Proof
  Cases_on `left_domain`
  >> Cases_on `right_domain`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_case16594_object_bool_and_lookup,
        compute_evalTheory.option_def,compute_evalTheory.check_def,
        compute_evalTheory.compute_eval_def,compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_state_domain_mul_eval:
  2 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_bool_and»
      [App «candle_cv_q_packed_object_state_domain»
        [from_cv (bounded_case16594_object_state_cv
          (if left_domain then compute_exec$Num 1 else compute_exec$Num 0)
          left_center left_center_gradient left_value left_gradient_bounds
          left_hessian)];
       App «candle_cv_q_packed_object_state_domain»
        [from_cv (bounded_case16594_object_state_cv
          (if right_domain then compute_exec$Num 1 else compute_exec$Num 0)
          right_center right_center_gradient right_value right_gradient_bounds
          right_hessian)]]) (refs:hol_refs) =
  (M_success
    (from_cv
      (if left_domain /\ right_domain then compute_exec$Num 1
       else compute_exec$Num 0)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_bool_and»
            [from_cv
               (if left_domain then compute_exec$Num 1 else compute_exec$Num 0);
             from_cv
               (if right_domain then compute_exec$Num 1 else compute_exec$Num 0)])
          refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_domain_eval]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_bool_and_flags_eval
  >> intLib.ARITH_TAC
QED

Definition bounded_case16594_object_state_mul_cv_def:
  bounded_case16594_object_state_mul_cv radii left_domain left_center
      left_center_gradient left_value left_gradient_bounds left_hessian
      right_domain right_center right_center_gradient right_value
      right_gradient_bounds right_hessian =
    let center = bounded_object_q_interval_mul_cv left_center right_center;
        center_gradient = bounded_object_q_interval_fused_scale_add_cv
          right_center left_center_gradient left_center right_center_gradient;
        outer = bounded_object_q_symmetric_product_pairs_cv
          left_gradient_bounds right_gradient_bounds;
        hessian = bounded_object_q_interval_fused_hessian_cv
          left_value right_value left_hessian right_hessian outer
    in
      bounded_case16594_object_state_cv
        (if left_domain /\ right_domain then compute_exec$Num 1
         else compute_exec$Num 0)
        center (bounded_object_q_cv_list center_gradient)
        (bounded_packed_q_source_value_bound6_cv radii center
          center_gradient hessian)
        (bounded_object_q_cv_list
          (bounded_packed_q_source_gradient_complete6_cv radii
            center_gradient hessian))
        (bounded_object_q_cv_list hessian)
End

Theorem bounded_case16594_object_state_mul_cv_unfold:
  bounded_case16594_object_state_mul_cv radii left_domain left_center
    left_center_gradient left_value left_gradient_bounds left_hessian
    right_domain right_center right_center_gradient right_value
    right_gradient_bounds right_hessian =
  bounded_case16594_object_state_cv
    (if left_domain /\ right_domain then compute_exec$Num 1
     else compute_exec$Num 0)
    (bounded_object_q_interval_mul_cv left_center right_center)
    (bounded_object_q_cv_list
      (bounded_object_q_interval_fused_scale_add_cv right_center
        left_center_gradient left_center right_center_gradient))
    (bounded_packed_q_source_value_bound6_cv radii
      (bounded_object_q_interval_mul_cv left_center right_center)
      (bounded_object_q_interval_fused_scale_add_cv right_center
        left_center_gradient left_center right_center_gradient)
      (bounded_object_q_interval_fused_hessian_cv left_value right_value
        left_hessian right_hessian
        (bounded_object_q_symmetric_product_pairs_cv
          left_gradient_bounds right_gradient_bounds)))
    (bounded_object_q_cv_list
      (bounded_packed_q_source_gradient_complete6_cv radii
        (bounded_object_q_interval_fused_scale_add_cv right_center
          left_center_gradient left_center right_center_gradient)
        (bounded_object_q_interval_fused_hessian_cv left_value right_value
          left_hessian right_hessian
          (bounded_object_q_symmetric_product_pairs_cv
            left_gradient_bounds right_gradient_bounds))))
    (bounded_object_q_cv_list
      (bounded_object_q_interval_fused_hessian_cv left_value right_value
        left_hessian right_hessian
        (bounded_object_q_symmetric_product_pairs_cv
          left_gradient_bounds right_gradient_bounds)))
Proof
  simp [bounded_case16594_object_state_mul_cv_def]
QED

Theorem bounded_case16594_object_state_mul_components_shape:
  bounded_object_q_interval_encoded left_center /\
  bounded_object_q_interval_encoded right_center /\
  EVERY bounded_object_q_interval_encoded left_center_gradient /\
  EVERY bounded_object_q_interval_encoded right_center_gradient /\
  LENGTH left_center_gradient = 6 /\ LENGTH right_center_gradient = 6 /\
  bounded_object_q_interval_encoded left_value /\
  bounded_object_q_interval_encoded right_value /\
  EVERY bounded_object_q_interval_encoded left_gradient_bounds /\
  EVERY bounded_object_q_interval_encoded right_gradient_bounds /\
  LENGTH left_gradient_bounds = 6 /\ LENGTH right_gradient_bounds = 6 /\
  EVERY bounded_object_q_interval_encoded left_hessian /\
  EVERY bounded_object_q_interval_encoded right_hessian /\
  LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 ==>
  bounded_packed_q_interval_encoded
    (bounded_object_q_interval_mul_cv left_center right_center) /\
  EVERY bounded_packed_q_interval_encoded
    (bounded_object_q_interval_fused_scale_add_cv right_center
      left_center_gradient left_center right_center_gradient) /\
  LENGTH (bounded_object_q_interval_fused_scale_add_cv right_center
      left_center_gradient left_center right_center_gradient) = 6 /\
  EVERY bounded_packed_q_interval_encoded
    (bounded_object_q_interval_fused_hessian_cv left_value right_value
      left_hessian right_hessian
      (bounded_object_q_symmetric_product_pairs_cv
        left_gradient_bounds right_gradient_bounds)) /\
  LENGTH (bounded_object_q_interval_fused_hessian_cv left_value right_value
      left_hessian right_hessian
      (bounded_object_q_symmetric_product_pairs_cv
        left_gradient_bounds right_gradient_bounds)) = 21
Proof
  strip_tac
  >> rpt conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulHessianEvalTheory.bounded_case16594_packed_interval_mul_encoded
      >> simp
           [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded])
  >- (irule bounded_case16594_object_fused_scale_add_packed_encoded
      >> simp
           [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded,
            bounded_case16594_object_interval_list_packed_encoded])
  >- (irule
        compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_fused_scale_add_cv_length6_relation
      >> simp [])
  >- (irule bounded_case16594_object_fused_hessian_packed_encoded
      >> simp
           [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded,
            bounded_case16594_object_interval_list_packed_encoded]
      >> irule
           bounded_case16594_object_symmetric_product_pairs_packed_encoded
      >> simp [bounded_case16594_object_interval_list_packed_encoded])
  >> irule
       compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_fused_hessian_cv_length21_relation
  >> simp []
  >> irule
       compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_symmetric_product_pairs_cv_length6_relation
  >> simp []
QED

Theorem bounded_case16594_object_state_recomplete_direct_eval:
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded hessian /\ LENGTH hessian = 21 /\
  4097 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_state_recomplete»
      [from_cv (bounded_object_q_cv_list radii);from_cv domain_cv;
       from_cv center;from_cv (bounded_object_q_cv_list center_gradient);
       from_cv (bounded_object_q_cv_list hessian)]) (refs:hol_refs) =
  (M_success
    (from_cv
      (bounded_case16594_object_state_cv domain_cv center
        (bounded_object_q_cv_list center_gradient)
        (bounded_packed_q_source_value_bound6_cv radii center
          center_gradient hessian)
        (bounded_object_q_cv_list
          (bounded_packed_q_source_gradient_complete6_cv radii
            center_gradient hessian))
        (bounded_object_q_cv_list hessian))),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateRecompleteEvalTheory.bounded_case16594_object_state_recomplete_eval
  >> simp []
QED


Theorem bounded_case16594_object_state_gradient_mul_eval:
  bounded_object_q_interval_encoded left_center /\
  bounded_object_q_interval_encoded right_center /\
  EVERY bounded_object_q_interval_encoded left_center_gradient /\
  EVERY bounded_object_q_interval_encoded right_center_gradient /\
  LENGTH left_center_gradient = 6 /\ LENGTH right_center_gradient = 6 /\
  450 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_fused_scale_add»
      [App «candle_cv_q_packed_object_state_center_value»
        [from_cv (bounded_case16594_object_state_cv right_domain right_center
          (bounded_object_q_cv_list right_center_gradient) right_value
          right_gradient_bounds right_hessian)];
       App «candle_cv_q_packed_object_state_center_gradient»
        [from_cv (bounded_case16594_object_state_cv left_domain left_center
          (bounded_object_q_cv_list left_center_gradient) left_value
          left_gradient_bounds left_hessian)];
       App «candle_cv_q_packed_object_state_center_value»
        [from_cv (bounded_case16594_object_state_cv left_domain left_center
          (bounded_object_q_cv_list left_center_gradient) left_value
          left_gradient_bounds left_hessian)];
       App «candle_cv_q_packed_object_state_center_gradient»
        [from_cv (bounded_case16594_object_state_cv right_domain right_center
          (bounded_object_q_cv_list right_center_gradient) right_value
          right_gradient_bounds right_hessian)]]) (refs:hol_refs) =
  (M_success
    (from_cv (bounded_object_q_cv_list
      (bounded_object_q_interval_fused_scale_add_cv
        right_center left_center_gradient left_center right_center_gradient))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_fused_scale_add»
            [from_cv right_center;
             from_cv (bounded_object_q_cv_list left_center_gradient);
             from_cv left_center;
             from_cv (bounded_object_q_cv_list right_center_gradient)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectQuadraticTermAtEvalTheory.bounded_packed_compute_eval_app4_argument_results
      >> simp
           [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_value_eval,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_gradient_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_fused_scale_add_eval
  >> simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded,
        bounded_case16594_object_interval_list_packed_encoded]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_hessian_mul_eval:
  bounded_object_q_interval_encoded left_value /\
  bounded_object_q_interval_encoded right_value /\
  EVERY bounded_object_q_interval_encoded left_gradient_bounds /\
  EVERY bounded_object_q_interval_encoded right_gradient_bounds /\
  EVERY bounded_object_q_interval_encoded left_hessian /\
  EVERY bounded_object_q_interval_encoded right_hessian /\
  LENGTH left_gradient_bounds = 6 /\ LENGTH right_gradient_bounds = 6 /\
  LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
  268 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_mul_hessian6»
      [App «candle_cv_q_packed_object_state_value_bound»
        [from_cv (bounded_case16594_object_state_cv left_domain left_center
          left_center_gradient left_value
          (bounded_object_q_cv_list left_gradient_bounds)
          (bounded_object_q_cv_list left_hessian))];
       App «candle_cv_q_packed_object_state_value_bound»
        [from_cv (bounded_case16594_object_state_cv right_domain right_center
          right_center_gradient right_value
          (bounded_object_q_cv_list right_gradient_bounds)
          (bounded_object_q_cv_list right_hessian))];
       App «candle_cv_q_packed_object_state_gradient_bounds»
        [from_cv (bounded_case16594_object_state_cv left_domain left_center
          left_center_gradient left_value
          (bounded_object_q_cv_list left_gradient_bounds)
          (bounded_object_q_cv_list left_hessian))];
       App «candle_cv_q_packed_object_state_gradient_bounds»
        [from_cv (bounded_case16594_object_state_cv right_domain right_center
          right_center_gradient right_value
          (bounded_object_q_cv_list right_gradient_bounds)
          (bounded_object_q_cv_list right_hessian))];
       App «candle_cv_q_packed_object_state_packed_hessian»
        [from_cv (bounded_case16594_object_state_cv left_domain left_center
          left_center_gradient left_value
          (bounded_object_q_cv_list left_gradient_bounds)
          (bounded_object_q_cv_list left_hessian))];
       App «candle_cv_q_packed_object_state_packed_hessian»
        [from_cv (bounded_case16594_object_state_cv right_domain right_center
          right_center_gradient right_value
          (bounded_object_q_cv_list right_gradient_bounds)
          (bounded_object_q_cv_list right_hessian))]]) (refs:hol_refs) =
  (M_success (from_cv (bounded_object_q_cv_list
    (bounded_object_q_interval_fused_hessian_cv left_value right_value
      left_hessian right_hessian
      (bounded_object_q_symmetric_product_pairs_cv
        left_gradient_bounds right_gradient_bounds)))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_mul_hessian6»
            [from_cv left_value;from_cv right_value;
             from_cv (bounded_object_q_cv_list left_gradient_bounds);
             from_cv (bounded_object_q_cv_list right_gradient_bounds);
             from_cv (bounded_object_q_cv_list left_hessian);
             from_cv (bounded_object_q_cv_list right_hessian)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_app6_argument_results
      >> simp
           [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_value_bound_eval,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_gradient_bounds_eval,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_packed_hessian_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectMulHessianCompleteEvalTheory.bounded_case16594_object_mul_hessian6_semantic_eval
  >> simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded,
        bounded_case16594_object_interval_list_packed_encoded]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_recomplete_mul_components_eval:
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  bounded_object_q_interval_encoded left_center /\
  EVERY bounded_object_q_interval_encoded left_center_gradient /\
  LENGTH left_center_gradient = 6 /\
  bounded_object_q_interval_encoded left_value /\
  EVERY bounded_object_q_interval_encoded left_gradient_bounds /\
  LENGTH left_gradient_bounds = 6 /\
  EVERY bounded_object_q_interval_encoded left_hessian /\
  LENGTH left_hessian = 21 /\
  bounded_object_q_interval_encoded right_center /\
  EVERY bounded_object_q_interval_encoded right_center_gradient /\
  LENGTH right_center_gradient = 6 /\
  bounded_object_q_interval_encoded right_value /\
  EVERY bounded_object_q_interval_encoded right_gradient_bounds /\
  LENGTH right_gradient_bounds = 6 /\
  EVERY bounded_object_q_interval_encoded right_hessian /\
  LENGTH right_hessian = 21 /\ 4101 < clock ==>
  compute_eval (clock - 4) bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_state_recomplete»
      [from_cv (bounded_object_q_cv_list radii);
       from_cv
         (if left_domain /\ right_domain then compute_exec$Num 1
          else compute_exec$Num 0);
       from_cv (bounded_object_q_interval_mul_cv left_center right_center);
       from_cv
         (bounded_object_q_cv_list
           (bounded_object_q_interval_fused_scale_add_cv right_center
             left_center_gradient left_center right_center_gradient));
       from_cv
         (bounded_object_q_cv_list
           (bounded_object_q_interval_fused_hessian_cv left_value right_value
             left_hessian right_hessian
             (bounded_object_q_symmetric_product_pairs_cv
               left_gradient_bounds right_gradient_bounds)))]) (refs:hol_refs) =
  (M_success
    (from_cv
      (bounded_case16594_object_state_mul_cv radii left_domain left_center
        left_center_gradient left_value left_gradient_bounds left_hessian
        right_domain right_center right_center_gradient right_value
        right_gradient_bounds right_hessian)),refs)
Proof
  strip_tac
  >> `bounded_packed_q_interval_encoded
        (bounded_object_q_interval_mul_cv left_center right_center) /\
      EVERY bounded_packed_q_interval_encoded
        (bounded_object_q_interval_fused_scale_add_cv right_center
          left_center_gradient left_center right_center_gradient) /\
      LENGTH
        (bounded_object_q_interval_fused_scale_add_cv right_center
          left_center_gradient left_center right_center_gradient) = 6 /\
      EVERY bounded_packed_q_interval_encoded
        (bounded_object_q_interval_fused_hessian_cv left_value right_value
          left_hessian right_hessian
          (bounded_object_q_symmetric_product_pairs_cv
            left_gradient_bounds right_gradient_bounds)) /\
      LENGTH
        (bounded_object_q_interval_fused_hessian_cv left_value right_value
          left_hessian right_hessian
          (bounded_object_q_symmetric_product_pairs_cv
            left_gradient_bounds right_gradient_bounds)) = 21` by
       (irule bounded_case16594_object_state_mul_components_shape
        >> simp [])
  >> PURE_REWRITE_TAC [bounded_case16594_object_state_mul_cv_unfold]
  >> irule bounded_case16594_object_state_recomplete_direct_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_recomplete_after_mul_eval:
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  bounded_object_q_interval_encoded left_center /\
  EVERY bounded_object_q_interval_encoded left_center_gradient /\
  LENGTH left_center_gradient = 6 /\
  bounded_object_q_interval_encoded left_value /\
  EVERY bounded_object_q_interval_encoded left_gradient_bounds /\
  LENGTH left_gradient_bounds = 6 /\
  EVERY bounded_object_q_interval_encoded left_hessian /\
  LENGTH left_hessian = 21 /\
  bounded_object_q_interval_encoded right_center /\
  EVERY bounded_object_q_interval_encoded right_center_gradient /\
  LENGTH right_center_gradient = 6 /\
  bounded_object_q_interval_encoded right_value /\
  EVERY bounded_object_q_interval_encoded right_gradient_bounds /\
  LENGTH right_gradient_bounds = 6 /\
  EVERY bounded_object_q_interval_encoded right_hessian /\
  LENGTH right_hessian = 21 /\ 4101 < clock ==>
  compute_eval (clock - 4) bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_state_recomplete»
      [from_cv (bounded_object_q_cv_list radii);
       App «candle_cv_bool_and»
         [App «candle_cv_q_packed_object_state_domain»
           [from_cv (bounded_case16594_object_state_cv
             (if left_domain then compute_exec$Num 1 else compute_exec$Num 0)
             left_center (bounded_object_q_cv_list left_center_gradient)
             left_value (bounded_object_q_cv_list left_gradient_bounds)
             (bounded_object_q_cv_list left_hessian))];
          App «candle_cv_q_packed_object_state_domain»
           [from_cv (bounded_case16594_object_state_cv
             (if right_domain then compute_exec$Num 1 else compute_exec$Num 0)
             right_center (bounded_object_q_cv_list right_center_gradient)
             right_value (bounded_object_q_cv_list right_gradient_bounds)
             (bounded_object_q_cv_list right_hessian))]];
       from_cv (bounded_object_q_interval_mul_cv left_center right_center);
       from_cv
         (bounded_object_q_cv_list
           (bounded_object_q_interval_fused_scale_add_cv right_center
             left_center_gradient left_center right_center_gradient));
       from_cv
         (bounded_object_q_cv_list
           (bounded_object_q_interval_fused_hessian_cv left_value right_value
             left_hessian right_hessian
             (bounded_object_q_symmetric_product_pairs_cv
               left_gradient_bounds right_gradient_bounds)))]) (refs:hol_refs) =
  (M_success
    (from_cv
      (bounded_case16594_object_state_mul_cv radii left_domain left_center
        left_center_gradient left_value left_gradient_bounds left_hessian
        right_domain right_center right_center_gradient right_value
        right_gradient_bounds right_hessian)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 4) bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_recomplete»
            [from_cv (bounded_object_q_cv_list radii);
             from_cv
               (if left_domain /\ right_domain then compute_exec$Num 1
                else compute_exec$Num 0);
             from_cv
               (bounded_object_q_interval_mul_cv left_center right_center);
             from_cv
               (bounded_object_q_cv_list
                 (bounded_object_q_interval_fused_scale_add_cv right_center
                   left_center_gradient left_center right_center_gradient));
             from_cv
               (bounded_object_q_cv_list
                 (bounded_object_q_interval_fused_hessian_cv
                   left_value right_value left_hessian right_hessian
                   (bounded_object_q_symmetric_product_pairs_cv
                     left_gradient_bounds right_gradient_bounds)))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateNegEvalTheory.bounded_case16594_object_compute_eval_app5_argument_results_for_neg
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule bounded_case16594_object_state_domain_mul_eval
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_state_recomplete_mul_components_eval
  >> simp []
QED

Theorem bounded_case16594_object_state_mul_complete_eval:
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  bounded_object_q_interval_encoded left_center /\
  EVERY bounded_object_q_interval_encoded left_center_gradient /\
  LENGTH left_center_gradient = 6 /\
  bounded_object_q_interval_encoded left_value /\
  EVERY bounded_object_q_interval_encoded left_gradient_bounds /\
  LENGTH left_gradient_bounds = 6 /\
  EVERY bounded_object_q_interval_encoded left_hessian /\
  LENGTH left_hessian = 21 /\
  bounded_object_q_interval_encoded right_center /\
  EVERY bounded_object_q_interval_encoded right_center_gradient /\
  LENGTH right_center_gradient = 6 /\
  bounded_object_q_interval_encoded right_value /\
  EVERY bounded_object_q_interval_encoded right_gradient_bounds /\
  LENGTH right_gradient_bounds = 6 /\
  EVERY bounded_object_q_interval_encoded right_hessian /\
  LENGTH right_hessian = 21 /\ 4101 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_state_mul»
      [from_cv (bounded_object_q_cv_list radii);
       from_cv (bounded_case16594_object_state_cv
         (if left_domain then compute_exec$Num 1 else compute_exec$Num 0)
         left_center (bounded_object_q_cv_list left_center_gradient)
         left_value (bounded_object_q_cv_list left_gradient_bounds)
         (bounded_object_q_cv_list left_hessian));
       from_cv (bounded_case16594_object_state_cv
         (if right_domain then compute_exec$Num 1 else compute_exec$Num 0)
         right_center (bounded_object_q_cv_list right_center_gradient)
         right_value (bounded_object_q_cv_list right_gradient_bounds)
         (bounded_object_q_cv_list right_hessian))]) (refs:hol_refs) =
  (M_success
    (from_cv
      (bounded_case16594_object_state_mul_cv radii left_domain left_center
        left_center_gradient left_value left_gradient_bounds left_hessian
        right_domain right_center right_center_gradient right_value
        right_gradient_bounds right_hessian)),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_state_mul_eval_from_components
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_cv_list
          (bounded_object_q_interval_fused_scale_add_cv right_center
            left_center_gradient left_center right_center_gradient)`
  >> qexists_tac
       `bounded_object_q_interval_mul_cv left_center right_center`
  >> qexists_tac
       `bounded_object_q_cv_list
          (bounded_object_q_interval_fused_hessian_cv left_value right_value
            left_hessian right_hessian
            (bounded_object_q_symmetric_product_pairs_cv
              left_gradient_bounds right_gradient_bounds))`
  >> rpt conj_tac
  >- (irule bounded_case16594_object_state_center_mul_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule bounded_case16594_object_state_hessian_mul_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule bounded_case16594_object_state_gradient_mul_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_state_recomplete_after_mul_eval
  >> simp []
QED

Theorem bounded_case16594_object_state_mul_eval_semantic:
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
  LENGTH semantic_right_hessian = 21 /\ 4101 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_mul»
        [from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (bounded_case16594_object_state_cv
           (if left_domain then compute_exec$Num 1 else compute_exec$Num 0)
           runtime_left_center
           (bounded_object_q_cv_list runtime_left_center_gradient)
           runtime_left_value
           (bounded_object_q_cv_list runtime_left_gradient_bounds)
           (bounded_object_q_cv_list runtime_left_hessian));
         from_cv (bounded_case16594_object_state_cv
           (if right_domain then compute_exec$Num 1 else compute_exec$Num 0)
           runtime_right_center
           (bounded_object_q_cv_list runtime_right_center_gradient)
           runtime_right_value
           (bounded_object_q_cv_list runtime_right_gradient_bounds)
           (bounded_object_q_cv_list runtime_right_hessian))]) (refs:hol_refs) =
      (M_success (from_cv result_state),refs) /\
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
  >> qexists_tac
       `bounded_case16594_object_state_mul_cv runtime_radii left_domain
          runtime_left_center runtime_left_center_gradient runtime_left_value
          runtime_left_gradient_bounds runtime_left_hessian right_domain
          runtime_right_center runtime_right_center_gradient
          runtime_right_value runtime_right_gradient_bounds
          runtime_right_hessian`
  >> conj_tac
  >- (irule bounded_case16594_object_state_mul_complete_eval
      >> simp [])
  >> PURE_REWRITE_TAC [bounded_case16594_object_state_mul_cv_def]
  >> irule
       compute_boundedCase16594ObjectMulRelationTheory.bounded_case16594_object_mul_recomplete_runtime_semantic_equiv
  >> simp []
QED

val _ = export_theory ();
