(*****************************************************************************
 * Complete production evaluator and semantic bridge for object-state
 * addition.  The proof composes center, gradient, packed-Hessian, domain,
 * and recompletion contracts without expanding genuine certificate data.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAddCompleteEval
Ancestors
  compute_boundedCase16594ObjectAddRelation
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_state_add_cv_def:
  bounded_case16594_object_state_add_cv radii left_domain left_center
      left_center_gradient left_hessian right_domain right_center
      right_center_gradient right_hessian =
    let center = bounded_object_q_interval_add_cv left_center right_center;
        center_gradient = MAP2 bounded_object_q_interval_add_cv
          left_center_gradient right_center_gradient;
        hessian = MAP2 bounded_object_q_interval_add_cv
          left_hessian right_hessian
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

Theorem bounded_case16594_object_state_add_cv_unfold:
  bounded_case16594_object_state_add_cv radii left_domain left_center
    left_center_gradient left_hessian right_domain right_center
    right_center_gradient right_hessian =
  bounded_case16594_object_state_cv
    (if left_domain /\ right_domain then compute_exec$Num 1
     else compute_exec$Num 0)
    (bounded_object_q_interval_add_cv left_center right_center)
    (bounded_object_q_cv_list
      (MAP2 bounded_object_q_interval_add_cv
        left_center_gradient right_center_gradient))
    (bounded_packed_q_source_value_bound6_cv radii
      (bounded_object_q_interval_add_cv left_center right_center)
      (MAP2 bounded_object_q_interval_add_cv
        left_center_gradient right_center_gradient)
      (MAP2 bounded_object_q_interval_add_cv left_hessian right_hessian))
    (bounded_object_q_cv_list
      (bounded_packed_q_source_gradient_complete6_cv radii
        (MAP2 bounded_object_q_interval_add_cv
          left_center_gradient right_center_gradient)
        (MAP2 bounded_object_q_interval_add_cv left_hessian right_hessian)))
    (bounded_object_q_cv_list
      (MAP2 bounded_object_q_interval_add_cv left_hessian right_hessian))
Proof
  simp [bounded_case16594_object_state_add_cv_def]
QED

Theorem bounded_case16594_object_interval_list_add_packed_encoded:
  !left right.
    EVERY bounded_packed_q_interval_encoded left /\
    EVERY bounded_packed_q_interval_encoded right /\
    LENGTH left = LENGTH right ==>
    EVERY bounded_packed_q_interval_encoded
      (MAP2 bounded_object_q_interval_add_cv left right)
Proof
  Induct
  >> Cases_on `right`
  >> simp []
  >> metis_tac
       [compute_boundedCase16594ObjectMulHessianEvalTheory.bounded_case16594_packed_interval_add_encoded]
QED

Theorem bounded_case16594_object_state_add_components_shape:
  bounded_object_q_interval_encoded left_center /\
  bounded_object_q_interval_encoded right_center /\
  EVERY bounded_object_q_interval_encoded left_center_gradient /\
  EVERY bounded_object_q_interval_encoded right_center_gradient /\
  LENGTH left_center_gradient = 6 /\ LENGTH right_center_gradient = 6 /\
  EVERY bounded_object_q_interval_encoded left_hessian /\
  EVERY bounded_object_q_interval_encoded right_hessian /\
  LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 ==>
  bounded_packed_q_interval_encoded
    (bounded_object_q_interval_add_cv left_center right_center) /\
  EVERY bounded_packed_q_interval_encoded
    (MAP2 bounded_object_q_interval_add_cv
      left_center_gradient right_center_gradient) /\
  LENGTH (MAP2 bounded_object_q_interval_add_cv
      left_center_gradient right_center_gradient) = 6 /\
  EVERY bounded_packed_q_interval_encoded
    (MAP2 bounded_object_q_interval_add_cv left_hessian right_hessian) /\
  LENGTH (MAP2 bounded_object_q_interval_add_cv
      left_hessian right_hessian) = 21
Proof
  strip_tac
  >> rpt conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulHessianEvalTheory.bounded_case16594_packed_interval_add_encoded
      >> simp
           [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded])
  >- (irule bounded_case16594_object_interval_list_add_packed_encoded
      >> simp
           [compute_boundedCase16594ObjectMulCompleteEvalTheory.bounded_case16594_object_interval_list_packed_encoded])
  >- (metis_tac
        [compute_boundedCase16594ObjectAddRelationTheory.bounded_case16594_object_interval_list_add_cv_length])
  >- (irule bounded_case16594_object_interval_list_add_packed_encoded
      >> simp
           [compute_boundedCase16594ObjectMulCompleteEvalTheory.bounded_case16594_object_interval_list_packed_encoded])
  >> metis_tac
       [compute_boundedCase16594ObjectAddRelationTheory.bounded_case16594_object_interval_list_add_cv_length]
QED

Theorem bounded_case16594_object_state_center_add_eval:
  bounded_object_q_interval_encoded left_center /\
  bounded_object_q_interval_encoded right_center /\
  10 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_interval_add»
      [App «candle_cv_q_packed_object_state_center_value»
        [from_cv (bounded_case16594_object_state_cv left_domain left_center
          left_center_gradient left_value left_gradient_bounds left_hessian)];
       App «candle_cv_q_packed_object_state_center_value»
        [from_cv (bounded_case16594_object_state_cv right_domain right_center
          right_center_gradient right_value right_gradient_bounds right_hessian)]])
    (refs:hol_refs) =
  (M_success
    (from_cv (bounded_object_q_interval_add_cv left_center right_center)),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_add_argument_results
  >> simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded,
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_value_eval]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_gradient_add_eval:
  EVERY bounded_object_q_interval_encoded left_center_gradient /\
  EVERY bounded_object_q_interval_encoded right_center_gradient /\
  LENGTH left_center_gradient = 6 /\ LENGTH right_center_gradient = 6 /\
  60 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_interval_list_add»
      [App «candle_cv_q_packed_object_state_center_gradient»
        [from_cv (bounded_case16594_object_state_cv left_domain left_center
          (bounded_object_q_cv_list left_center_gradient) left_value
          left_gradient_bounds left_hessian)];
       App «candle_cv_q_packed_object_state_center_gradient»
        [from_cv (bounded_case16594_object_state_cv right_domain right_center
          (bounded_object_q_cv_list right_center_gradient) right_value
          right_gradient_bounds right_hessian)]]) (refs:hol_refs) =
  (M_success
    (from_cv (bounded_object_q_cv_list
      (MAP2 bounded_object_q_interval_add_cv
        left_center_gradient right_center_gradient))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_interval_list_add»
            [from_cv (bounded_object_q_cv_list left_center_gradient);
             from_cv (bounded_object_q_cv_list right_center_gradient)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_gradient_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectAddEvalTheory.bounded_case16594_object_interval_list_add_eval
  >> simp
       [compute_boundedCase16594ObjectMulCompleteEvalTheory.bounded_case16594_object_interval_list_packed_encoded]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_hessian_add_eval:
  EVERY bounded_object_q_interval_encoded left_hessian /\
  EVERY bounded_object_q_interval_encoded right_hessian /\
  LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
  180 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_interval_list_add»
      [App «candle_cv_q_packed_object_state_packed_hessian»
        [from_cv (bounded_case16594_object_state_cv left_domain left_center
          left_center_gradient left_value left_gradient_bounds
          (bounded_object_q_cv_list left_hessian))];
       App «candle_cv_q_packed_object_state_packed_hessian»
        [from_cv (bounded_case16594_object_state_cv right_domain right_center
          right_center_gradient right_value right_gradient_bounds
          (bounded_object_q_cv_list right_hessian))]]) (refs:hol_refs) =
  (M_success
    (from_cv (bounded_object_q_cv_list
      (MAP2 bounded_object_q_interval_add_cv
        left_hessian right_hessian))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_interval_list_add»
            [from_cv (bounded_object_q_cv_list left_hessian);
             from_cv (bounded_object_q_cv_list right_hessian)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_packed_hessian_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectAddEvalTheory.bounded_case16594_object_interval_list_add_eval
  >> simp
       [compute_boundedCase16594ObjectMulCompleteEvalTheory.bounded_case16594_object_interval_list_packed_encoded]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_recomplete_after_add_eval:
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  bounded_object_q_interval_encoded left_center /\
  EVERY bounded_object_q_interval_encoded left_center_gradient /\
  LENGTH left_center_gradient = 6 /\
  EVERY bounded_object_q_interval_encoded left_hessian /\
  LENGTH left_hessian = 21 /\
  bounded_object_q_interval_encoded right_center /\
  EVERY bounded_object_q_interval_encoded right_center_gradient /\
  LENGTH right_center_gradient = 6 /\
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
             left_value left_gradient_bounds
             (bounded_object_q_cv_list left_hessian))];
          App «candle_cv_q_packed_object_state_domain»
           [from_cv (bounded_case16594_object_state_cv
             (if right_domain then compute_exec$Num 1 else compute_exec$Num 0)
             right_center (bounded_object_q_cv_list right_center_gradient)
             right_value right_gradient_bounds
             (bounded_object_q_cv_list right_hessian))]];
       from_cv (bounded_object_q_interval_add_cv left_center right_center);
       from_cv (bounded_object_q_cv_list
         (MAP2 bounded_object_q_interval_add_cv
           left_center_gradient right_center_gradient));
       from_cv (bounded_object_q_cv_list
         (MAP2 bounded_object_q_interval_add_cv
           left_hessian right_hessian))]) (refs:hol_refs) =
  (M_success
    (from_cv (bounded_case16594_object_state_add_cv radii left_domain
      left_center left_center_gradient left_hessian right_domain
      right_center right_center_gradient right_hessian)),refs)
Proof
  strip_tac
  >> `bounded_packed_q_interval_encoded
        (bounded_object_q_interval_add_cv left_center right_center) /\
      EVERY bounded_packed_q_interval_encoded
        (MAP2 bounded_object_q_interval_add_cv
          left_center_gradient right_center_gradient) /\
      LENGTH (MAP2 bounded_object_q_interval_add_cv
          left_center_gradient right_center_gradient) = 6 /\
      EVERY bounded_packed_q_interval_encoded
        (MAP2 bounded_object_q_interval_add_cv left_hessian right_hessian) /\
      LENGTH (MAP2 bounded_object_q_interval_add_cv
          left_hessian right_hessian) = 21` by
       (irule bounded_case16594_object_state_add_components_shape
        >> simp [])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 4) bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_recomplete»
            [from_cv (bounded_object_q_cv_list radii);
             from_cv
               (if left_domain /\ right_domain then compute_exec$Num 1
                else compute_exec$Num 0);
             from_cv (bounded_object_q_interval_add_cv
               left_center right_center);
             from_cv (bounded_object_q_cv_list
               (MAP2 bounded_object_q_interval_add_cv
                 left_center_gradient right_center_gradient));
             from_cv (bounded_object_q_cv_list
               (MAP2 bounded_object_q_interval_add_cv
                 left_hessian right_hessian))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateNegEvalTheory.bounded_case16594_object_compute_eval_app5_argument_results_for_neg
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule
           compute_boundedCase16594ObjectMulCompleteEvalTheory.bounded_case16594_object_state_domain_mul_eval
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [bounded_case16594_object_state_add_cv_unfold]
  >> irule
       compute_boundedCase16594ObjectMulCompleteEvalTheory.bounded_case16594_object_state_recomplete_direct_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_add_complete_eval:
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  bounded_object_q_interval_encoded left_center /\
  EVERY bounded_object_q_interval_encoded left_center_gradient /\
  LENGTH left_center_gradient = 6 /\
  EVERY bounded_object_q_interval_encoded left_hessian /\
  LENGTH left_hessian = 21 /\
  bounded_object_q_interval_encoded right_center /\
  EVERY bounded_object_q_interval_encoded right_center_gradient /\
  LENGTH right_center_gradient = 6 /\
  EVERY bounded_object_q_interval_encoded right_hessian /\
  LENGTH right_hessian = 21 /\ 4101 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_state_add»
      [from_cv (bounded_object_q_cv_list radii);
       from_cv (bounded_case16594_object_state_cv
         (if left_domain then compute_exec$Num 1 else compute_exec$Num 0)
         left_center (bounded_object_q_cv_list left_center_gradient)
         left_value left_gradient_bounds
         (bounded_object_q_cv_list left_hessian));
       from_cv (bounded_case16594_object_state_cv
         (if right_domain then compute_exec$Num 1 else compute_exec$Num 0)
         right_center (bounded_object_q_cv_list right_center_gradient)
         right_value right_gradient_bounds
         (bounded_object_q_cv_list right_hessian))]) (refs:hol_refs) =
  (M_success
    (from_cv (bounded_case16594_object_state_add_cv radii left_domain
      left_center left_center_gradient left_hessian right_domain
      right_center right_center_gradient right_hessian)),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectAddControlEvalTheory.bounded_case16594_object_state_add_eval_from_components
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_cv_list
          (MAP2 bounded_object_q_interval_add_cv
            left_center_gradient right_center_gradient)`
  >> qexists_tac
       `bounded_object_q_interval_add_cv left_center right_center`
  >> qexists_tac
       `bounded_object_q_cv_list
          (MAP2 bounded_object_q_interval_add_cv left_hessian right_hessian)`
  >> rpt conj_tac
  >- (irule bounded_case16594_object_state_center_add_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule bounded_case16594_object_state_hessian_add_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule bounded_case16594_object_state_gradient_add_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_state_recomplete_after_add_eval
  >> simp []
QED

Theorem bounded_case16594_object_state_add_eval_semantic:
  !left_domain right_domain.
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_object_q_interval_encoded runtime_left_center /\
  EVERY bounded_object_q_interval_encoded runtime_left_center_gradient /\
  LENGTH runtime_left_center_gradient = 6 /\
  EVERY bounded_object_q_interval_encoded runtime_left_hessian /\
  LENGTH runtime_left_hessian = 21 /\
  bounded_object_q_interval_encoded runtime_right_center /\
  EVERY bounded_object_q_interval_encoded runtime_right_center_gradient /\
  LENGTH runtime_right_center_gradient = 6 /\
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
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_right_hessian semantic_right_hessian /\
  EVERY bounded_packed_q_interval_valid_cv semantic_right_hessian /\
  LENGTH semantic_right_hessian = 21 /\ 4101 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_add»
        [from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (bounded_case16594_object_state_cv
           (if left_domain then compute_exec$Num 1 else compute_exec$Num 0)
           runtime_left_center
           (bounded_object_q_cv_list runtime_left_center_gradient)
           runtime_left_value runtime_left_gradient_bounds
           (bounded_object_q_cv_list runtime_left_hessian));
         from_cv (bounded_case16594_object_state_cv
           (if right_domain then compute_exec$Num 1 else compute_exec$Num 0)
           runtime_right_center
           (bounded_object_q_cv_list runtime_right_center_gradient)
           runtime_right_value runtime_right_gradient_bounds
           (bounded_object_q_cv_list runtime_right_hessian))]) (refs:hol_refs) =
      (M_success (from_cv result_state),refs) /\
    bounded_object_q_taylor_runtime_equiv result_state
      (bounded_object_q_taylor_add semantic_radii weights
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
       `bounded_case16594_object_state_add_cv runtime_radii left_domain
          runtime_left_center runtime_left_center_gradient runtime_left_hessian
          right_domain runtime_right_center runtime_right_center_gradient
          runtime_right_hessian`
  >> conj_tac
  >- (irule bounded_case16594_object_state_add_complete_eval
      >> simp [])
  >> PURE_REWRITE_TAC [bounded_case16594_object_state_add_cv_def]
  >> simp [LET_THM]
  >> irule
       compute_boundedCase16594ObjectAddRelationTheory.bounded_case16594_object_add_recomplete_runtime_semantic_equiv
  >> simp []
QED

val _ = export_theory ();
