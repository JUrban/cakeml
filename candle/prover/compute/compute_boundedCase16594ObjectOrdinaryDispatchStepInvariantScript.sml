(*****************************************************************************
 * Stack-level semantic adapters for the certificate-free ordinary branches.
 *
 * The numerical dispatch invariants return one related Taylor item.  Program
 * induction needs the stronger statement that the complete runtime stack is
 * related to the complete object stack and that the matching object-q
 * analytic step was taken.  These adapters provide that interface without
 * re-evaluating any numerical expression or naming a genuine instruction
 * index.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectOrdinaryDispatchStepInvariant
Ancestors
  compute_boundedCase16594ObjectCertifiedAtanDispatchInvariant
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_neg_dispatch_stack_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_state::runtime_rest) (semantic_state::semantic_rest) /\
  4106 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Num 2);from_cv certificates;
         from_cv
           (bounded_object_q_cv_list (runtime_state::runtime_rest))])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair
              (bounded_object_q_cv_list (runtime_result::runtime_rest))
              certificates))),refs) /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticNeg
      (semantic_state::semantic_rest,semantic_certificates)
      (bounded_object_q_taylor_neg semantic_radii weights semantic_state::
         semantic_rest,
       semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_neg semantic_radii weights semantic_state::
         semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_state` |-> `runtime_state`,
          `semantic_state` |-> `semantic_state`,
          `stack_rest` |-> `bounded_object_q_cv_list runtime_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `certificates`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_neg_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> asm_rewrite_tac
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_add_dispatch_stack_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_right::runtime_left::runtime_rest)
    (semantic_right::semantic_left::semantic_rest) /\
  4106 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Num 3);from_cv certificates;
         from_cv
           (bounded_object_q_cv_list
             (runtime_right::runtime_left::runtime_rest))])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair
              (bounded_object_q_cv_list (runtime_result::runtime_rest))
              certificates))),refs) /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticAdd
      (semantic_right::semantic_left::semantic_rest,semantic_certificates)
      (bounded_object_q_taylor_add semantic_radii weights
         semantic_left semantic_right::semantic_rest,
       semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_add semantic_radii weights
         semantic_left semantic_right::semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_left_state` |-> `runtime_left`,
          `semantic_left_state` |-> `semantic_left`,
          `runtime_right_state` |-> `runtime_right`,
          `semantic_right_state` |-> `semantic_right`,
          `stack_rest` |-> `bounded_object_q_cv_list runtime_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `certificates`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_add_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> asm_rewrite_tac
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_mul_dispatch_stack_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_right::runtime_left::runtime_rest)
    (semantic_right::semantic_left::semantic_rest) /\
  4106 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Num 4);from_cv certificates;
         from_cv
           (bounded_object_q_cv_list
             (runtime_right::runtime_left::runtime_rest))])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair
              (bounded_object_q_cv_list (runtime_result::runtime_rest))
              certificates))),refs) /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticMul
      (semantic_right::semantic_left::semantic_rest,semantic_certificates)
      (bounded_object_q_taylor_mul semantic_radii weights
         semantic_left semantic_right::semantic_rest,
       semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_mul semantic_radii weights
         semantic_left semantic_right::semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_left_state` |-> `runtime_left`,
          `semantic_left_state` |-> `semantic_left`,
          `runtime_right_state` |-> `runtime_right`,
          `semantic_right_state` |-> `semantic_right`,
          `stack_rest` |-> `bounded_object_q_cv_list runtime_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `certificates`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_mul_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> asm_rewrite_tac
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_square_dispatch_stack_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_state::runtime_rest) (semantic_state::semantic_rest) /\
  4106 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Num 5);from_cv certificates;
         from_cv
           (bounded_object_q_cv_list (runtime_state::runtime_rest))])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair
              (bounded_object_q_cv_list (runtime_result::runtime_rest))
              certificates))),refs) /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticSquare
      (semantic_state::semantic_rest,semantic_certificates)
      (bounded_object_q_taylor_mul semantic_radii weights semantic_state
         semantic_state::semantic_rest,
       semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_mul semantic_radii weights semantic_state
         semantic_state::semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_state` |-> `runtime_state`,
          `semantic_state` |-> `semantic_state`,
          `stack_rest` |-> `bounded_object_q_cv_list runtime_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `certificates`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_square_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> asm_rewrite_tac
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_poly_dispatch_stack_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  LENGTH runtime_center_boxes = 6 /\
  LENGTH runtime_outer_boxes = 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_center_boxes semantic_center_boxes /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_outer_boxes semantic_outer_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_center_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_outer_boxes /\
  bounded_object_q_taylor_stack_runtime_refines
    runtime_stack semantic_stack /\
  bounded_analytic_instruction_of_cv runtime_source =
    SOME (BoundedAnalyticPolynomial semantic_program) /\
  bounded_object_q_poly_run semantic_radii weights
    semantic_center_boxes semantic_outer_boxes semantic_program [] =
      SOME [semantic_result] /\
  4105 + LENGTH semantic_program < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv (bounded_object_q_cv_list runtime_center_boxes);
         from_cv (bounded_object_q_cv_list runtime_outer_boxes);
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv runtime_source;from_cv certificates;
         from_cv (bounded_object_q_cv_list runtime_stack)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair
            (bounded_object_q_cv_list (runtime_result::runtime_stack))
            certificates))),refs) /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes
      (BoundedAnalyticPolynomial semantic_program)
      (semantic_stack,semantic_certificates)
      (semantic_result::semantic_stack,semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_stack) (semantic_result::semantic_stack)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_center_boxes` |-> `runtime_center_boxes`,
          `runtime_outer_boxes` |-> `runtime_outer_boxes`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `runtime_stack` |-> `runtime_stack`,
          `semantic_stack` |-> `semantic_stack`,
          `runtime_source` |-> `runtime_source`,
          `semantic_program` |-> `semantic_program`,
          `semantic_result` |-> `semantic_result`,
          `certificates` |-> `certificates`, `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         compute_boundedCase16594ObjectOrdinaryPolyInvariantTheory.bounded_case16594_object_ordinary_poly_eval_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_inverse_dispatch_stack_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_packed_q_interval_valid_cv runtime_center_reciprocal /\
  bounded_packed_q_interval_valid_cv runtime_box_reciprocal /\
  runtime_center_reciprocal =
    bounded_interval64_object_q_cv word_center_reciprocal /\
  runtime_box_reciprocal =
    bounded_interval64_object_q_cv word_box_reciprocal /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_taylor_center semantic_state)
    runtime_center_reciprocal /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_taylor_value_bound semantic_state)
    runtime_box_reciprocal /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_state::runtime_rest) (semantic_state::semantic_rest) /\
  8213 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Num 6);
         from_cv
           (bounded_object_q_cv_list
             ([runtime_center_reciprocal;runtime_box_reciprocal] ++
                runtime_certificate_rest));
         from_cv (bounded_object_q_cv_list (runtime_state::runtime_rest))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair
            (bounded_object_q_cv_list (runtime_result::runtime_rest))
            (bounded_object_q_cv_list runtime_certificate_rest)))),refs) /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticInverse
      (semantic_state::semantic_rest,
       BoundedAnalytic64InverseCertificate word_center_reciprocal
         word_box_reciprocal::semantic_certificate_rest)
      (bounded_object_q_taylor_inverse semantic_radii weights
         runtime_center_reciprocal runtime_box_reciprocal semantic_state::
         semantic_rest,
       semantic_certificate_rest) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_inverse semantic_radii weights
         runtime_center_reciprocal runtime_box_reciprocal semantic_state::
         semantic_rest)
Proof
  Cases_on `semantic_state`
  >> rename1
       `BoundedObjectQTaylor object_domain object_center object_center_gradient
          object_value object_gradient_bounds object_hessian`
  >> strip_tac
  >> `bounded_object_q_positive_inv_certificate_exact object_center
        (bounded_interval64_object_q_cv word_center_reciprocal)` by
       (qpat_x_assum
          `bounded_object_q_positive_inv_certificate_exact
             (bounded_object_q_taylor_center _) _` mp_tac
        >> asm_rewrite_tac
             [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def])
  >> `bounded_object_q_positive_inv_certificate_exact object_value
        (bounded_interval64_object_q_cv word_box_reciprocal)` by
       (qpat_x_assum
          `bounded_object_q_positive_inv_certificate_exact
             (bounded_object_q_taylor_value_bound _) _` mp_tac
        >> asm_rewrite_tac
             [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_value_bound_def])
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_reciprocal` |-> `runtime_center_reciprocal`,
          `box_reciprocal` |-> `runtime_box_reciprocal`,
          `certificate_rest` |-> `runtime_certificate_rest`,
          `runtime_item` |-> `runtime_state`,
          `semantic_state` |->
            `BoundedObjectQTaylor object_domain object_center
               object_center_gradient object_value object_gradient_bounds
               object_hessian`,
          `stack_rest` |-> `bounded_object_q_cv_list runtime_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_boundedCase16594ObjectCertifiedInverseDispatchInvariantTheory.bounded_case16594_object_inverse_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def]
      >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> `bounded_object_q_taylor_runtime_refines runtime_result
        (bounded_object_q_taylor_inverse semantic_radii weights
          runtime_center_reciprocal runtime_box_reciprocal
          (BoundedObjectQTaylor object_domain object_center
            object_center_gradient object_value object_gradient_bounds
            object_hessian))` by
       (qpat_x_assum
          `bounded_object_q_taylor_runtime_refines runtime_result _` mp_tac
        >> asm_rewrite_tac [])
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (qpat_x_assum
        `compute_eval _ _ _ _ = _` mp_tac
      >> PURE_REWRITE_TAC
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            compute_execTheory.from_cv_def]
      >> simp [])
  >> conj_tac
  >- gvs
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def,
        compute_boundedAnalyticObjectInverseOperationRefinementTheory.bounded_object_q_inv_certificate_exact_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

val _ = export_theory ();
