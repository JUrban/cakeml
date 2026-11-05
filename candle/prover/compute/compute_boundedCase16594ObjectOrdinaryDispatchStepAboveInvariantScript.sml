(*****************************************************************************
 * Uniform clock-floor adapters for the ordinary case-16594 dispatcher.
 *
 * The operation-specific invariants already provide the exact runtime result,
 * analytic step, and stack refinement at any sufficiently large single
 * clock.  Successful compute evaluation is independent of the HOL reference
 * state and monotone in clock fuel, so one evaluation at the successor of the
 * operation floor supplies the uniform premise consumed by program traces.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectOrdinaryDispatchStepAboveInvariant
Ancestors
  compute_boundedCase16594ObjectAlgebraicDispatchInvariant
  compute_boundedCase16594ObjectOrdinaryDispatchStepInvariant
  compute_boundedCase16594ObjectOrdinaryPolyInvariant
  compute_boundedCase16594ObjectDispatchStepAboveEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_neg_dispatch_stack_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_state::runtime_rest) (semantic_state::semantic_rest) ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above 4106
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (Num 2) certificates
      (bounded_object_q_cv_list (runtime_state::runtime_rest))
      (bounded_object_q_cv_list (runtime_result::runtime_rest)) certificates /\
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
          `clock` |-> `SUC 4106`, `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_neg_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> asm_rewrite_tac
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_add_dispatch_stack_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_right::runtime_left::runtime_rest)
    (semantic_right::semantic_left::semantic_rest) ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above 4106
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (Num 3) certificates
      (bounded_object_q_cv_list
        (runtime_right::runtime_left::runtime_rest))
      (bounded_object_q_cv_list (runtime_result::runtime_rest)) certificates /\
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
          `clock` |-> `SUC 4106`, `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_add_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> asm_rewrite_tac
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_mul_dispatch_stack_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_right::runtime_left::runtime_rest)
    (semantic_right::semantic_left::semantic_rest) ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above 4106
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (Num 4) certificates
      (bounded_object_q_cv_list
        (runtime_right::runtime_left::runtime_rest))
      (bounded_object_q_cv_list (runtime_result::runtime_rest)) certificates /\
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
          `clock` |-> `SUC 4106`, `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_mul_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> asm_rewrite_tac
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_square_dispatch_stack_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_state::runtime_rest) (semantic_state::semantic_rest) ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above 4106
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (Num 5) certificates
      (bounded_object_q_cv_list (runtime_state::runtime_rest))
      (bounded_object_q_cv_list (runtime_result::runtime_rest)) certificates /\
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
          `clock` |-> `SUC 4106`, `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_square_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> asm_rewrite_tac
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_pi_half_dispatch_stack_eval_above:
  bounded_object_q_taylor_stack_runtime_refines
    runtime_stack semantic_stack ==>
  bounded_case16594_object_dispatch_step_eval_above 4106
    center_boxes outer_boxes radii (Num 0) (Num 8) certificates
    (bounded_object_q_cv_list runtime_stack)
    (bounded_object_q_cv_list
      (bounded_case16594_object_pi_half_runtime_cv::runtime_stack))
    certificates /\
  bounded_object_q_analytic_ordinary_step semantic_radii weights
    semantic_center_boxes semantic_outer_boxes BoundedAnalyticPiHalf
    (semantic_stack,semantic_certificates)
    (bounded_case16594_object_pi_half_semantic::semantic_stack,
     semantic_certificates) /\
  bounded_object_q_taylor_stack_runtime_refines
    (bounded_case16594_object_pi_half_runtime_cv::runtime_stack)
    (bounded_case16594_object_pi_half_semantic::semantic_stack)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_stack` |-> `runtime_stack`,
          `semantic_stack` |-> `semantic_stack`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`, `radii` |-> `radii`,
          `certificates` |-> `certificates`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `semantic_certificates` |-> `semantic_certificates`,
          `clock` |-> `SUC 4106`, `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectPiHalfInvariantTheory.bounded_case16594_object_dispatch_pi_half_eval_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> strip_tac
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> first_assum ACCEPT_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_poly_dispatch_stack_eval_above:
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
      SOME [semantic_result] ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above
      (4105 + LENGTH semantic_program)
      (bounded_object_q_cv_list runtime_center_boxes)
      (bounded_object_q_cv_list runtime_outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      (Num 0) runtime_source certificates
      (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list (runtime_result::runtime_stack)) certificates /\
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
          `certificates` |-> `certificates`,
          `clock` |-> `SUC (4105 + LENGTH semantic_program) - 1`,
          `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectOrdinaryPolyInvariantTheory.bounded_case16594_object_ordinary_poly_eval_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> irule
           compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_inverse_dispatch_stack_eval_above:
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
    (runtime_state::runtime_rest) (semantic_state::semantic_rest) ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above 8213
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (Num 6)
      (bounded_object_q_cv_list
        ([runtime_center_reciprocal;runtime_box_reciprocal] ++
           runtime_certificate_rest))
      (bounded_object_q_cv_list (runtime_state::runtime_rest))
      (bounded_object_q_cv_list (runtime_result::runtime_rest))
      (bounded_object_q_cv_list runtime_certificate_rest) /\
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
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `SUC 8213`, `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectOrdinaryDispatchStepInvariantTheory.bounded_case16594_object_inverse_dispatch_stack_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> first_assum ACCEPT_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_sqrt_dispatch_stack_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_packed_q_interval_valid_cv runtime_center_root /\
  bounded_packed_q_interval_valid_cv runtime_box_root /\
  bounded_packed_q_interval_valid_cv runtime_center_derivative /\
  bounded_packed_q_interval_valid_cv runtime_box_derivative /\
  bounded_packed_q_interval_valid_cv runtime_box_second_reciprocal /\
  runtime_center_root = bounded_interval64_object_q_cv word_center_root /\
  runtime_box_root = bounded_interval64_object_q_cv word_box_root /\
  runtime_center_derivative =
    bounded_interval64_object_q_cv word_center_derivative /\
  runtime_box_derivative =
    bounded_interval64_object_q_cv word_box_derivative /\
  runtime_box_second_reciprocal =
    bounded_interval64_object_q_cv word_box_second_reciprocal /\
  bounded_object_q_sqrt_certificate_exact
    (bounded_object_q_taylor_center semantic_state) runtime_center_root /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_add_cv runtime_center_root runtime_center_root)
    runtime_center_derivative /\
  bounded_object_q_sqrt_certificate_exact
    (bounded_object_q_taylor_value_bound semantic_state) runtime_box_root /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_add_cv runtime_box_root runtime_box_root)
    runtime_box_derivative /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_mul_cv
      (bounded_object_q_interval_add_cv runtime_box_root runtime_box_root)
      (bounded_object_q_interval_add_cv
        (bounded_object_q_taylor_value_bound semantic_state)
        (bounded_object_q_taylor_value_bound semantic_state)))
    runtime_box_second_reciprocal /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_state::runtime_rest) (semantic_state::semantic_rest) ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above 8213
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (Pair (Num 1) source_payload)
      (bounded_object_q_cv_list
        ([runtime_center_root;runtime_box_root;
          runtime_center_derivative;runtime_box_derivative;
          runtime_box_second_reciprocal] ++ runtime_certificate_rest))
      (bounded_object_q_cv_list (runtime_state::runtime_rest))
      (bounded_object_q_cv_list (runtime_result::runtime_rest))
      (bounded_object_q_cv_list runtime_certificate_rest) /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticSqrt
      (semantic_state::semantic_rest,
       BoundedAnalytic64SqrtCertificate word_center_root word_box_root
         word_center_derivative word_box_derivative
         word_box_second_reciprocal::semantic_certificate_rest)
      (bounded_object_q_taylor_sqrt semantic_radii weights
         runtime_center_root runtime_center_derivative
         runtime_box_derivative runtime_box_second_reciprocal semantic_state::
         semantic_rest,
       semantic_certificate_rest) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_sqrt semantic_radii weights
         runtime_center_root runtime_center_derivative
         runtime_box_derivative runtime_box_second_reciprocal semantic_state::
         semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `SUC 8213`, `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectOrdinaryDispatchStepInvariantTheory.bounded_case16594_object_sqrt_dispatch_stack_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> first_assum ACCEPT_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_atan_dispatch_stack_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_packed_q_interval_valid_cv runtime_center_result /\
  bounded_packed_q_interval_valid_cv runtime_center_derivative /\
  bounded_packed_q_interval_valid_cv runtime_box_derivative /\
  bounded_packed_q_interval_valid_cv runtime_box_derivative_square /\
  bounded_object_q_interval_encoded runtime_center_input /\
  bounded_object_q_interval_encoded runtime_box_input /\
  runtime_center_input =
    bounded_interval64_object_q_cv word_center_input /\
  runtime_box_input = bounded_interval64_object_q_cv word_box_input /\
  runtime_center_result =
    bounded_interval64_object_q_cv word_center_result /\
  runtime_center_square =
    bounded_interval64_object_q_cv word_center_square /\
  runtime_center_derivative =
    bounded_interval64_object_q_cv word_center_derivative /\
  runtime_box_square = bounded_interval64_object_q_cv word_box_square /\
  runtime_box_derivative =
    bounded_interval64_object_q_cv word_box_derivative /\
  runtime_box_derivative_square =
    bounded_interval64_object_q_cv word_box_derivative_square /\
  bounded_interval64_atan_range word_center_input word_lower_reciprocal
    word_upper_reciprocal = SOME word_center_result /\
  bounded_object_q_interval_encloses runtime_center_input
    (bounded_object_q_taylor_center semantic_state) /\
  bounded_object_q_interval_encloses runtime_box_input
    (bounded_object_q_taylor_value_bound semantic_state) /\
  bounded_object_q_square_certificate_exact
    (bounded_object_q_taylor_center semantic_state) runtime_center_input
    runtime_center_square /\
  bounded_object_q_square_certificate_exact
    (bounded_object_q_taylor_value_bound semantic_state) runtime_box_input
    runtime_box_square /\
  bounded_object_q_inv_certificate_exact
    (bounded_object_q_atan_denominator_cv runtime_center_square)
    runtime_center_derivative /\
  bounded_object_q_inv_certificate_exact
    (bounded_object_q_atan_denominator_cv runtime_box_square)
    runtime_box_derivative /\
  bounded_object_q_square_certificate_exact runtime_box_derivative
    runtime_box_derivative runtime_box_derivative_square /\
  bounded_case16594_object_atan_fixed_pure_contract runtime_center_input
    runtime_box_input runtime_center_result runtime_center_square
    runtime_center_derivative runtime_box_square runtime_box_derivative
    runtime_box_derivative_square /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_state::runtime_rest) (semantic_state::semantic_rest) ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above 16387
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (Num 7)
      (bounded_object_q_cv_list
        ([runtime_center_input;runtime_box_input;runtime_center_result;
          runtime_center_square;runtime_center_derivative;
          runtime_box_square;runtime_box_derivative;
          runtime_box_derivative_square] ++ runtime_certificate_rest))
      (bounded_object_q_cv_list (runtime_state::runtime_rest))
      (bounded_object_q_cv_list (runtime_result::runtime_rest))
      (bounded_object_q_cv_list runtime_certificate_rest) /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticAtan
      (semantic_state::semantic_rest,
       BoundedAnalytic64AtanCertificate word_lower_reciprocal
         word_upper_reciprocal word_center_derivative word_box_derivative::
         semantic_certificate_rest)
      (bounded_object_q_taylor_atan semantic_radii weights
         runtime_center_result runtime_center_derivative
         runtime_box_derivative runtime_box_derivative_square semantic_state::
         semantic_rest,
       semantic_certificate_rest) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_atan semantic_radii weights
         runtime_center_result runtime_center_derivative
         runtime_box_derivative runtime_box_derivative_square semantic_state::
         semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `SUC 16387`, `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectOrdinaryDispatchStepInvariantTheory.bounded_case16594_object_atan_dispatch_stack_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> first_assum ACCEPT_TAC)
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
