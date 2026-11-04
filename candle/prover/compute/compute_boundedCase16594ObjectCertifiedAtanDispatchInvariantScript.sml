(*****************************************************************************
 * Generic semantic refinement for production atan certificate packets.
 *
 * Unlike the earlier genuine-packet theorem, this layer contains no fixed
 * case-16594 certificate bytes or instruction index.  The evaluator guard
 * is generalized separately; this file establishes the reusable state
 * relation that its successful result must preserve.  Closed numerical
 * checks are collected in a packet contract so that the evaluator plumbing
 * is proved once while each production packet supplies only its data proof.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectCertifiedAtanDispatchInvariant
Ancestors
  compute_boundedCase16594ObjectCertifiedSqrtDispatchInvariant
  compute_boundedCase16594ObjectAtanStepSemanticEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_atan_second_equiv_cong_generic:
  bounded_packed_q_interval_valid_cv derivative_square /\
  bounded_object_q_interval_cv_equiv runtime_source semantic_source ==>
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_atan_second_cv runtime_source derivative_square)
    (bounded_object_q_atan_second_cv semantic_source derivative_square)
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_atan_second_cv_def]
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_neg_cv_equiv_cong
  >> irule
       compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_mul_cv_equiv_cong
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_add_cv_equiv_cong
      >> simp [])
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
  >> metis_tac
       [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded]
QED

Definition bounded_case16594_object_atan_fixed_pure_contract_def:
  bounded_case16594_object_atan_fixed_pure_contract center_input box_input
      center_result center_square center_derivative box_square
      box_derivative box_derivative_square <=>
    compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_atn_certificate»
        [from_cv center_input;from_cv center_result]) = SOME (Num 1) /\
    compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_encloses»
        [from_cv center_square;
         App «candle_cv_q_interval_normalize»
           [App «candle_cv_q_interval_square» [from_cv center_input]]]) =
      SOME (Num 1) /\
    compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [App «candle_cv_q_packed_object_atn_denominator»
          [from_cv center_square];
         from_cv center_derivative]) = SOME (Num 1) /\
    compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_encloses»
        [from_cv box_square;
         App «candle_cv_q_interval_normalize»
           [App «candle_cv_q_interval_square» [from_cv box_input]]]) =
      SOME (Num 1) /\
    compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [App «candle_cv_q_packed_object_atn_denominator»
          [from_cv box_square];
         from_cv box_derivative]) = SOME (Num 1) /\
    compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_square_outer_certificate»
        [from_cv box_derivative;from_cv box_derivative;
         from_cv box_derivative_square]) = SOME (Num 1)
End

Definition bounded_case16594_object_atan_generic_check_expression_def:
  bounded_case16594_object_atan_generic_check_expression
      runtime_center runtime_value_bound center_input box_input
      center_result center_square center_derivative box_square
      box_derivative box_derivative_square =
    App «candle_cv_bool_and»
      [App «candle_cv_q_interval_atn_outer_certificate»
        [from_cv runtime_center;from_cv center_input;
         from_cv center_result];
       App «candle_cv_bool_and»
        [App «candle_cv_q_interval_square_outer_certificate»
          [from_cv runtime_center;from_cv center_input;
           from_cv center_square];
         App «candle_cv_bool_and»
          [App «candle_cv_q_interval_inv_certificate»
            [App «candle_cv_q_packed_object_atn_denominator»
              [from_cv center_square];
             from_cv center_derivative];
           App «candle_cv_bool_and»
            [App «candle_cv_q_interval_square_outer_certificate»
              [from_cv runtime_value_bound;from_cv box_input;
               from_cv box_square];
             App «candle_cv_bool_and»
              [App «candle_cv_q_interval_inv_certificate»
                [App «candle_cv_q_packed_object_atn_denominator»
                  [from_cv box_square];
                 from_cv box_derivative];
               App «candle_cv_q_interval_square_outer_certificate»
                [from_cv box_derivative;from_cv box_derivative;
                 from_cv box_derivative_square]]]]]]
End

Definition bounded_case16594_object_atan_generic_state_check_expression_def:
  bounded_case16594_object_atan_generic_state_check_expression item
      center_input box_input center_result center_square center_derivative
      box_square box_derivative box_derivative_square =
    App «candle_cv_bool_and»
      [App «candle_cv_q_interval_atn_outer_certificate»
        [App «candle_cv_q_packed_object_state_center_value» [from_cv item];
         from_cv center_input;from_cv center_result];
       App «candle_cv_bool_and»
        [App «candle_cv_q_interval_square_outer_certificate»
          [App «candle_cv_q_packed_object_state_center_value» [from_cv item];
           from_cv center_input;from_cv center_square];
         App «candle_cv_bool_and»
          [App «candle_cv_q_interval_inv_certificate»
            [App «candle_cv_q_packed_object_atn_denominator»
              [from_cv center_square];
             from_cv center_derivative];
           App «candle_cv_bool_and»
            [App «candle_cv_q_interval_square_outer_certificate»
              [App «candle_cv_q_packed_object_state_value_bound»
                [from_cv item];
               from_cv box_input;from_cv box_square];
             App «candle_cv_bool_and»
              [App «candle_cv_q_interval_inv_certificate»
                [App «candle_cv_q_packed_object_atn_denominator»
                  [from_cv box_square];
                 from_cv box_derivative];
               App «candle_cv_q_interval_square_outer_certificate»
                [from_cv box_derivative;from_cv box_derivative;
                 from_cv box_derivative_square]]]]]]
End

Theorem bounded_case16594_object_atan_outer_certificate_eval_generic:
  bounded_object_q_interval_encoded source_input /\
  bounded_object_q_interval_encoded word_input /\
  bounded_object_q_interval_encloses word_input source_input /\
  compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_interval_atn_certificate»
      [from_cv word_input;from_cv output]) = SOME (Num 1) /\
  4097 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_atn_outer_certificate»
        [from_cv source_input;from_cv word_input;from_cv output])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp
       [compute_boundedCase16594ObjectAtanOuterCertificateEvalTheory.bounded_case16594_object_q_interval_atn_outer_certificate_unfold,
        compute_boundedCase16594ObjectAtanOuterCertificateEvalTheory.bounded_case16594_object_q_interval_atn_outer_certificate_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectAtanOuterCertificateEvalTheory.bounded_case16594_object_q_interval_encloses_contract_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_square_outer_certificate_eval_generic:
  bounded_object_q_interval_encoded source_input /\
  bounded_object_q_interval_encoded word_input /\
  bounded_object_q_interval_encloses word_input source_input /\
  compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_interval_encloses»
      [from_cv output;
       App «candle_cv_q_interval_normalize»
         [App «candle_cv_q_interval_square» [from_cv word_input]]]) =
    SOME (Num 1) /\
  4097 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_square_outer_certificate»
        [from_cv source_input;from_cv word_input;from_cv output])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp
       [compute_boundedCase16594ObjectAtanAlgebraicCertificateEvalTheory.bounded_case16594_object_q_interval_square_outer_certificate_unfold,
        compute_boundedCase16594ObjectAtanAlgebraicCertificateEvalTheory.bounded_case16594_object_q_interval_square_outer_certificate_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectAtanOuterCertificateEvalTheory.bounded_case16594_object_q_interval_encloses_contract_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_atan_center_outer_state_eval_generic:
  bounded_object_q_interval_encoded runtime_center /\
  bounded_object_q_interval_encoded center_input /\
  bounded_object_q_interval_encloses center_input runtime_center /\
  compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_interval_atn_certificate»
      [from_cv center_input;from_cv center_result]) = SOME (Num 1) /\
  4098 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_atn_outer_certificate»
        [App «candle_cv_q_packed_object_state_center_value»
          [from_cv
            (bounded_case16594_object_state_cv domain_cv runtime_center
              center_gradient runtime_value_bound gradient_bounds hessian)];
         from_cv center_input;from_cv center_result])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_atn_outer_certificate»
            [from_cv runtime_center;from_cv center_input;
             from_cv center_result]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_app3_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_value_eval]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_atan_outer_certificate_eval_generic
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_atan_center_square_state_eval_generic:
  bounded_object_q_interval_encoded runtime_center /\
  bounded_object_q_interval_encoded center_input /\
  bounded_object_q_interval_encloses center_input runtime_center /\
  compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_interval_encloses»
      [from_cv center_square;
       App «candle_cv_q_interval_normalize»
         [App «candle_cv_q_interval_square» [from_cv center_input]]]) =
    SOME (Num 1) /\
  4099 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_square_outer_certificate»
        [App «candle_cv_q_packed_object_state_center_value»
          [from_cv
            (bounded_case16594_object_state_cv domain_cv runtime_center
              center_gradient runtime_value_bound gradient_bounds hessian)];
         from_cv center_input;from_cv center_square])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_square_outer_certificate»
            [from_cv runtime_center;from_cv center_input;
             from_cv center_square]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_app3_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_value_eval]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_square_outer_certificate_eval_generic
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_atan_box_square_state_eval_generic:
  bounded_object_q_interval_encoded runtime_value_bound /\
  bounded_object_q_interval_encoded box_input /\
  bounded_object_q_interval_encloses box_input runtime_value_bound /\
  compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_interval_encloses»
      [from_cv box_square;
       App «candle_cv_q_interval_normalize»
         [App «candle_cv_q_interval_square» [from_cv box_input]]]) =
    SOME (Num 1) /\
  4099 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_square_outer_certificate»
        [App «candle_cv_q_packed_object_state_value_bound»
          [from_cv
            (bounded_case16594_object_state_cv domain_cv runtime_center
              center_gradient runtime_value_bound gradient_bounds hessian)];
         from_cv box_input;from_cv box_square])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_square_outer_certificate»
            [from_cv runtime_value_bound;from_cv box_input;
             from_cv box_square]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_app3_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_value_bound_eval]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_square_outer_certificate_eval_generic
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_atan_generic_check_eval:
  bounded_object_q_interval_encoded runtime_center /\
  bounded_object_q_interval_encoded runtime_value_bound /\
  bounded_object_q_interval_encoded center_input /\
  bounded_object_q_interval_encoded box_input /\
  bounded_object_q_interval_encloses center_input runtime_center /\
  bounded_object_q_interval_encloses box_input runtime_value_bound /\
  bounded_case16594_object_atan_fixed_pure_contract center_input box_input
    center_result center_square center_derivative box_square
    box_derivative box_derivative_square /\
  4097 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (bounded_case16594_object_atan_generic_check_expression
        runtime_center runtime_value_bound center_input box_input
        center_result center_square center_derivative box_square
        box_derivative box_derivative_square) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> fs [bounded_case16594_object_atan_fixed_pure_contract_def]
  >> rewrite_tac
       [bounded_case16594_object_atan_generic_check_expression_def]
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_atan_outer_certificate_eval_generic
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_square_outer_certificate_eval_generic
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule compute_evalPureTheory.compute_eval_pure_refines
      >> qexists_tac `4096`
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_square_outer_certificate_eval_generic
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule compute_evalPureTheory.compute_eval_pure_refines
      >> qexists_tac `4096`
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_atan_generic_state_check_eval:
  bounded_object_q_interval_encoded runtime_center /\
  bounded_object_q_interval_encoded runtime_value_bound /\
  bounded_object_q_interval_encoded center_input /\
  bounded_object_q_interval_encoded box_input /\
  bounded_object_q_interval_encloses center_input runtime_center /\
  bounded_object_q_interval_encloses box_input runtime_value_bound /\
  bounded_case16594_object_atan_fixed_pure_contract center_input box_input
    center_result center_square center_derivative box_square
    box_derivative box_derivative_square /\
  4101 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (bounded_case16594_object_atan_generic_state_check_expression
        (bounded_case16594_object_state_cv domain_cv runtime_center
          center_gradient runtime_value_bound gradient_bounds hessian)
        center_input box_input center_result center_square center_derivative
        box_square box_derivative box_derivative_square) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> fs [bounded_case16594_object_atan_fixed_pure_contract_def]
  >> rewrite_tac
       [bounded_case16594_object_atan_generic_state_check_expression_def]
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_atan_center_outer_state_eval_generic
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_atan_center_square_state_eval_generic
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule compute_evalPureTheory.compute_eval_pure_refines
      >> qexists_tac `4096`
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_atan_box_square_state_eval_generic
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule compute_evalPureTheory.compute_eval_pure_refines
      >> qexists_tac `4096`
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_atan_decomposition_runtime_refines:
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_packed_q_interval_valid_cv center_result /\
  bounded_packed_q_interval_valid_cv center_derivative /\
  bounded_packed_q_interval_valid_cv box_derivative /\
  bounded_packed_q_interval_valid_cv box_derivative_square /\
  bounded_object_q_taylor_runtime_refines runtime_item semantic_state /\
  runtime_item =
    bounded_case16594_object_state_cv runtime_domain runtime_center
      (bounded_object_q_cv_list runtime_center_gradient)
      runtime_value_bound
      (bounded_object_q_cv_list runtime_gradient_bounds)
      (bounded_object_q_cv_list runtime_hessian) ==>
  runtime_domain =
    (if bounded_object_q_taylor_domain semantic_state
     then Num 1 else Num 0) /\
  bounded_object_q_taylor_runtime_refines
    (compute_boundedCase16594ObjectUnaryCompleteEval$bounded_case16594_object_state_unary_cv
      runtime_radii runtime_domain center_result center_derivative
      box_derivative
      (bounded_object_q_atan_second_cv runtime_value_bound
        box_derivative_square)
      runtime_center_gradient runtime_gradient_bounds runtime_hessian)
    (bounded_object_q_taylor_atan semantic_radii weights center_result
      center_derivative box_derivative box_derivative_square
      semantic_state)
Proof
  Cases_on `semantic_state`
  >> strip_tac
  >> `bounded_packed_q_interval_valid_cv
        (bounded_object_q_atan_second_cv c0 box_derivative_square)` by
       (irule
          compute_boundedCase16594ObjectAtanStepSemanticEvalTheory.bounded_case16594_object_atan_second_valid
        >> fs
             [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_def,
              compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def])
  >> `bounded_object_q_interval_cv_equiv center_result center_result /\
      bounded_object_q_interval_cv_equiv
        center_derivative center_derivative /\
      bounded_object_q_interval_cv_equiv box_derivative box_derivative` by
       (rpt conj_tac
        >> irule
             compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
        >> metis_tac
             [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded])
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_runtime_equiv_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_encoded_cv_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_cv_equiv_def,
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_domain_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_list_cv_equiv_encoded]
  >> conj_tac
  >- (asm_simp_tac std_ss
        [compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_atan_def]
      >> irule
           (REWRITE_RULE
             [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_runtime_equiv_def]
             compute_boundedCase16594ObjectUnaryRelationTheory.bounded_case16594_object_unary_runtime_semantic_equiv)
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def]
      >> irule bounded_case16594_object_atan_second_equiv_cong_generic
      >> asm_rewrite_tac [])
  >> rewrite_tac
       [compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_atan_def]
  >> irule
       compute_boundedCase16594ObjectUnaryRelationTheory.bounded_object_q_taylor_unary_semantic_valid
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def]
QED

val _ = export_theory ();
