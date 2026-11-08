(*****************************************************************************
 * Genuine case-16594 instantiation of the complete production atan step.
 * The theorem consumes the authenticated post-inverse certificate stream and
 * applies to every runtime source-8 state related to its exact semantics.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAtanStepRuntimeEval
Ancestors
  compute_boundedCase16594ObjectAtanStepCompleteEval
  compute_boundedCase16594ObjectInverseStepRuntimeEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_after_atan_certificates_encode:
  ?certificate_rest.
    bounded_object_q_cv_list certificate_rest =
      bounded_case16594_object_cell0_after_atan_certificates_cv
Proof
  qexists_tac
    `THE
      (bounded_object_q_cv_list_decode
        bounded_case16594_object_cell0_after_atan_certificates_cv)`
  >> irule
       compute_boundedPackedObjectEntryRefinementTheory.bounded_object_q_cv_list_encode_decode
  >> rewrite_tac
       [compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_after_atan_certificates_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_genuine_atan_step_eval:
  bounded_object_q_taylor_runtime_refines runtime_item
      bounded_case16594_object_source8_result /\
  16384 < clock ==>
  ?runtime_domain runtime_center runtime_center_gradient runtime_value_bound
      runtime_gradient_bounds runtime_hessian.
    runtime_item =
      bounded_case16594_object_state_cv runtime_domain runtime_center
        (bounded_object_q_cv_list runtime_center_gradient)
        runtime_value_bound
        (bounded_object_q_cv_list runtime_gradient_bounds)
        (bounded_object_q_cv_list runtime_hessian) /\
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_atn_step»
          [from_cv bounded_case16594_object_cell0_radii_cv;
           from_cv
             bounded_case16594_object_cell0_after_inverse_certificates_cv;
           from_cv (Pair runtime_item stack_rest)]) (refs:hol_refs) =
      (M_success
        (Pair (Num 1)
          (Pair
            (Pair
              (from_cv
                (bounded_case16594_object_state_unary_cv
                  bounded_case16594_object_cell0_runtime_radii
                  runtime_domain
                  bounded_case16594_object_cell0_atan_center_result_cv
                  bounded_case16594_object_cell0_atan_center_derivative_cv
                  bounded_case16594_object_cell0_atan_box_derivative_cv
                  (bounded_object_q_atan_second_cv runtime_value_bound
                    bounded_case16594_object_cell0_atan_box_derivative_square_cv)
                  runtime_center_gradient runtime_gradient_bounds
                  runtime_hessian))
              (from_cv stack_rest))
            (from_cv
              bounded_case16594_object_cell0_after_atan_certificates_cv))),
       refs)
Proof
  strip_tac
  >> drule
       compute_boundedCase16594ObjectSqrtStepRuntimeEvalTheory.bounded_case16594_object_runtime_refines_selector_contract
  >> disch_then
       (qx_choose_then `runtime_domain`
         (qx_choose_then `runtime_center`
           (qx_choose_then `runtime_center_gradient`
             (qx_choose_then `runtime_value_bound`
               (qx_choose_then `runtime_gradient_bounds`
                 (qx_choose_then `runtime_hessian` strip_assume_tac))))))
  >> mp_tac bounded_case16594_object_after_atan_certificates_encode
  >> disch_then (qx_choose_then `certificate_rest` assume_tac)
  >> qexists_tac `runtime_domain`
  >> qexists_tac `runtime_center`
  >> qexists_tac `runtime_center_gradient`
  >> qexists_tac `runtime_value_bound`
  >> qexists_tac `runtime_gradient_bounds`
  >> qexists_tac `runtime_hessian`
  >> conj_tac
  >> TRY (asm_rewrite_tac [])
  >> PURE_REWRITE_TAC
       [GSYM
          compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_encode,
        compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_certificates_atan_split]
  >> qpat_x_assum
       `bounded_object_q_cv_list certificate_rest =
          bounded_case16594_object_cell0_after_atan_certificates_cv`
       (fn th => PURE_REWRITE_TAC [GSYM th])
  >> irule
       (PURE_REWRITE_RULE
         [listTheory.APPEND,
          compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
         compute_boundedCase16594ObjectAtanStepCompleteEvalTheory.bounded_case16594_object_atan_step_eval)
  >> simp
       [compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_encoded,
        compute_boundedCase16594ObjectFirstPolyRunBridgeTheory.bounded_case16594_object_source0_runtime_radii_length,
        compute_boundedCase16594ObjectNegEvalTheory.bounded_object_q_interval_encoded_packed]
  >> fs [listTheory.EVERY_MEM]
  >> metis_tac
       [compute_boundedCase16594ObjectNegEvalTheory.bounded_object_q_interval_encoded_packed]
QED

val _ = export_theory ();
