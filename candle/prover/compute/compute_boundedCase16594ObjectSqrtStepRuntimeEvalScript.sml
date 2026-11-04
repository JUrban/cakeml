(*****************************************************************************
 * Genuine case-16594 instantiation of the complete production square-root
 * instruction.  This is the representation-boundary probe: the theorem uses
 * the authenticated 134-record certificate stream and any production source
 * state related to the exact source-5 Taylor semantics.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSqrtStepRuntimeEval
Ancestors
  compute_boundedCase16594ObjectSqrtStepCompleteEval
  compute_boundedCase16594ObjectSqrtRuntimeCertificateContract
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_after_sqrt_certificates_encode:
  ?certificate_rest.
    bounded_object_q_cv_list certificate_rest =
      bounded_case16594_object_cell0_after_sqrt_certificates_cv
Proof
  qexists_tac
    `THE
      (bounded_object_q_cv_list_decode
        bounded_case16594_object_cell0_after_sqrt_certificates_cv)`
  >> irule
       compute_boundedPackedObjectEntryRefinementTheory.bounded_object_q_cv_list_encode_decode
  >> rewrite_tac
       [compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_after_sqrt_certificates_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_sqrt_certificate_outputs_encoded:
  bounded_object_q_interval_encoded
      bounded_case16594_object_cell0_sqrt_center_root_cv /\
  bounded_object_q_interval_encoded
      bounded_case16594_object_cell0_sqrt_box_root_cv /\
  bounded_object_q_interval_encoded
      bounded_case16594_object_cell0_sqrt_center_derivative_cv /\
  bounded_object_q_interval_encoded
      bounded_case16594_object_cell0_sqrt_box_derivative_cv /\
  bounded_object_q_interval_encoded
      bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv
Proof
  rw
    [compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_center_root_cv_def,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_box_root_cv_def,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_center_derivative_cv_def,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_box_derivative_cv_def,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv_def,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> EVAL_TAC
  >> simp []
QED

Theorem bounded_case16594_object_runtime_refines_selector_contract:
  bounded_object_q_taylor_runtime_refines runtime semantic ==>
  ?runtime_domain runtime_center runtime_center_gradient runtime_value_bound
      runtime_gradient_bounds runtime_hessian.
    runtime =
      bounded_case16594_object_state_cv runtime_domain runtime_center
        (bounded_object_q_cv_list runtime_center_gradient)
        runtime_value_bound
        (bounded_object_q_cv_list runtime_gradient_bounds)
        (bounded_object_q_cv_list runtime_hessian) /\
    runtime_domain =
      (if bounded_object_q_taylor_domain semantic then Num 1 else Num 0) /\
    bounded_object_q_interval_encoded runtime_center /\
    EVERY bounded_object_q_interval_encoded runtime_center_gradient /\
    LENGTH runtime_center_gradient = 6 /\
    bounded_object_q_interval_encoded runtime_value_bound /\
    EVERY bounded_object_q_interval_encoded runtime_gradient_bounds /\
    LENGTH runtime_gradient_bounds = 6 /\
    EVERY bounded_object_q_interval_encoded runtime_hessian /\
    LENGTH runtime_hessian = 21 /\
    bounded_object_q_interval_cv_equiv runtime_center
      (bounded_object_q_taylor_center semantic) /\
    LIST_REL bounded_object_q_interval_cv_equiv runtime_center_gradient
      (bounded_object_q_taylor_center_gradient semantic) /\
    bounded_object_q_interval_cv_equiv runtime_value_bound
      (bounded_object_q_taylor_value_bound semantic) /\
    LIST_REL bounded_object_q_interval_cv_equiv runtime_gradient_bounds
      (bounded_object_q_taylor_gradient_bounds semantic) /\
    LIST_REL bounded_object_q_interval_cv_equiv runtime_hessian
      (bounded_object_q_taylor_hessian semantic)
Proof
  Cases_on `semantic`
  >> strip_tac
  >> drule
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_contract
  >> strip_tac
  >> qexists_tac `if b then Num 1 else Num 0`
  >> qexists_tac `runtime_center`
  >> qexists_tac `runtime_center_gradient`
  >> qexists_tac `runtime_value_bound`
  >> qexists_tac `runtime_gradient_bounds`
  >> qexists_tac `runtime_hessian`
  >> fs
    [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_domain_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_value_bound_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_gradient_bounds_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def]
QED

Theorem bounded_case16594_object_genuine_sqrt_step_eval:
  bounded_object_q_taylor_runtime_refines runtime_item
      bounded_case16594_object_source5_result /\
  8210 < clock ==>
  ?runtime_domain runtime_center runtime_center_gradient runtime_value_bound
      runtime_gradient_bounds runtime_hessian.
    runtime_item =
      bounded_case16594_object_state_cv runtime_domain runtime_center
        (bounded_object_q_cv_list runtime_center_gradient)
        runtime_value_bound
        (bounded_object_q_cv_list runtime_gradient_bounds)
        (bounded_object_q_cv_list runtime_hessian) /\
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_sqrt_step»
          [from_cv bounded_case16594_object_cell0_radii_cv;
           from_cv bounded_case16594_object_cell0_full_certificates_cv;
           from_cv (Pair runtime_item stack_rest)]) (refs:hol_refs) =
      (M_success
        (Pair (Num 1)
          (Pair
            (Pair
              (from_cv
                (bounded_case16594_object_state_unary_cv
                  bounded_case16594_object_cell0_runtime_radii
                  runtime_domain
                  bounded_case16594_object_cell0_sqrt_center_root_cv
                  bounded_case16594_object_cell0_sqrt_center_derivative_cv
                  bounded_case16594_object_cell0_sqrt_box_derivative_cv
                  (bounded_object_q_interval_neg_cv
                    bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv)
                  runtime_center_gradient runtime_gradient_bounds
                  runtime_hessian))
              (from_cv stack_rest))
            (from_cv
              bounded_case16594_object_cell0_after_sqrt_certificates_cv))),
       refs)
Proof
  strip_tac
  >> drule bounded_case16594_object_runtime_refines_selector_contract
  >> disch_then
       (qx_choose_then `runtime_domain`
         (qx_choose_then `runtime_center`
           (qx_choose_then `runtime_center_gradient`
             (qx_choose_then `runtime_value_bound`
               (qx_choose_then `runtime_gradient_bounds`
                 (qx_choose_then `runtime_hessian` strip_assume_tac))))))
  >> mp_tac bounded_case16594_object_after_sqrt_certificates_encode
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
        compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_certificates_sqrt_split]
  >> qpat_x_assum
       `bounded_object_q_cv_list certificate_rest =
          bounded_case16594_object_cell0_after_sqrt_certificates_cv`
       (fn th => PURE_REWRITE_TAC [GSYM th])
  >> irule
       (PURE_REWRITE_RULE
         [listTheory.APPEND,
          compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
         compute_boundedCase16594ObjectSqrtStepCompleteEvalTheory.bounded_case16594_object_sqrt_step_eval)
  >> simp
       [compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_encoded,
        compute_boundedCase16594ObjectFirstPolyRunBridgeTheory.bounded_case16594_object_source0_runtime_radii_length,
        bounded_case16594_object_sqrt_certificate_outputs_encoded,
        compute_boundedCase16594ObjectNegEvalTheory.bounded_object_q_interval_encoded_packed,
        compute_boundedCase16594ObjectSqrtCertificateContractTheory.bounded_case16594_object_sqrt_center_derivative_exact,
        compute_boundedCase16594ObjectSqrtCertificateContractTheory.bounded_case16594_object_sqrt_box_derivative_exact]
  >> fs [listTheory.EVERY_MEM]
  >> metis_tac
       [compute_boundedCase16594ObjectNegEvalTheory.bounded_object_q_interval_encoded_packed,
        compute_boundedCase16594ObjectSqrtRuntimeCertificateContractTheory.bounded_case16594_object_runtime_sqrt_center_root_exact,
        compute_boundedCase16594ObjectSqrtRuntimeCertificateContractTheory.bounded_case16594_object_runtime_sqrt_box_root_exact,
        compute_boundedCase16594ObjectSqrtRuntimeCertificateContractTheory.bounded_case16594_object_runtime_sqrt_box_second_reciprocal_exact]
QED

val _ = export_theory ();
