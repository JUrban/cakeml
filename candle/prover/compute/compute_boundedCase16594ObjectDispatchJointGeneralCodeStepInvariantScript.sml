(*****************************************************************************
 * One fail-closed joint step for every general-code instruction.
 *
 * The fixed-word trace supplies both the typed certificate state and the
 * exact flat packet emitted for this instruction.  The packet ledger proves
 * the packet shape and guards.  This adapter then joins the fixed-word step,
 * object-q semantic step, and production evaluator step while preserving the
 * remaining packet ledger.  Only the six explicitly specialized delta
 * positions are outside this theorem.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchJointGeneralCodeStepInvariant
Ancestors
  compute_boundedCase16594ObjectDispatchJointGeneralStepInvariant
  compute_boundedCase16594Cell0WordDispatchPacketContracts
Libs
  bossLib preamble intLib

Theorem bounded_case16594_certificate_free_packet_state:
  bounded_case16594_certificate_free_ordinary prepared /\
  bounded_analytic64_runtime_certificate_packet prepared word_state =
    SOME packet /\
  bounded_analytic64_program_step radii center_boxes outer_boxes prepared
    word_state = SOME word_next
  ==>
  packet = [] /\ SND word_next = SND word_state
Proof
  Cases_on `prepared`
  >> Cases_on `word_state`
  >> simp
       [compute_boundedCase16594ObjectDispatchJointGeneralStepInvariantTheory.bounded_case16594_certificate_free_ordinary_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_runtime_certificate_packet_def,
        compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> rpt strip_tac
  >> gvs []
QED

Theorem bounded_case16594_object_joint_general_code_step_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  LENGTH runtime_center_box_values = 6 /\
  LENGTH runtime_outer_box_values = 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_center_box_values semantic_center_boxes /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_outer_box_values semantic_outer_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_center_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_outer_boxes /\
  bounded_analytic64_ordinary_instruction prepared /\
  bounded_analytic_instruction_refines 6 source prepared /\
  bounded_analytic64_state_covers_object_q word_state semantic_state /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_boxes semantic_center_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_outer_boxes semantic_outer_boxes /\
  bounded_analytic64_runtime_certificate_packet prepared word_state =
    SOME packet /\
  bounded_analytic64_program_step semantic_radii word_center_boxes
    word_outer_boxes prepared word_state = SOME word_next /\
  bounded_case16594_word_dispatch_packet_contracts (SND word_state)
    (packet ++ packet_rest) /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack
    (FST semantic_state) /\
  (case source of
   | BoundedAnalyticPolynomial source_program =>
       4105 + LENGTH source_program <= 524405
   | _ => T)
  ==>
  ?semantic_next next_runtime_stack.
    bounded_object_q_analytic_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes source prepared
      semantic_state semantic_next /\
    bounded_analytic64_state_covers_object_q word_next semantic_next /\
    bounded_case16594_object_dispatch_step_eval_above 524405
      (bounded_object_q_cv_list runtime_center_box_values)
      (bounded_object_q_cv_list runtime_outer_box_values)
      (bounded_object_q_cv_list runtime_radii) (Num 0)
      (bounded_case16594_analytic_instruction_cv source)
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv (packet ++ packet_rest)))
      (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack)
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv packet_rest)) /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = SND word_next /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_next) packet_rest
Proof
  strip_tac
  >> `bounded_case16594_certificate_free_ordinary prepared \/
      prepared = BoundedAnalytic64Sqrt \/
      prepared = BoundedAnalytic64Inverse \/
      prepared = BoundedAnalytic64Atan` by
       (Cases_on `prepared`
        >> fs
             [compute_boundedCase16594ObjectDispatchJointGeneralStepInvariantTheory.bounded_case16594_certificate_free_ordinary_def,
              compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def])
  >- (`packet = [] /\ SND word_next = SND word_state` by
         metis_tac [bounded_case16594_certificate_free_packet_state]
      >> gvs []
      >> Cases_on `word_state`
      >> Cases_on `semantic_state`
      >> fs
           [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def]
      >> mp_tac
           (Q.INST
             [`source` |-> `source`, `prepared` |-> `prepared`,
              `word_stack` |-> `q`,
              `semantic_certificates` |-> `r`,
              `semantic_stack` |-> `q'`,
              `word_next` |-> `word_next`,
              `runtime_stack` |-> `runtime_stack`,
              `runtime_center_boxes` |-> `runtime_center_box_values`,
              `runtime_outer_boxes` |-> `runtime_outer_box_values`,
              `runtime_certificates` |->
                `bounded_object_q_cv_list
                   (MAP bounded_interval64_object_q_cv packet_rest)`]
             compute_boundedCase16594ObjectDispatchJointGeneralStepInvariantTheory.bounded_case16594_object_joint_certificate_free_step_eval_above)
      >> impl_tac
      >- fs
           [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def]
      >> disch_then
           (qx_choose_then `semantic_next`
             (qx_choose_then `next_runtime_stack` strip_assume_tac))
      >> qexists_tac `semantic_next`
      >> qexists_tac `next_runtime_stack`
      >> gvs [])
  >- (gvs
        [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def]
      >> Cases_on `word_state`
      >> Cases_on `semantic_state`
      >> fs
           [compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_runtime_certificate_packet_def,
            compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
            compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def]
      >> every_case_tac
      >> gvs
           [compute_boundedCase16594Cell0WordDispatchPacketContractsTheory.bounded_case16594_word_dispatch_packet_contracts_def]
      >> mp_tac
           (Q.INST
             [`runtime_radii` |-> `runtime_radii`,
              `semantic_radii` |-> `semantic_radii`,
              `weights` |-> `weights`,
              `source` |-> `BoundedAnalyticSqrt`,
              `word_stack` |-> `h::t'`,
              `semantic_stack` |-> `q'`,
              `center_sqrt` |-> `b`, `box_sqrt` |-> `b0`,
              `center_derivative` |-> `b1`,
              `box_derivative` |-> `b2`,
              `box_second_reciprocal` |-> `b3`,
              `semantic_certificate_rest` |-> `t`,
              `word_next` |-> `(x::t',t)`,
              `runtime_stack` |-> `runtime_stack`,
              `runtime_center_boxes` |->
                `bounded_object_q_cv_list runtime_center_box_values`,
              `runtime_outer_boxes` |->
                `bounded_object_q_cv_list runtime_outer_box_values`,
              `runtime_certificate_rest` |->
                `MAP bounded_interval64_object_q_cv packet_rest`]
             compute_boundedCase16594ObjectDispatchJointCertifiedStepInvariantTheory.bounded_case16594_object_joint_sqrt_step_eval_above)
      >> impl_tac
      >- fs
           [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
            compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
            compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
      >> disch_then
           (qx_choose_then `semantic_next`
             (qx_choose_then `next_runtime_stack` strip_assume_tac))
      >> qexists_tac `semantic_next`
      >> qexists_tac `next_runtime_stack`
      >> gvs [])
  >- (gvs
        [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def]
      >> Cases_on `word_state`
      >> Cases_on `semantic_state`
      >> fs
           [compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_runtime_certificate_packet_def,
            compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
            compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def]
      >> every_case_tac
      >> gvs
           [compute_boundedCase16594Cell0WordDispatchPacketContractsTheory.bounded_case16594_word_dispatch_packet_contracts_def]
      >> Cases_on `h`
      >> Cases_on `q'`
      >> gvs
           [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
            LIST_REL_def]
      >> Cases_on `h`
      >> gvs
           [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def]
      >> mp_tac
           (Q.INST
             [`runtime_radii` |-> `runtime_radii`,
              `semantic_radii` |-> `semantic_radii`,
              `weights` |-> `weights`,
              `source` |-> `BoundedAnalyticInverse`,
              `word_domain` |-> `b'`, `word_center` |-> `b0'`,
              `word_center_gradient` |-> `l`, `word_box` |-> `b1`,
              `word_gradient_bounds` |-> `l0`, `word_hessian` |-> `l1`,
              `word_rest` |-> `t'`, `object_domain` |-> `b''`,
              `object_center` |-> `c`, `object_center_gradient` |-> `l'`,
              `object_box` |-> `c0`, `object_gradient_bounds` |-> `l0'`,
              `object_hessian` |-> `l1'`, `semantic_tail` |-> `t''`,
              `center_reciprocal` |-> `b`, `box_reciprocal` |-> `b0`,
              `semantic_certificate_rest` |-> `t`,
              `word_next` |-> `(x::t',t)`,
              `runtime_stack` |-> `runtime_stack`,
              `runtime_center_boxes` |->
                `bounded_object_q_cv_list runtime_center_box_values`,
              `runtime_outer_boxes` |->
                `bounded_object_q_cv_list runtime_outer_box_values`,
              `runtime_certificate_rest` |->
                `MAP bounded_interval64_object_q_cv packet_rest`]
             compute_boundedCase16594ObjectDispatchJointCertifiedStepInvariantTheory.bounded_case16594_object_joint_inverse_step_eval_above)
      >> impl_tac
      >- fs
           [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
            compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
            compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
            compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def,
            compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
      >> disch_then
           (qx_choose_then `semantic_next`
             (qx_choose_then `next_runtime_stack` strip_assume_tac))
      >> qexists_tac `semantic_next`
      >> qexists_tac `next_runtime_stack`
      >> gvs [])
  >- (gvs
        [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def]
      >> Cases_on `word_state`
      >> Cases_on `semantic_state`
      >> fs
           [compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_runtime_certificate_packet_def,
            compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
            compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def]
      >> every_case_tac
      >> gvs
           [compute_boundedCase16594Cell0WordDispatchPacketContractsTheory.bounded_case16594_word_dispatch_packet_contracts_def]
      >> Cases_on `q'`
      >> gvs
           [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
            LIST_REL_def]
      >> Cases_on `h`
      >> Cases_on `runtime_stack`
      >> gvs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def]
      >> qmatch_assum_rename_tac
           `bounded_taylor64_atan semantic_radii lower_reciprocal
              upper_reciprocal center_derivative box_derivative
              (BoundedTaylor64 word_domain center_input
                word_center_gradient box_input word_gradient_bounds
                word_hessian) = SOME word_result`
      >> qmatch_assum_rename_tac
           `bounded_interval64_atan_range center_input lower_reciprocal
              upper_reciprocal = SOME center_result`
      >> qmatch_assum_rename_tac
           `bounded_interval64_square center_input = SOME center_square`
      >> qmatch_assum_rename_tac
           `bounded_interval64_square box_input = SOME box_square`
      >> qmatch_assum_rename_tac
           `bounded_interval64_square box_derivative =
              SOME box_derivative_square`
      >> qmatch_assum_rename_tac
           `bounded_taylor64_covers_object_q
              (BoundedTaylor64 word_domain center_input
                word_center_gradient box_input word_gradient_bounds
                word_hessian)
              (BoundedObjectQTaylor object_domain object_center
                object_center_gradient object_box object_gradient_bounds
                object_hessian)`
      >> qmatch_assum_rename_tac
           `bounded_object_q_taylor_runtime_refines runtime_head
              (BoundedObjectQTaylor object_domain object_center
                object_center_gradient object_box object_gradient_bounds
                object_hessian)`
      >> qmatch_assum_rename_tac
           `LIST_REL bounded_object_q_taylor_runtime_refines
              runtime_tail semantic_tail`
      >> qmatch_assum_rename_tac
           `LIST_REL bounded_taylor64_covers_object_q word_tail semantic_tail`
      >> mp_tac
           (Q.INST
             [`runtime_radii` |-> `runtime_radii`,
              `semantic_radii` |-> `semantic_radii`,
              `weights` |-> `weights`, `source` |-> `BoundedAnalyticAtan`,
              `word_domain` |-> `word_domain`,
              `word_center` |-> `center_input`,
              `word_center_gradient` |-> `word_center_gradient`,
              `word_box` |-> `box_input`,
              `word_gradient_bounds` |-> `word_gradient_bounds`,
              `word_hessian` |-> `word_hessian`,
              `word_rest` |-> `word_tail`,
              `object_domain` |-> `object_domain`,
              `object_center` |-> `object_center`,
              `object_center_gradient` |-> `object_center_gradient`,
              `object_box` |-> `object_box`,
              `object_gradient_bounds` |-> `object_gradient_bounds`,
              `object_hessian` |-> `object_hessian`,
              `semantic_tail` |-> `semantic_tail`,
              `lower_reciprocal` |-> `lower_reciprocal`,
              `upper_reciprocal` |-> `upper_reciprocal`,
              `center_derivative` |-> `center_derivative`,
              `box_derivative` |-> `box_derivative`,
              `semantic_certificate_rest` |-> `t`,
              `word_next` |-> `(word_result::word_tail,t)`,
              `center_input` |-> `center_input`,
              `box_input` |-> `box_input`,
              `center_result` |-> `center_result`,
              `center_square` |-> `center_square`,
              `box_square` |-> `box_square`,
              `box_derivative_square` |-> `box_derivative_square`,
              `runtime_head` |-> `runtime_head`,
              `runtime_tail` |-> `runtime_tail`,
              `runtime_center_boxes` |->
                `bounded_object_q_cv_list runtime_center_box_values`,
              `runtime_outer_boxes` |->
                `bounded_object_q_cv_list runtime_outer_box_values`,
              `runtime_certificate_rest` |->
                `MAP bounded_interval64_object_q_cv packet_rest`]
             compute_boundedCase16594ObjectDispatchJointCertifiedStepInvariantTheory.bounded_case16594_object_joint_atan_step_eval_above)
      >> impl_tac
      >- fs
           [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
            compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
            compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
            compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
            compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_runtime_certificate_packet_def,
            LIST_REL_def]
      >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
      >> qexists_tac
           `(bounded_object_q_taylor_atan semantic_radii weights
              (bounded_interval64_object_q_cv center_result)
              (bounded_interval64_object_q_cv center_derivative)
              (bounded_interval64_object_q_cv box_derivative)
              (bounded_interval64_object_q_cv box_derivative_square)
              (BoundedObjectQTaylor object_domain object_center
                object_center_gradient object_box object_gradient_bounds
                object_hessian)::semantic_tail,t)`
      >> qexists_tac `runtime_result::runtime_tail`
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
QED

val _ = export_theory ();
