(*****************************************************************************
 * Joint fixed-word/object/production-dispatch adapter for certificate-free
 * ordinary analytic instructions.
 *
 * This is the reusable step used by the genuine trace induction.  It keeps
 * the fixed-word successor, mathematical object successor, and production
 * evaluator successor tied to one source/prepared instruction.  The three
 * certificate-consuming families are handled by the certified joint theory;
 * the two delta families remain explicit specialized branches.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchJointGeneralStepInvariant
Ancestors
  compute_boundedCase16594ObjectDispatchJointCertifiedStepInvariant
  compute_boundedCase16594ObjectDispatchCanonicalStepInvariant
Libs
  bossLib preamble intLib

Definition bounded_case16594_certificate_free_ordinary_def:
  bounded_case16594_certificate_free_ordinary prepared <=>
    bounded_analytic64_ordinary_instruction prepared /\
    (case prepared of
     | BoundedAnalytic64Sqrt => F
     | BoundedAnalytic64Inverse => F
     | BoundedAnalytic64Atan => F
     | _ => T)
End

Theorem bounded_case16594_object_joint_certificate_free_step_eval_above:
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
  bounded_case16594_certificate_free_ordinary prepared /\
  bounded_analytic_instruction_refines 6 source prepared /\
  bounded_analytic64_state_covers_object_q
    (word_stack,semantic_certificates)
    (semantic_stack,semantic_certificates) /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_boxes semantic_center_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_outer_boxes semantic_outer_boxes /\
  bounded_analytic64_program_step semantic_radii word_center_boxes
    word_outer_boxes prepared (word_stack,semantic_certificates) =
      SOME word_next /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack
    semantic_stack /\
  (case source of
   | BoundedAnalyticPolynomial source_program =>
       4105 + LENGTH source_program <= 524405
   | _ => T)
  ==>
  ?semantic_next next_runtime_stack.
    bounded_object_q_analytic_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes source prepared
      (semantic_stack,semantic_certificates) semantic_next /\
    bounded_analytic64_state_covers_object_q word_next semantic_next /\
    bounded_case16594_object_dispatch_step_eval_above 524405
      (bounded_object_q_cv_list runtime_center_boxes)
      (bounded_object_q_cv_list runtime_outer_boxes)
      (bounded_object_q_cv_list runtime_radii) (Num 0)
      (bounded_case16594_analytic_instruction_cv source)
      runtime_certificates (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack)
      runtime_certificates /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = semantic_certificates
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`source` |-> `source`, `prepared` |-> `prepared`,
          `word_state` |-> `(word_stack,semantic_certificates)`,
          `object_state` |-> `(semantic_stack,semantic_certificates)`,
          `center_environment` |-> `word_center_boxes`,
          `object_center_environment` |-> `semantic_center_boxes`,
          `box_environment` |-> `word_outer_boxes`,
          `object_box_environment` |-> `semantic_outer_boxes`,
          `radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `word_next` |-> `word_next`]
         compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_analytic64_complete_dispatch_refines_object_q)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `semantic_next` strip_assume_tac)
  >> Cases_on `prepared`
  >> gvs
       [bounded_case16594_certificate_free_ordinary_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def]
  >- (qexists_tac `semantic_next`
      >> asm_rewrite_tac []
      >> irule
           compute_boundedCase16594ObjectDispatchCanonicalStepInvariantTheory.bounded_case16594_object_canonical_poly_step_eval_above
      >> fs
           [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def]
      >> conj_tac
      >- (qexists_tac `l`
          >> qexists_tac `semantic_center_boxes`
          >> qexists_tac `semantic_outer_boxes`
          >> qexists_tac `semantic_radii`
          >> qexists_tac `semantic_stack`
          >> qexists_tac `weights`
          >> gvs [])
      >> gvs [])
  >- (qexists_tac `semantic_next`
      >> asm_rewrite_tac []
      >> irule
           compute_boundedCase16594ObjectDispatchCanonicalStepInvariantTheory.bounded_case16594_object_canonical_neg_step_eval_above
      >> asm_rewrite_tac []
      >> qexists_tac `semantic_center_boxes`
      >> qexists_tac `semantic_outer_boxes`
      >> qexists_tac `semantic_radii`
      >> qexists_tac `semantic_stack`
      >> qexists_tac `weights`
      >> asm_rewrite_tac [])
  >- (qexists_tac `semantic_next`
      >> asm_rewrite_tac []
      >> irule
           compute_boundedCase16594ObjectDispatchCanonicalStepInvariantTheory.bounded_case16594_object_canonical_add_step_eval_above
      >> asm_rewrite_tac []
      >> qexists_tac `semantic_center_boxes`
      >> qexists_tac `semantic_outer_boxes`
      >> qexists_tac `semantic_radii`
      >> qexists_tac `semantic_stack`
      >> qexists_tac `weights`
      >> asm_rewrite_tac [])
  >- (qexists_tac `semantic_next`
      >> asm_rewrite_tac []
      >> irule
           compute_boundedCase16594ObjectDispatchCanonicalStepInvariantTheory.bounded_case16594_object_canonical_mul_step_eval_above
      >> asm_rewrite_tac []
      >> qexists_tac `semantic_center_boxes`
      >> qexists_tac `semantic_outer_boxes`
      >> qexists_tac `semantic_radii`
      >> qexists_tac `semantic_stack`
      >> qexists_tac `weights`
      >> asm_rewrite_tac [])
  >- (qexists_tac `semantic_next`
      >> asm_rewrite_tac []
      >> irule
           compute_boundedCase16594ObjectDispatchCanonicalStepInvariantTheory.bounded_case16594_object_canonical_square_step_eval_above
      >> asm_rewrite_tac []
      >> qexists_tac `semantic_center_boxes`
      >> qexists_tac `semantic_outer_boxes`
      >> qexists_tac `semantic_radii`
      >> qexists_tac `semantic_stack`
      >> qexists_tac `weights`
      >> asm_rewrite_tac [])
  >- (qexists_tac `semantic_next`
      >> asm_rewrite_tac []
      >> irule
           compute_boundedCase16594ObjectDispatchCanonicalStepInvariantTheory.bounded_case16594_object_canonical_pi_half_step_eval_above
      >> asm_rewrite_tac []
      >> qexists_tac `semantic_center_boxes`
      >> qexists_tac `semantic_outer_boxes`
      >> qexists_tac `semantic_radii`
      >> qexists_tac `semantic_stack`
      >> qexists_tac `weights`
      >> asm_rewrite_tac [])
QED

val _ = export_theory ();
