(*****************************************************************************
 * Source/prepared dispatcher for ordinary outer analytic instructions.
 *
 * Each constructor already has a focused preservation theorem.  This child
 * performs only structural dispatch through the authenticated plan relation;
 * the two recognized delta instructions remain excluded and visible.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectOrdinaryDispatcherRefinement
Ancestors
  compute_boundedAnalyticObjectProgramStepRefinement
Libs
  bossLib preamble

Definition bounded_analytic64_ordinary_instruction_def:
  bounded_analytic64_ordinary_instruction
      (BoundedAnalytic64NegDeltaDerivative coordinate) = F /\
  bounded_analytic64_ordinary_instruction
      (BoundedAnalytic64FourCoordinateDelta coordinate) = F /\
  bounded_analytic64_ordinary_instruction _ = T
End

Theorem bounded_analytic64_polynomial_dispatch_refines_object_q:
  bounded_analytic_instruction_refines 6
      (BoundedAnalyticPolynomial source_program) prepared /\
  bounded_analytic64_ordinary_instruction prepared /\
  bounded_analytic64_state_covers_object_q word_state object_state /\
  LIST_REL bounded_interval64_covers_object_q
      center_environment object_center_environment /\
  LIST_REL bounded_interval64_covers_object_q
      box_environment object_box_environment /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      prepared word_state = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      (BoundedAnalyticPolynomial source_program) object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `word_state`
  >> Cases_on `object_state`
  >> rw [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
         bounded_analytic64_ordinary_instruction_def]
  >> gvs [bounded_analytic64_ordinary_instruction_def,
          bounded_analytic64_state_covers_object_q_def]
  >> match_mp_tac
       (Q.INST [`word_stack` |-> `q`,
                `certificates` |-> `r`,
                `object_stack` |-> `q'`]
          bounded_analytic64_polynomial_step_refines_object_q)
  >> asm_rewrite_tac [bounded_analytic64_state_covers_object_q_def]
QED

Theorem bounded_analytic64_neg_dispatch_refines_object_q:
  bounded_analytic_instruction_refines 6 BoundedAnalyticNeg prepared /\
  bounded_analytic64_ordinary_instruction prepared /\
  bounded_analytic64_state_covers_object_q word_state object_state /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      prepared word_state = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      BoundedAnalyticNeg object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `word_state`
  >> Cases_on `object_state`
  >> rw [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
         bounded_analytic64_ordinary_instruction_def]
  >> gvs [bounded_analytic64_ordinary_instruction_def]
  >> Cases_on `q`
  >> Cases_on `q'`
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
          LIST_REL_def]
  >> match_mp_tac
       (Q.INST [`word_value` |-> `h`, `word_rest` |-> `t`,
                `object_value` |-> `h'`, `object_rest` |-> `t'`,
                `certificates` |-> `r`]
          bounded_analytic64_neg_step_refines_object_q)
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
          LIST_REL_def]
QED

Theorem bounded_analytic64_add_dispatch_refines_object_q:
  bounded_analytic_instruction_refines 6 BoundedAnalyticAdd prepared /\
  bounded_analytic64_ordinary_instruction prepared /\
  bounded_analytic64_state_covers_object_q word_state object_state /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      prepared word_state = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      BoundedAnalyticAdd object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `word_state`
  >> Cases_on `object_state`
  >> rw [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
         bounded_analytic64_ordinary_instruction_def]
  >> gvs [bounded_analytic64_ordinary_instruction_def]
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> match_mp_tac
       (Q.INST [`word_right` |-> `h`, `word_left` |-> `h'`,
                `word_rest` |-> `t'`, `object_right` |-> `y`,
                `object_left` |-> `y'`, `object_rest` |-> `ys'`,
                `certificates` |-> `r`]
          bounded_analytic64_add_step_refines_object_q)
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
          LIST_REL_def]
QED

Theorem bounded_analytic64_mul_dispatch_refines_object_q:
  bounded_analytic_instruction_refines 6 BoundedAnalyticMul prepared /\
  bounded_analytic64_ordinary_instruction prepared /\
  bounded_analytic64_state_covers_object_q word_state object_state /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      prepared word_state = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      BoundedAnalyticMul object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `word_state`
  >> Cases_on `object_state`
  >> rw [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
         bounded_analytic64_ordinary_instruction_def]
  >> gvs [bounded_analytic64_ordinary_instruction_def]
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> match_mp_tac
       (Q.INST [`word_right` |-> `h`, `word_left` |-> `h'`,
                `word_rest` |-> `t'`, `object_right` |-> `y`,
                `object_left` |-> `y'`, `object_rest` |-> `ys'`,
                `certificates` |-> `r`]
          bounded_analytic64_mul_step_refines_object_q)
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
          LIST_REL_def]
QED

Theorem bounded_analytic64_square_dispatch_refines_object_q:
  bounded_analytic_instruction_refines 6 BoundedAnalyticSquare prepared /\
  bounded_analytic64_ordinary_instruction prepared /\
  bounded_analytic64_state_covers_object_q word_state object_state /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      prepared word_state = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      BoundedAnalyticSquare object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `word_state`
  >> Cases_on `object_state`
  >> rw [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
         bounded_analytic64_ordinary_instruction_def]
  >> gvs [bounded_analytic64_ordinary_instruction_def]
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> match_mp_tac
       (Q.INST [`word_value` |-> `h`, `word_rest` |-> `t`,
                `object_value` |-> `y`, `object_rest` |-> `ys`,
                `certificates` |-> `r`]
          bounded_analytic64_square_step_refines_object_q)
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
          LIST_REL_def]
QED

Theorem bounded_analytic64_pi_half_dispatch_refines_object_q:
  bounded_analytic_instruction_refines 6 BoundedAnalyticPiHalf prepared /\
  bounded_analytic64_ordinary_instruction prepared /\
  bounded_analytic64_state_covers_object_q word_state object_state /\
  bounded_analytic64_program_step radii center_environment box_environment
      prepared word_state = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      BoundedAnalyticPiHalf object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `word_state`
  >> Cases_on `object_state`
  >> rw [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
         bounded_analytic64_ordinary_instruction_def]
  >> gvs [bounded_analytic64_ordinary_instruction_def]
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> gvs [bounded_analytic64_state_covers_object_q_def]
  >> match_mp_tac
       (Q.INST [`word_stack` |-> `q`, `object_stack` |-> `q'`,
                `certificates` |-> `r`]
          bounded_analytic64_pi_half_step_refines_object_q)
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_analytic64_sqrt_dispatch_refines_object_q:
  bounded_analytic_instruction_refines 6 BoundedAnalyticSqrt prepared /\
  bounded_analytic64_ordinary_instruction prepared /\
  bounded_analytic64_state_covers_object_q word_state object_state /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      prepared word_state = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      BoundedAnalyticSqrt object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `word_state`
  >> Cases_on `object_state`
  >> rw [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
         bounded_analytic64_ordinary_instruction_def]
  >> gvs [bounded_analytic64_ordinary_instruction_def]
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> match_mp_tac
       (Q.INST [`word_value` |-> `h`, `word_rest` |-> `t'`,
                `object_value` |-> `y`, `object_rest` |-> `ys`,
                `center_sqrt` |-> `b`, `box_sqrt` |-> `b0`,
                `center_derivative` |-> `b1`, `box_derivative` |-> `b2`,
                `box_second_reciprocal` |-> `b3`,
                `certificate_rest` |-> `t`]
          bounded_analytic64_sqrt_step_refines_object_q)
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
          LIST_REL_def]
QED

Theorem bounded_analytic64_inverse_dispatch_refines_object_q:
  bounded_analytic_instruction_refines 6 BoundedAnalyticInverse prepared /\
  bounded_analytic64_ordinary_instruction prepared /\
  bounded_analytic64_state_covers_object_q word_state object_state /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      prepared word_state = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      BoundedAnalyticInverse object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `word_state`
  >> Cases_on `object_state`
  >> rw [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
         bounded_analytic64_ordinary_instruction_def]
  >> gvs [bounded_analytic64_ordinary_instruction_def]
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> match_mp_tac
       (Q.INST [`word_value` |-> `h`, `word_rest` |-> `t'`,
                `object_value` |-> `y`, `object_rest` |-> `ys`,
                `center_reciprocal` |-> `b`, `box_reciprocal` |-> `b0`,
                `certificate_rest` |-> `t`]
          bounded_analytic64_inverse_step_refines_object_q)
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
          LIST_REL_def]
QED

Theorem bounded_analytic64_atan_dispatch_refines_object_q:
  bounded_analytic_instruction_refines 6 BoundedAnalyticAtan prepared /\
  bounded_analytic64_ordinary_instruction prepared /\
  bounded_analytic64_state_covers_object_q word_state object_state /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      prepared word_state = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      BoundedAnalyticAtan object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `word_state`
  >> Cases_on `object_state`
  >> rw [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
         bounded_analytic64_ordinary_instruction_def]
  >> gvs [bounded_analytic64_ordinary_instruction_def]
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> match_mp_tac
       (Q.INST [`word_value` |-> `h`, `word_rest` |-> `t'`,
                `object_value` |-> `y`, `object_rest` |-> `ys`,
                `center_lower_reciprocal` |-> `b`,
                `center_upper_reciprocal` |-> `b0`,
                `center_derivative` |-> `b1`, `box_derivative` |-> `b2`,
                `certificate_rest` |-> `t`]
          bounded_analytic64_atan_step_refines_object_q)
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
          LIST_REL_def]
QED

Theorem bounded_analytic64_ordinary_dispatch_refines_object_q:
  bounded_analytic_instruction_refines 6 source prepared /\
  bounded_analytic64_ordinary_instruction prepared /\
  bounded_analytic64_state_covers_object_q word_state object_state /\
  LIST_REL bounded_interval64_covers_object_q
      center_environment object_center_environment /\
  LIST_REL bounded_interval64_covers_object_q
      box_environment object_box_environment /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      prepared word_state = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      source object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `source`
  >> metis_tac
       [bounded_analytic64_polynomial_dispatch_refines_object_q,
        bounded_analytic64_sqrt_dispatch_refines_object_q,
        bounded_analytic64_neg_dispatch_refines_object_q,
        bounded_analytic64_add_dispatch_refines_object_q,
        bounded_analytic64_mul_dispatch_refines_object_q,
        bounded_analytic64_square_dispatch_refines_object_q,
        bounded_analytic64_inverse_dispatch_refines_object_q,
        bounded_analytic64_atan_dispatch_refines_object_q,
        bounded_analytic64_pi_half_dispatch_refines_object_q]
QED

val _ = export_theory ();
