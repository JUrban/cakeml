(*****************************************************************************
 * Complete source/prepared dispatcher, including authenticated delta states.
 *
 * The optimized delta calculations are not identified with the ordinary
 * postfix evaluator: their interval association order is intentionally
 * different.  Instead this relation retains the exact source-specialization
 * guard and records the proved object-rational state returned by the matching
 * optimized calculation.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectCompleteDispatcherRefinement
Ancestors
  compute_boundedAnalyticObjectDeltaFourCoordinateRefinement
Libs
  bossLib preamble

Definition bounded_object_q_analytic_step_def:
  bounded_object_q_analytic_step radii weights object_center_environment
      object_box_environment source prepared object_state object_next <=>
    if bounded_analytic64_ordinary_instruction prepared then
      bounded_object_q_analytic_ordinary_step radii weights
        object_center_environment object_box_environment source
        object_state object_next
    else
      case (prepared,object_state) of
      | (BoundedAnalytic64NegDeltaDerivative coordinate,
          (object_stack,object_certificates)) =>
          bounded_analytic_specialization_ok source
            (BoundedNegDeltaDerivative coordinate) /\
          ?object_result.
            bounded_object_q_delta_neg_derivative_cv radii
              object_center_environment coordinate = SOME object_result /\
            object_next =
              (object_result::object_stack,object_certificates)
      | (BoundedAnalytic64FourCoordinateDelta coordinate,
          (object_stack,object_certificates)) =>
          bounded_analytic_specialization_ok source
            (BoundedFourCoordinateDelta coordinate) /\
          ?object_result.
            bounded_object_q_delta_four_coordinate_cv radii
              object_center_environment object_box_environment coordinate =
                SOME object_result /\
            object_next =
              (object_result::object_stack,object_certificates)
      | _ => F
End

Theorem bounded_analytic64_neg_delta_dispatch_refines_object_q:
  bounded_analytic_instruction_refines 6 source
      (BoundedAnalytic64NegDeltaDerivative coordinate) /\
  bounded_analytic64_state_covers_object_q word_state object_state /\
  LIST_REL bounded_interval64_covers_object_q
      center_environment object_center_environment /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      (BoundedAnalytic64NegDeltaDerivative coordinate) word_state =
        SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_step radii weights
      object_center_environment object_box_environment source
      (BoundedAnalytic64NegDeltaDerivative coordinate)
      object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `word_state`
  >> Cases_on `object_state`
  >> strip_tac
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded_delta64_neg_derivative radii center_environment coordinate =
          SOME word_result`
  >> drule_all
       compute_boundedAnalyticObjectDeltaNegDerivativeRefinementTheory.bounded_delta64_neg_derivative_covers_object_q
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_neg_derivative_cv radii
          object_center_environment coordinate = SOME object_result`
  >> qexists_tac `(object_result::q',r')`
  >> gvs [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
          bounded_object_q_analytic_step_def,
          compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
          compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
QED

Theorem bounded_analytic64_four_coordinate_dispatch_refines_object_q:
  bounded_analytic_instruction_refines 6 source
      (BoundedAnalytic64FourCoordinateDelta coordinate) /\
  bounded_analytic64_state_covers_object_q word_state object_state /\
  LIST_REL bounded_interval64_covers_object_q
      center_environment object_center_environment /\
  LIST_REL bounded_interval64_covers_object_q
      box_environment object_box_environment /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      (BoundedAnalytic64FourCoordinateDelta coordinate) word_state =
        SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_step radii weights
      object_center_environment object_box_environment source
      (BoundedAnalytic64FourCoordinateDelta coordinate)
      object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `word_state`
  >> Cases_on `object_state`
  >> strip_tac
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded_delta64_four_coordinate radii center_environment
          box_environment coordinate = SOME word_result`
  >> drule_all
       compute_boundedAnalyticObjectDeltaFourCoordinateRefinementTheory.bounded_delta64_four_coordinate_covers_object_q
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_four_coordinate_cv radii
          object_center_environment object_box_environment coordinate =
            SOME object_result`
  >> qexists_tac `(object_result::q',r')`
  >> gvs [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
          bounded_object_q_analytic_step_def,
          compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
          compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
QED

Theorem bounded_analytic64_ordinary_complete_dispatch_refines_object_q:
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
    bounded_object_q_analytic_step radii weights
      object_center_environment object_box_environment source prepared
      object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  strip_tac
  >> drule_all
       compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_dispatch_refines_object_q
  >> strip_tac
  >> qexists_tac `object_next`
  >> simp [bounded_object_q_analytic_step_def]
QED

Theorem bounded_analytic64_complete_dispatch_refines_object_q:
  bounded_analytic_instruction_refines 6 source prepared /\
  bounded_analytic64_state_covers_object_q word_state object_state /\
  LIST_REL bounded_interval64_covers_object_q
      center_environment object_center_environment /\
  LIST_REL bounded_interval64_covers_object_q
      box_environment object_box_environment /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      prepared word_state = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_step radii weights
      object_center_environment object_box_environment source prepared
      object_state object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `prepared`
  >> metis_tac
       [compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        bounded_analytic64_ordinary_complete_dispatch_refines_object_q,
        bounded_analytic64_neg_delta_dispatch_refines_object_q,
        bounded_analytic64_four_coordinate_dispatch_refines_object_q]
QED

val _ = export_theory ();
