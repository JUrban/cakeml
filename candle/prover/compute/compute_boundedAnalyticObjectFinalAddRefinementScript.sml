(*****************************************************************************
 * Final-add object-state boundary for the packed analytic handoff.
 *
 * A source program ending in ordinary addition cannot hide an independently
 * supplied value bound: its final object state is the exact Taylor completion
 * constructed from the resulting center, center gradient, and packed Hessian.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectFinalAddRefinement
Ancestors
  compute_boundedPackedAnalyticSoundBoundary
Libs
  bossLib preamble

Theorem bounded_object_q_analytic_run_append:
  !source_left prepared_left object_start object_finish.
    LENGTH source_left = LENGTH prepared_left ==>
    (bounded_object_q_analytic_run radii weights object_center_environment
       object_box_environment (source_left ++ source_right)
       (prepared_left ++ prepared_right) object_start object_finish <=>
     ?object_middle.
       bounded_object_q_analytic_run radii weights object_center_environment
         object_box_environment source_left prepared_left object_start
         object_middle /\
       bounded_object_q_analytic_run radii weights object_center_environment
         object_box_environment source_right prepared_right object_middle
         object_finish)
Proof
  Induct_on `source_left`
  >- (Cases_on `prepared_left`
      >> simp
           [compute_boundedAnalyticObjectProgramRunRefinementTheory.bounded_object_q_analytic_run_def])
  >> Cases_on `prepared_left`
  >- simp
       [compute_boundedAnalyticObjectProgramRunRefinementTheory.bounded_object_q_analytic_run_def]
  >> rpt gen_tac
  >> simp
       [compute_boundedAnalyticObjectProgramRunRefinementTheory.bounded_object_q_analytic_run_def]
  >> metis_tac []
QED

Theorem bounded_object_q_analytic_run_final_add_complete:
  LENGTH source_prefix = LENGTH prepared_prefix /\
  bounded_object_q_analytic_run radii weights object_center_environment
    object_box_environment
    (source_prefix ++ [BoundedAnalyticAdd])
    (prepared_prefix ++ [BoundedAnalytic64Add]) object_start
    ([BoundedObjectQTaylor object_domain object_center
        object_center_gradient object_value_bound object_gradient_bounds
        object_hessian],[]) ==>
  object_value_bound =
    bounded_object_q_taylor_value_complete_cv object_center
      (bounded_object_q_taylor_error_cv radii object_center_gradient weights
        object_hessian)
Proof
  strip_tac
  >> mp_tac
       (Q.SPECL
         [`source_prefix`, `prepared_prefix`, `object_start`,
          `([BoundedObjectQTaylor object_domain object_center
              object_center_gradient object_value_bound
              object_gradient_bounds object_hessian],[])`]
         (Q.INST
           [`source_right` |-> `[BoundedAnalyticAdd]`,
            `prepared_right` |-> `[BoundedAnalytic64Add]`]
           bounded_object_q_analytic_run_append))
  >> impl_tac >- simp []
  >> strip_tac
  >> fs []
  >> rename1
       `bounded_object_q_analytic_run radii weights object_center_environment
          object_box_environment [BoundedAnalyticAdd]
          [BoundedAnalytic64Add] object_middle
          ([BoundedObjectQTaylor object_domain object_center
              object_center_gradient object_value_bound
              object_gradient_bounds object_hessian],[])`
  >> PairCases_on `object_middle`
  >> Cases_on `object_middle0`
  >> fs
       [compute_boundedAnalyticObjectProgramRunRefinementTheory.bounded_object_q_analytic_run_def,
        compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> Cases_on `t`
  >> fs []
  >> Cases_on `h`
  >> Cases_on `h'`
  >> gvs
       [compute_boundedAnalyticObjectProgramRunRefinementTheory.bounded_object_q_analytic_run_def,
        compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_add_def,
        LET_THM]
QED

val _ = export_theory ();
