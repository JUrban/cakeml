(*****************************************************************************
 * One-step object-q refinement for prepared polynomial postfix programs.
 *
 * This child combines the authenticated source/prepared instruction relation
 * with the word/object Taylor stack relation.  It is intentionally separate
 * from the stable operation theories: source-plan registration and stack
 * induction can change without rebuilding the numerical certificates.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectPolyStepRefinement
Ancestors
  compute_boundedAnalyticPreparedPlanRefinement
  compute_boundedAnalyticObjectPolyProgramRefinement
Libs
  bossLib preamble

Theorem bounded_analytic_rational_interval_covers_object_q:
  bounded_analytic_rational_interval_covers positive negative
      denominator_predecessor word_interval ==>
  bounded_interval64_covers_object_q word_interval
    (bounded_analytic_source_q_interval_cv positive negative
      denominator_predecessor)
Proof
  rw [compute_boundedAnalyticPreparedPlanSoundTheory.bounded_analytic_rational_interval_covers_def,
      compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def,
      compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
      compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
      compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
      compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
      compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
      compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
      compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def,
      compute_boundedAnalyticRationalConstantTheory.bounded_analytic_scale40_def]
QED

Theorem bounded_taylor64_constant_covers_source_q_general:
  bounded_analytic_rational_interval_covers positive negative
      denominator_predecessor word_interval /\
  bounded_taylor64_constant word_interval = SOME result ==>
  bounded_taylor64_covers_object_q result
    (bounded_object_q_taylor_constant positive negative
      denominator_predecessor)
Proof
  strip_tac
  >> `bounded_interval64_valid word_interval` by
       fs [compute_boundedAnalyticPreparedPlanSoundTheory.bounded_analytic_rational_interval_covers_def]
  >> fs [compute_boundedTaylorBaseTheory.bounded_taylor64_constant_def,
         compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
         compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def,
         compute_boundedTaylorBaseTheory.bounded_interval64_zeros_def]
  >> gvs [bounded_taylor64_covers_object_q_def,
          bounded_object_q_taylor_constant_def,
          compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def]
  >> simp [compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
           compute_boundedAnalyticObjectRefinementTheory.bounded_interval64_zeros_cover_object_q_zeros,
           bounded_analytic_rational_interval_covers_object_q]
QED

Theorem bounded_taylor64_poly_constant_step_refines:
  bounded_analytic_rational_interval_covers positive negative
      denominator_predecessor word_interval /\
  bounded_taylor64_stack_covers_object_q word_stack object_stack /\
  bounded_taylor64_program_step radii center_environment box_environment
    (BoundedTaylor64Constant word_interval) word_stack = SOME word_next ==>
  ?object_next.
    bounded_object_q_poly_step radii weights object_center_environment
      object_box_environment
      (BoundedPolyConstant positive negative denominator_predecessor)
      object_stack = SOME object_next /\
    bounded_taylor64_stack_covers_object_q word_next object_next
Proof
  strip_tac
  >> fs [compute_boundedTaylorProgramTheory.bounded_taylor64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> qexists_tac
       `bounded_object_q_taylor_constant positive negative
          denominator_predecessor::object_stack`
  >> simp [bounded_object_q_poly_step_def,
           bounded_taylor64_stack_covers_object_q_def, LIST_REL_def]
  >> gvs [bounded_taylor64_stack_covers_object_q_def, LIST_REL_def]
  >> metis_tac [bounded_taylor64_constant_covers_source_q_general]
QED

Theorem bounded_taylor64_poly_variable_step_refines:
  bounded_taylor64_stack_covers_object_q word_stack object_stack /\
  LIST_REL bounded_interval64_covers_object_q
    center_environment object_center_environment /\
  LIST_REL bounded_interval64_covers_object_q
    box_environment object_box_environment /\
  bounded_taylor64_program_step radii center_environment box_environment
    (BoundedTaylor64Variable index) word_stack = SOME word_next ==>
  ?object_next.
    bounded_object_q_poly_step radii weights object_center_environment
      object_box_environment (BoundedPolyVariable index) object_stack =
        SOME object_next /\
    bounded_taylor64_stack_covers_object_q word_next object_next
Proof
  strip_tac
  >> Cases_on
       `bounded_taylor64_variable center_environment box_environment index`
  >> fs [compute_boundedTaylorProgramTheory.bounded_taylor64_program_step_def]
  >> gvs []
  >> rename1
       `bounded_taylor64_variable center_environment box_environment index =
          SOME word_result`
  >> mp_tac
       (Q.INST
         [`center_environment` |-> `center_environment`,
          `object_center_environment` |-> `object_center_environment`,
          `box_environment` |-> `box_environment`,
          `object_box_environment` |-> `object_box_environment`,
          `index` |-> `index`, `result` |-> `word_result`]
         bounded_taylor64_covers_object_q_variable)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac `object_result::object_stack`
  >> simp [bounded_object_q_poly_step_def,
           bounded_taylor64_stack_covers_object_q_def, LIST_REL_def]
  >> gvs [bounded_taylor64_stack_covers_object_q_def]
QED

Theorem bounded_taylor64_poly_neg_step_refines:
  bounded_taylor64_stack_covers_object_q word_stack object_stack /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_program_step radii center_environment box_environment
    BoundedTaylor64Neg word_stack = SOME word_next ==>
  ?object_next.
    bounded_object_q_poly_step radii weights object_center_environment
      object_box_environment BoundedPolyNeg object_stack = SOME object_next /\
    bounded_taylor64_stack_covers_object_q word_next object_next
Proof
  Cases_on `word_stack`
  >> Cases_on `object_stack`
  >> rw [compute_boundedTaylorProgramTheory.bounded_taylor64_program_step_def,
         bounded_object_q_poly_step_def,
         bounded_taylor64_stack_covers_object_q_def, LIST_REL_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_taylor64_covers_object_q_neg]
QED

Theorem bounded_taylor64_poly_add_step_refines:
  bounded_taylor64_stack_covers_object_q word_stack object_stack /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_program_step radii center_environment box_environment
    BoundedTaylor64Add word_stack = SOME word_next ==>
  ?object_next.
    bounded_object_q_poly_step radii weights object_center_environment
      object_box_environment BoundedPolyAdd object_stack = SOME object_next /\
    bounded_taylor64_stack_covers_object_q word_next object_next
Proof
  Cases_on `word_stack`
  >> Cases_on `object_stack`
  >> rw [compute_boundedTaylorProgramTheory.bounded_taylor64_program_step_def,
         bounded_object_q_poly_step_def,
         bounded_taylor64_stack_covers_object_q_def, LIST_REL_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_taylor64_covers_object_q_add]
QED

Theorem bounded_taylor64_poly_mul_step_refines:
  bounded_taylor64_stack_covers_object_q word_stack object_stack /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_program_step radii center_environment box_environment
    BoundedTaylor64Mul word_stack = SOME word_next ==>
  ?object_next.
    bounded_object_q_poly_step radii weights object_center_environment
      object_box_environment BoundedPolyMul object_stack = SOME object_next /\
    bounded_taylor64_stack_covers_object_q word_next object_next
Proof
  Cases_on `word_stack`
  >> Cases_on `object_stack`
  >> rw [compute_boundedTaylorProgramTheory.bounded_taylor64_program_step_def,
         bounded_object_q_poly_step_def,
         bounded_taylor64_stack_covers_object_q_def, LIST_REL_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_taylor64_covers_object_q_mul]
QED

Theorem bounded_taylor64_poly_square_step_refines:
  bounded_taylor64_stack_covers_object_q word_stack object_stack /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_program_step radii center_environment box_environment
    BoundedTaylor64Square word_stack = SOME word_next ==>
  ?object_next.
    bounded_object_q_poly_step radii weights object_center_environment
      object_box_environment BoundedPolySquare object_stack = SOME object_next /\
    bounded_taylor64_stack_covers_object_q word_next object_next
Proof
  Cases_on `word_stack`
  >> Cases_on `object_stack`
  >> rw [compute_boundedTaylorProgramTheory.bounded_taylor64_program_step_def,
         bounded_object_q_poly_step_def,
         bounded_taylor64_stack_covers_object_q_def, LIST_REL_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_taylor64_covers_object_q_mul]
QED

Theorem bounded_taylor64_poly_step_refines:
  bounded_analytic_poly_instruction_refines 6 source prepared /\
  bounded_taylor64_stack_covers_object_q word_stack object_stack /\
  LIST_REL bounded_interval64_covers_object_q
    center_environment object_center_environment /\
  LIST_REL bounded_interval64_covers_object_q
    box_environment object_box_environment /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_program_step radii center_environment box_environment
    prepared word_stack = SOME word_next ==>
  ?object_next.
    bounded_object_q_poly_step radii weights object_center_environment
      object_box_environment source object_stack = SOME object_next /\
    bounded_taylor64_stack_covers_object_q word_next object_next
Proof
  rw [bounded_analytic_poly_instruction_refines_def]
  >> metis_tac [bounded_taylor64_poly_constant_step_refines,
                bounded_taylor64_poly_variable_step_refines,
                bounded_taylor64_poly_neg_step_refines,
                bounded_taylor64_poly_add_step_refines,
                bounded_taylor64_poly_mul_step_refines,
                bounded_taylor64_poly_square_step_refines]
QED

val _ = export_theory ();
