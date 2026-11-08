(*****************************************************************************
 * Zero preservation for the shared object-q unary Taylor constructor.
 *
 * These representation-independent lemmas keep the genuine inverse bridge
 * from expanding large rational encodings merely to establish that the
 * derivative fields of a constant expression remain zero.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectUnaryZeroAlgebra
Ancestors
  compute_boundedCase16594ObjectUnaryRelation
  compute_boundedObjectTaylorZeroAlgebra
Libs
  bossLib preamble intLib

Theorem bounded_object_q_interval_list_scale_decodes_zero:
  !scalar values.
    bounded_object_q_interval_encoded scalar /\
    EVERY bounded_object_q_interval_decodes_zero values ==>
    EVERY bounded_object_q_interval_decodes_zero
      (bounded_object_q_interval_list_scale_cv scalar values)
Proof
  gen_tac
  >> Induct
  >- simp
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
  >> gen_tac
  >> simp
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
  >> strip_tac
  >> conj_tac
  >- (irule
        compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_right_decodes_zero
      >> simp [])
  >> first_x_assum mp_tac
  >> simp
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
  >> disch_tac
  >> fs
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
QED

Theorem bounded_object_q_interval_self_outer_decodes_zero:
  !values.
    EVERY bounded_object_q_interval_decodes_zero values ==>
    EVERY bounded_object_q_interval_decodes_zero
      (bounded_object_q_interval_self_outer_cv values)
Proof
  Induct
  >- simp
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_self_outer_cv_def]
  >> gen_tac
  >> simp
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_self_outer_cv_def]
  >> strip_tac
  >> irule bounded_object_q_interval_list_scale_decodes_zero
  >> simp
       [compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_decodes_zero_encoded]
QED

Theorem bounded_object_q_interval_list_add_decodes_zero:
  !left right.
    EVERY bounded_object_q_interval_decodes_zero left /\
    EVERY bounded_object_q_interval_decodes_zero right /\
    LENGTH left = LENGTH right ==>
    EVERY bounded_object_q_interval_decodes_zero
      (MAP2 bounded_object_q_interval_add_cv left right)
Proof
  Induct
  >> Cases_on `right`
  >> simp []
  >> metis_tac
       [compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_decodes_zero]
QED

Theorem bounded_object_q_taylor_unary_hessian_decodes_zero:
  bounded_object_q_interval_encoded box_derivative /\
  bounded_object_q_interval_encoded box_second /\
  EVERY bounded_object_q_interval_decodes_zero gradient_bounds /\
  LENGTH gradient_bounds = 6 /\
  EVERY bounded_object_q_interval_decodes_zero hessian /\
  LENGTH hessian = 21 ==>
  EVERY bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_unary_hessian_cv box_derivative box_second
      gradient_bounds hessian)
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_taylor_unary_hessian_cv_def]
  >> irule bounded_object_q_interval_list_add_decodes_zero
  >> simp
       [bounded_object_q_interval_list_scale_decodes_zero,
        bounded_object_q_interval_self_outer_decodes_zero,
        compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_interval_list_scale_length,
        compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_self_outer_length6]
QED

val _ = export_theory ();
