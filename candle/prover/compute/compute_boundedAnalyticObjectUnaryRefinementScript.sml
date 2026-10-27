(*****************************************************************************
 * Object-q refinement for the generic scale-2^40 unary Taylor chain rule.
 *
 * The proof-only witnesses below mirror list scaling and the compact
 * symmetric self-outer product without adding executable runtime code.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectUnaryRefinement
Ancestors
  compute_boundedAnalyticObjectTaylorRefinement
Libs
  bossLib preamble

Definition bounded_object_q_interval_list_scale_cv_def:
  bounded_object_q_interval_list_scale_cv scalar values =
    MAP (bounded_object_q_interval_mul_cv scalar) values
End

Theorem bounded_interval64_list_scale_covers_object_q:
  !values object_values result.
    bounded_interval64_covers_object_q scalar object_scalar /\
    LIST_REL bounded_interval64_covers_object_q values object_values /\
    bounded_interval64_list_scale scalar values = SOME result ==>
    LIST_REL bounded_interval64_covers_object_q result
      (bounded_object_q_interval_list_scale_cv object_scalar object_values)
Proof
  Induct
  >> Cases_on `object_values`
  >> rw [compute_boundedIntervalListTheory.bounded_interval64_list_scale_def,
         bounded_object_q_interval_list_scale_cv_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> imp_res_tac
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q
  >> res_tac
  >> fs [bounded_object_q_interval_list_scale_cv_def]
QED

Definition bounded_object_q_interval_self_outer_cv_def:
  bounded_object_q_interval_self_outer_cv [] = [] /\
  bounded_object_q_interval_self_outer_cv (entry::rest) =
    bounded_object_q_interval_list_scale_cv entry (entry::rest) ++
    bounded_object_q_interval_self_outer_cv rest
End

Theorem bounded_interval64_self_outer_covers_object_q:
  !values object_values result.
    LIST_REL bounded_interval64_covers_object_q values object_values /\
    bounded_interval64_self_outer values = SOME result ==>
    LIST_REL bounded_interval64_covers_object_q result
      (bounded_object_q_interval_self_outer_cv object_values)
Proof
  Induct
  >> Cases_on `object_values`
  >> rw [compute_boundedTaylorUnaryTheory.bounded_interval64_self_outer_def,
         bounded_object_q_interval_self_outer_cv_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> imp_res_tac bounded_interval64_list_scale_covers_object_q
  >> res_tac
  >> irule listTheory.LIST_REL_APPEND_suff
  >> simp []
QED

val _ = export_theory ();
