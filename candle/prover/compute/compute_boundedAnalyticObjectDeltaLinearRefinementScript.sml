(*****************************************************************************
 * Object-q refinement for the linear helper layer used by the two compact
 * delta evaluators.
 *
 * These witnesses deliberately mirror the executable association order.  No
 * normalization or algebraic reassociation is hidden in the proof boundary:
 * each successful word addition is related to the corresponding exact
 * rational addition.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectDeltaLinearRefinement
Ancestors
  compute_boundedAnalyticObjectDeltaBoundary
Libs
  bossLib preamble

Definition bounded_object_q_interval_sum_aux_cv_def:
  bounded_object_q_interval_sum_aux_cv [] accumulator = accumulator /\
  bounded_object_q_interval_sum_aux_cv (value::rest) accumulator =
    bounded_object_q_interval_sum_aux_cv rest
      (bounded_object_q_interval_add_cv accumulator value)
End

Definition bounded_object_q_interval_sum_cv_def:
  bounded_object_q_interval_sum_cv values =
    bounded_object_q_interval_sum_aux_cv values
      (bounded_analytic_source_q_interval_cv 0 0 0)
End

Theorem bounded_interval64_sum_aux_covers_object_q:
  !word_values object_values word_accumulator object_accumulator result.
    LIST_REL bounded_interval64_covers_object_q
      word_values object_values /\
    bounded_interval64_covers_object_q
      word_accumulator object_accumulator /\
    bounded_interval64_sum_aux word_values word_accumulator = SOME result ==>
    bounded_interval64_covers_object_q result
      (bounded_object_q_interval_sum_aux_cv
        object_values object_accumulator)
Proof
  Induct
  >> Cases_on `object_values`
  >> rw [compute_boundedDeltaTaylorTheory.bounded_interval64_sum_aux_def,
         bounded_object_q_interval_sum_aux_cv_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_add_covers_object_q
  >> res_tac
QED

Theorem bounded_interval64_sum_covers_object_q:
  LIST_REL bounded_interval64_covers_object_q
    word_values object_values /\
  bounded_interval64_sum word_values = SOME result ==>
  bounded_interval64_covers_object_q result
    (bounded_object_q_interval_sum_cv object_values)
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_interval64_sum_def,
      bounded_object_q_interval_sum_cv_def]
  >> match_mp_tac
       (Q.SPECL
         [`word_values`, `object_values`, `bounded_interval64_zero`,
          `bounded_analytic_source_q_interval_cv 0 0 0`, `result`]
         bounded_interval64_sum_aux_covers_object_q)
  >> simp
       [compute_boundedAnalyticObjectRefinementTheory.bounded_interval64_zero_covers_object_q_zero]
QED

Definition bounded_object_q_interval_scale4_cv_def:
  bounded_object_q_interval_scale4_cv value =
    let twice = bounded_object_q_interval_add_cv value value in
      bounded_object_q_interval_add_cv twice twice
End

Theorem bounded_interval64_scale4_covers_object_q:
  bounded_interval64_covers_object_q word_value object_value /\
  bounded_interval64_scale4 word_value = SOME result ==>
  bounded_interval64_covers_object_q result
    (bounded_object_q_interval_scale4_cv object_value)
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_interval64_scale4_def,
      bounded_object_q_interval_scale4_cv_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_add_covers_object_q
  >> metis_tac
       [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_add_covers_object_q]
QED

Definition bounded_object_q_interval_list_scale4_cv_def:
  bounded_object_q_interval_list_scale4_cv values =
    MAP bounded_object_q_interval_scale4_cv values
End

Theorem bounded_interval64_list_scale4_covers_object_q:
  !word_values object_values result.
    LIST_REL bounded_interval64_covers_object_q
      word_values object_values /\
    bounded_interval64_list_scale4 word_values = SOME result ==>
    LIST_REL bounded_interval64_covers_object_q result
      (bounded_object_q_interval_list_scale4_cv object_values)
Proof
  Induct
  >> Cases_on `object_values`
  >> rw [compute_boundedDeltaTaylorTheory.bounded_interval64_list_scale4_def,
         bounded_object_q_interval_list_scale4_cv_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> imp_res_tac bounded_interval64_scale4_covers_object_q
  >> res_tac
  >> fs [bounded_object_q_interval_list_scale4_cv_def]
QED

Definition bounded_object_q_interval_sums_cv_def:
  bounded_object_q_interval_sums_cv values =
    MAP bounded_object_q_interval_sum_cv values
End

Theorem bounded_interval64_sums_covers_object_q:
  !word_values object_values result.
    LIST_REL (LIST_REL bounded_interval64_covers_object_q)
      word_values object_values /\
    bounded_interval64_sums word_values = SOME result ==>
    LIST_REL bounded_interval64_covers_object_q result
      (bounded_object_q_interval_sums_cv object_values)
Proof
  Induct
  >> Cases_on `object_values`
  >> rw [compute_boundedDeltaTaylorTheory.bounded_interval64_sums_def,
         bounded_object_q_interval_sums_cv_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> imp_res_tac bounded_interval64_sum_covers_object_q
  >> res_tac
  >> fs [bounded_object_q_interval_sums_cv_def]
QED

Definition bounded_object_q_interval_list_add_at_cv_def:
  bounded_object_q_interval_list_add_at_cv value 0 [] = [] /\
  bounded_object_q_interval_list_add_at_cv value 0 (entry::rest) =
    bounded_object_q_interval_add_cv entry value::rest /\
  bounded_object_q_interval_list_add_at_cv value (SUC index) [] = [] /\
  bounded_object_q_interval_list_add_at_cv value (SUC index) (entry::rest) =
    entry::bounded_object_q_interval_list_add_at_cv value index rest
End

Theorem bounded_interval64_list_add_at_covers_object_q:
  !index word_values object_values result.
    bounded_interval64_covers_object_q word_value object_value /\
    LIST_REL bounded_interval64_covers_object_q
      word_values object_values /\
    bounded_interval64_list_add_at word_value index word_values =
      SOME result ==>
    LIST_REL bounded_interval64_covers_object_q result
      (bounded_object_q_interval_list_add_at_cv
        object_value index object_values)
Proof
  Induct
  >> Cases_on `word_values`
  >> Cases_on `object_values`
  >> rw [compute_boundedDeltaTaylorTheory.bounded_interval64_list_add_at_def,
         bounded_object_q_interval_list_add_at_cv_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_add_covers_object_q
  >> res_tac
  >> fs [LIST_REL_def]
QED

val _ = export_theory ();
