(*****************************************************************************
 * Object-q refinement for the multiplication helpers used by the compact
 * delta evaluators.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectDeltaProductRefinement
Ancestors
  compute_boundedAnalyticObjectDeltaLinearRefinement
Libs
  bossLib preamble

Definition bounded_object_q_interval_mul3_cv_def:
  bounded_object_q_interval_mul3_cv first second third =
    bounded_object_q_interval_mul_cv
      (bounded_object_q_interval_mul_cv first second) third
End

Theorem bounded_interval64_mul3_covers_object_q:
  bounded_interval64_covers_object_q word_first object_first /\
  bounded_interval64_covers_object_q word_second object_second /\
  bounded_interval64_covers_object_q word_third object_third /\
  bounded_interval64_mul3 word_first word_second word_third = SOME result ==>
  bounded_interval64_covers_object_q result
    (bounded_object_q_interval_mul3_cv
      object_first object_second object_third)
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_interval64_mul3_def,
      bounded_object_q_interval_mul3_cv_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q
  >> metis_tac
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q]
QED

Definition bounded_object_q_interval_list_pairwise_mul_cv_def:
  bounded_object_q_interval_list_pairwise_mul_cv left right =
    MAP2 bounded_object_q_interval_mul_cv left right
End

Theorem bounded_interval64_list_pairwise_mul_covers_object_q:
  !left right object_left object_right result.
    LIST_REL bounded_interval64_covers_object_q left object_left /\
    LIST_REL bounded_interval64_covers_object_q right object_right /\
    bounded_interval64_list_pairwise_mul left right = SOME result ==>
    LIST_REL bounded_interval64_covers_object_q result
      (bounded_object_q_interval_list_pairwise_mul_cv
        object_left object_right)
Proof
  Induct
  >> Cases_on `right`
  >> Cases_on `object_left`
  >> Cases_on `object_right`
  >> rw [compute_boundedIntervalListTheory.bounded_interval64_list_pairwise_mul_def,
         bounded_object_q_interval_list_pairwise_mul_cv_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> imp_res_tac
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q
  >> res_tac
  >> fs [bounded_object_q_interval_list_pairwise_mul_cv_def]
QED

Definition bounded_object_q_delta_pair_products_six_cv_def:
  bounded_object_q_delta_pair_products_six_cv x0 x1 x2 x3 x4 x5 =
    bounded_object_q_interval_list_pairwise_mul_cv
      [x0;x0;x0;x0;x0;x0;
       x1;x1;x1;x1;x1;
       x2;x2;x2;x2;
       x3;x3;x3;
       x4;x4;
       x5]
      [x0;x1;x2;x3;x4;x5;
       x1;x2;x3;x4;x5;
       x2;x3;x4;x5;
       x3;x4;x5;
       x4;x5;
       x5]
End

Theorem bounded_delta64_pair_products_six_covers_object_q:
  bounded_interval64_covers_object_q word_x0 object_x0 /\
  bounded_interval64_covers_object_q word_x1 object_x1 /\
  bounded_interval64_covers_object_q word_x2 object_x2 /\
  bounded_interval64_covers_object_q word_x3 object_x3 /\
  bounded_interval64_covers_object_q word_x4 object_x4 /\
  bounded_interval64_covers_object_q word_x5 object_x5 /\
  bounded_delta64_pair_products
    [word_x0;word_x1;word_x2;word_x3;word_x4;word_x5] = SOME result ==>
  LIST_REL bounded_interval64_covers_object_q result
    (bounded_object_q_delta_pair_products_six_cv
      object_x0 object_x1 object_x2 object_x3 object_x4 object_x5)
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_pair_products_def,
      bounded_object_q_delta_pair_products_six_cv_def]
  >> match_mp_tac bounded_interval64_list_pairwise_mul_covers_object_q
  >> qexists_tac
       `[word_x0;word_x0;word_x0;word_x0;word_x0;word_x0;
         word_x1;word_x1;word_x1;word_x1;word_x1;
         word_x2;word_x2;word_x2;word_x2;
         word_x3;word_x3;word_x3;
         word_x4;word_x4;
         word_x5]`
  >> qexists_tac
       `[word_x0;word_x1;word_x2;word_x3;word_x4;word_x5;
         word_x1;word_x2;word_x3;word_x4;word_x5;
         word_x2;word_x3;word_x4;word_x5;
         word_x3;word_x4;word_x5;
         word_x4;word_x5;
         word_x5]`
  >> simp [LIST_REL_def]
QED

val _ = export_theory ();
