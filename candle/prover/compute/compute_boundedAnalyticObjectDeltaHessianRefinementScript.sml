(*****************************************************************************
 * Object-q refinement for the fixed compact delta Hessian.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectDeltaHessianRefinement
Ancestors
  compute_boundedAnalyticObjectDeltaValueRefinement
Libs
  bossLib preamble

Definition bounded_object_q_delta_hessian_six_cv_def:
  bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5 =
    let n0 = bounded_object_q_interval_neg_cv x0;
        n1 = bounded_object_q_interval_neg_cv x1;
        n2 = bounded_object_q_interval_neg_cv x2;
        n3 = bounded_object_q_interval_neg_cv x3;
        n4 = bounded_object_q_interval_neg_cv x4;
        n5 = bounded_object_q_interval_neg_cv x5
    in
      bounded_object_q_interval_sums_cv
        [[n3;n3];
         [x3;x4;n5];
         [x3;n4;x5];
         [n0;n0;x1;x2;n3;n3;x4;x5];
         [x1;n2;x3];
         [n1;x2;x3];
         [n4;n4];
         [n3;x4;x5];
         [x0;n2;x4];
         [x0;n1;n1;x2;x3;n4;n4;x5];
         [n0;x2;x4];
         [n5;n5];
         [x0;n1;x5];
         [n0;x1;x5];
         [x0;x1;n2;n2;x3;x4;n5;n5];
         [n0;n0];
         [x0;x1;n5];
         [x0;x2;n4];
         [n1;n1];
         [x1;x2;n3];
         [n2;n2]]
End

Theorem bounded_delta64_hessian_six_covers_object_q:
  bounded_interval64_covers_object_q word0 object0 /\
  bounded_interval64_covers_object_q word1 object1 /\
  bounded_interval64_covers_object_q word2 object2 /\
  bounded_interval64_covers_object_q word3 object3 /\
  bounded_interval64_covers_object_q word4 object4 /\
  bounded_interval64_covers_object_q word5 object5 /\
  bounded_delta64_hessian
    [word0;word1;word2;word3;word4;word5] = SOME result ==>
  LIST_REL bounded_interval64_covers_object_q result
    (bounded_object_q_delta_hessian_six_cv
      object0 object1 object2 object3 object4 object5)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_neg_covers_object_q
  >> fs [compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_def]
  >> rw [bounded_object_q_delta_hessian_six_cv_def]
  >> match_mp_tac
       (Q.SPECL
         [`[[bounded_interval64_neg word3;bounded_interval64_neg word3];
              [word3;word4;bounded_interval64_neg word5];
              [word3;bounded_interval64_neg word4;word5];
              [bounded_interval64_neg word0;bounded_interval64_neg word0;
               word1;word2;bounded_interval64_neg word3;
               bounded_interval64_neg word3;word4;word5];
              [word1;bounded_interval64_neg word2;word3];
              [bounded_interval64_neg word1;word2;word3];
              [bounded_interval64_neg word4;bounded_interval64_neg word4];
              [bounded_interval64_neg word3;word4;word5];
              [word0;bounded_interval64_neg word2;word4];
              [word0;bounded_interval64_neg word1;
               bounded_interval64_neg word1;word2;word3;
               bounded_interval64_neg word4;
               bounded_interval64_neg word4;word5];
              [bounded_interval64_neg word0;word2;word4];
              [bounded_interval64_neg word5;bounded_interval64_neg word5];
              [word0;bounded_interval64_neg word1;word5];
              [bounded_interval64_neg word0;word1;word5];
              [word0;word1;bounded_interval64_neg word2;
               bounded_interval64_neg word2;word3;word4;
               bounded_interval64_neg word5;
               bounded_interval64_neg word5];
              [bounded_interval64_neg word0;bounded_interval64_neg word0];
              [word0;word1;bounded_interval64_neg word5];
              [word0;word2;bounded_interval64_neg word4];
              [bounded_interval64_neg word1;bounded_interval64_neg word1];
              [word1;word2;bounded_interval64_neg word3];
              [bounded_interval64_neg word2;bounded_interval64_neg word2]]`,
          `[[bounded_object_q_interval_neg_cv object3;
               bounded_object_q_interval_neg_cv object3];
              [object3;object4;bounded_object_q_interval_neg_cv object5];
              [object3;bounded_object_q_interval_neg_cv object4;object5];
              [bounded_object_q_interval_neg_cv object0;
               bounded_object_q_interval_neg_cv object0;object1;object2;
               bounded_object_q_interval_neg_cv object3;
               bounded_object_q_interval_neg_cv object3;object4;object5];
              [object1;bounded_object_q_interval_neg_cv object2;object3];
              [bounded_object_q_interval_neg_cv object1;object2;object3];
              [bounded_object_q_interval_neg_cv object4;
               bounded_object_q_interval_neg_cv object4];
              [bounded_object_q_interval_neg_cv object3;object4;object5];
              [object0;bounded_object_q_interval_neg_cv object2;object4];
              [object0;bounded_object_q_interval_neg_cv object1;
               bounded_object_q_interval_neg_cv object1;object2;object3;
               bounded_object_q_interval_neg_cv object4;
               bounded_object_q_interval_neg_cv object4;object5];
              [bounded_object_q_interval_neg_cv object0;object2;object4];
              [bounded_object_q_interval_neg_cv object5;
               bounded_object_q_interval_neg_cv object5];
              [object0;bounded_object_q_interval_neg_cv object1;object5];
              [bounded_object_q_interval_neg_cv object0;object1;object5];
              [object0;object1;bounded_object_q_interval_neg_cv object2;
               bounded_object_q_interval_neg_cv object2;object3;object4;
               bounded_object_q_interval_neg_cv object5;
               bounded_object_q_interval_neg_cv object5];
              [bounded_object_q_interval_neg_cv object0;
               bounded_object_q_interval_neg_cv object0];
              [object0;object1;bounded_object_q_interval_neg_cv object5];
              [object0;object2;bounded_object_q_interval_neg_cv object4];
              [bounded_object_q_interval_neg_cv object1;
               bounded_object_q_interval_neg_cv object1];
              [object1;object2;bounded_object_q_interval_neg_cv object3];
              [bounded_object_q_interval_neg_cv object2;
               bounded_object_q_interval_neg_cv object2]]`,
          `result`]
         compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_interval64_sums_covers_object_q)
  >> simp [LIST_REL_def]
QED

val _ = export_theory ();
