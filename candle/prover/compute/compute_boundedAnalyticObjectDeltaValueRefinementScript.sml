(*****************************************************************************
 * Object-q refinement for the compact delta value evaluator.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectDeltaValueRefinement
Ancestors
  compute_boundedAnalyticObjectDeltaProductRefinement
Libs
  bossLib preamble

Theorem bounded_interval64_sum6_covers_object_q:
  bounded_interval64_covers_object_q word0 object0 /\
  bounded_interval64_covers_object_q word1 object1 /\
  bounded_interval64_covers_object_q word2 object2 /\
  bounded_interval64_covers_object_q word3 object3 /\
  bounded_interval64_covers_object_q word4 object4 /\
  bounded_interval64_covers_object_q word5 object5 /\
  bounded_interval64_sum [word0;word1;word2;word3;word4;word5] =
    SOME result ==>
  bounded_interval64_covers_object_q result
    (bounded_object_q_interval_sum_cv
      [object0;object1;object2;object3;object4;object5])
Proof
  strip_tac
  >> match_mp_tac
       (Q.INST
         [`word_values` |-> `[word0;word1;word2;word3;word4;word5]`,
          `object_values` |-> `[object0;object1;object2;object3;object4;object5]`,
          `result` |-> `result`]
         compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_interval64_sum_covers_object_q)
  >> simp [LIST_REL_def]
QED

Theorem bounded_interval64_sum7_covers_object_q:
  bounded_interval64_covers_object_q word0 object0 /\
  bounded_interval64_covers_object_q word1 object1 /\
  bounded_interval64_covers_object_q word2 object2 /\
  bounded_interval64_covers_object_q word3 object3 /\
  bounded_interval64_covers_object_q word4 object4 /\
  bounded_interval64_covers_object_q word5 object5 /\
  bounded_interval64_covers_object_q word6 object6 /\
  bounded_interval64_sum
    [word0;word1;word2;word3;word4;word5;word6] = SOME result ==>
  bounded_interval64_covers_object_q result
    (bounded_object_q_interval_sum_cv
      [object0;object1;object2;object3;object4;object5;object6])
Proof
  strip_tac
  >> match_mp_tac
       (Q.INST
         [`word_values` |-> `[word0;word1;word2;word3;word4;word5;word6]`,
          `object_values` |->
            `[object0;object1;object2;object3;object4;object5;object6]`,
          `result` |-> `result`]
         compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_interval64_sum_covers_object_q)
  >> simp [LIST_REL_def]
QED

Theorem bounded_delta64_value_six_trace:
  bounded_delta64_value_six word0 word1 word2 word3 word4 word5 =
    SOME result ==>
  ?first_linear second_linear third_linear first_product second_product
      third_product fourth_product fifth_product sixth_product seventh_product.
    bounded_interval64_sum
      [bounded_interval64_neg word0;word1;word2;
       bounded_interval64_neg word3;word4;word5] = SOME first_linear /\
    bounded_interval64_sum
      [word0;bounded_interval64_neg word1;word2;word3;
       bounded_interval64_neg word4;word5] = SOME second_linear /\
    bounded_interval64_sum
      [word0;word1;bounded_interval64_neg word2;word3;word4;
       bounded_interval64_neg word5] = SOME third_linear /\
    bounded_interval64_mul3 word0 word3 first_linear = SOME first_product /\
    bounded_interval64_mul3 word1 word4 second_linear = SOME second_product /\
    bounded_interval64_mul3 word2 word5 third_linear = SOME third_product /\
    bounded_interval64_mul3 word1 word2 word3 = SOME fourth_product /\
    bounded_interval64_mul3 word0 word2 word4 = SOME fifth_product /\
    bounded_interval64_mul3 word0 word1 word5 = SOME sixth_product /\
    bounded_interval64_mul3 word3 word4 word5 = SOME seventh_product /\
    bounded_interval64_sum
      [first_product;second_product;third_product;
       bounded_interval64_neg fourth_product;
       bounded_interval64_neg fifth_product;
       bounded_interval64_neg sixth_product;
       bounded_interval64_neg seventh_product] = SOME result
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_value_six_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Definition bounded_object_q_delta_value_six_cv_def:
  bounded_object_q_delta_value_six_cv object0 object1 object2 object3
      object4 object5 =
    let first_linear = bounded_object_q_interval_sum_cv
          [bounded_object_q_interval_neg_cv object0;object1;object2;
           bounded_object_q_interval_neg_cv object3;object4;object5];
        second_linear = bounded_object_q_interval_sum_cv
          [object0;bounded_object_q_interval_neg_cv object1;object2;object3;
           bounded_object_q_interval_neg_cv object4;object5];
        third_linear = bounded_object_q_interval_sum_cv
          [object0;object1;bounded_object_q_interval_neg_cv object2;object3;
           object4;bounded_object_q_interval_neg_cv object5];
        first = bounded_object_q_interval_mul3_cv object0 object3 first_linear;
        second = bounded_object_q_interval_mul3_cv object1 object4 second_linear;
        third = bounded_object_q_interval_mul3_cv object2 object5 third_linear;
        fourth = bounded_object_q_interval_mul3_cv object1 object2 object3;
        fifth = bounded_object_q_interval_mul3_cv object0 object2 object4;
        sixth = bounded_object_q_interval_mul3_cv object0 object1 object5;
        seventh = bounded_object_q_interval_mul3_cv object3 object4 object5
    in
      bounded_object_q_interval_sum_cv
        [first;second;third;bounded_object_q_interval_neg_cv fourth;
         bounded_object_q_interval_neg_cv fifth;
         bounded_object_q_interval_neg_cv sixth;
         bounded_object_q_interval_neg_cv seventh]
End

Theorem bounded_delta64_value_six_covers_object_q:
  bounded_interval64_covers_object_q word0 object0 /\
  bounded_interval64_covers_object_q word1 object1 /\
  bounded_interval64_covers_object_q word2 object2 /\
  bounded_interval64_covers_object_q word3 object3 /\
  bounded_interval64_covers_object_q word4 object4 /\
  bounded_interval64_covers_object_q word5 object5 /\
  bounded_delta64_value_six word0 word1 word2 word3 word4 word5 =
    SOME result ==>
  bounded_interval64_covers_object_q result
    (bounded_object_q_delta_value_six_cv
      object0 object1 object2 object3 object4 object5)
Proof
  strip_tac
  >> drule bounded_delta64_value_six_trace
  >> strip_tac
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_neg_covers_object_q
  >> `bounded_interval64_covers_object_q first_linear
        (bounded_object_q_interval_sum_cv
          [bounded_object_q_interval_neg_cv object0;object1;object2;
           bounded_object_q_interval_neg_cv object3;object4;object5])` by
       (match_mp_tac
          (Q.INST
            [`word_values` |->
               `[bounded_interval64_neg word0;word1;word2;
                 bounded_interval64_neg word3;word4;word5]`,
             `object_values` |->
               `[bounded_object_q_interval_neg_cv object0;object1;object2;
                 bounded_object_q_interval_neg_cv object3;object4;object5]`,
             `result` |-> `first_linear`]
            compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_interval64_sum_covers_object_q)
        >> simp [LIST_REL_def])
  >> `bounded_interval64_covers_object_q second_linear
        (bounded_object_q_interval_sum_cv
          [object0;bounded_object_q_interval_neg_cv object1;object2;object3;
           bounded_object_q_interval_neg_cv object4;object5])` by
       (match_mp_tac
          (Q.INST
            [`word_values` |->
               `[word0;bounded_interval64_neg word1;word2;word3;
                 bounded_interval64_neg word4;word5]`,
             `object_values` |->
               `[object0;bounded_object_q_interval_neg_cv object1;object2;
                 object3;bounded_object_q_interval_neg_cv object4;object5]`,
             `result` |-> `second_linear`]
            compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_interval64_sum_covers_object_q)
        >> simp [LIST_REL_def])
  >> `bounded_interval64_covers_object_q third_linear
        (bounded_object_q_interval_sum_cv
          [object0;object1;bounded_object_q_interval_neg_cv object2;object3;
           object4;bounded_object_q_interval_neg_cv object5])` by
       (match_mp_tac
          (Q.INST
            [`word_values` |->
               `[word0;word1;bounded_interval64_neg word2;word3;word4;
                 bounded_interval64_neg word5]`,
             `object_values` |->
               `[object0;object1;bounded_object_q_interval_neg_cv object2;
                 object3;object4;bounded_object_q_interval_neg_cv object5]`,
             `result` |-> `third_linear`]
            compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_interval64_sum_covers_object_q)
        >> simp [LIST_REL_def])
  >> imp_res_tac
       compute_boundedAnalyticObjectDeltaProductRefinementTheory.bounded_interval64_mul3_covers_object_q
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_neg_covers_object_q
  >> rw [bounded_object_q_delta_value_six_cv_def]
  >> match_mp_tac
       (Q.INST
         [`word_values` |->
            `[first_product;second_product;third_product;
              bounded_interval64_neg fourth_product;
              bounded_interval64_neg fifth_product;
              bounded_interval64_neg sixth_product;
              bounded_interval64_neg seventh_product]`,
          `object_values` |->
            `[bounded_object_q_interval_mul3_cv object0 object3
                (bounded_object_q_interval_sum_cv
                  [bounded_object_q_interval_neg_cv object0;object1;object2;
                   bounded_object_q_interval_neg_cv object3;object4;object5]);
              bounded_object_q_interval_mul3_cv object1 object4
                (bounded_object_q_interval_sum_cv
                  [object0;bounded_object_q_interval_neg_cv object1;object2;
                   object3;bounded_object_q_interval_neg_cv object4;object5]);
              bounded_object_q_interval_mul3_cv object2 object5
                (bounded_object_q_interval_sum_cv
                  [object0;object1;bounded_object_q_interval_neg_cv object2;
                   object3;object4;bounded_object_q_interval_neg_cv object5]);
              bounded_object_q_interval_neg_cv
                (bounded_object_q_interval_mul3_cv object1 object2 object3);
              bounded_object_q_interval_neg_cv
                (bounded_object_q_interval_mul3_cv object0 object2 object4);
              bounded_object_q_interval_neg_cv
                (bounded_object_q_interval_mul3_cv object0 object1 object5);
              bounded_object_q_interval_neg_cv
                (bounded_object_q_interval_mul3_cv object3 object4 object5)]`,
          `result` |-> `result`]
         compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_interval64_sum_covers_object_q)
  >> simp [LIST_REL_def]
QED

val _ = export_theory ();
