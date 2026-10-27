(*****************************************************************************
 * Exact-rational refinement of the fixed-scale arctangent word kernel.
 *
 * The real alternating-polynomial enclosure is proved separately.  This
 * theory connects the executable Horner calculation to exact rational
 * coefficients through the existing generic interval add/product contract.
 *****************************************************************************)
Theory compute_boundedAtanWordRefinement
Ancestors
  compute_boundedAtanRealRefinement
  compute_boundedAnalyticObjectProductRefinement
Libs
  bossLib preamble

Theorem bounded_atan_pos_third_covers_object_q:
  bounded_interval64_covers_object_q bounded_atan_pos_third
    (bounded_analytic_source_q_interval_cv 1 0 2)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_atan_neg_third_covers_object_q:
  bounded_interval64_covers_object_q bounded_atan_neg_third
    (bounded_analytic_source_q_interval_cv 0 1 2)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_atan_pos_fifth_covers_object_q:
  bounded_interval64_covers_object_q bounded_atan_pos_fifth
    (bounded_analytic_source_q_interval_cv 1 0 4)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_atan_neg_seventh_covers_object_q:
  bounded_interval64_covers_object_q bounded_atan_neg_seventh
    (bounded_analytic_source_q_interval_cv 0 1 6)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_atan_pos_ninth_covers_object_q:
  bounded_interval64_covers_object_q bounded_atan_pos_ninth
    (bounded_analytic_source_q_interval_cv 1 0 8)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_atan_neg_eleventh_covers_object_q:
  bounded_interval64_covers_object_q bounded_atan_neg_eleventh
    (bounded_analytic_source_q_interval_cv 0 1 10)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_atan_pos_thirteenth_covers_object_q:
  bounded_interval64_covers_object_q bounded_atan_pos_thirteenth
    (bounded_analytic_source_q_interval_cv 1 0 12)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_interval64_mul_add_covers_object_q:
  bounded_interval64_covers_object_q scalar object_scalar /\
  bounded_interval64_covers_object_q accumulator object_accumulator /\
  bounded_interval64_covers_object_q addend object_addend /\
  bounded_interval64_mul_add scalar accumulator addend = SOME result ==>
  bounded_interval64_covers_object_q result
    (bounded_object_q_interval_add_cv object_addend
      (bounded_object_q_interval_mul_cv object_scalar object_accumulator))
Proof
  rw [compute_boundedAtanTheory.bounded_interval64_mul_add_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_add_covers_object_q
QED

Definition bounded_atan_object_q_square_def:
  bounded_atan_object_q_square point =
    bounded_object_q_interval_mul_cv point point
End

Definition bounded_atan_pos_lower_step9_object_q_def:
  bounded_atan_pos_lower_step9_object_q point =
    bounded_object_q_interval_add_cv
      (bounded_analytic_source_q_interval_cv 1 0 8)
      (bounded_object_q_interval_mul_cv
        (bounded_atan_object_q_square point)
        (bounded_analytic_source_q_interval_cv 0 1 10))
End

Definition bounded_atan_pos_lower_step7_object_q_def:
  bounded_atan_pos_lower_step7_object_q point =
    bounded_object_q_interval_add_cv
      (bounded_analytic_source_q_interval_cv 0 1 6)
      (bounded_object_q_interval_mul_cv
        (bounded_atan_object_q_square point)
        (bounded_atan_pos_lower_step9_object_q point))
End

Definition bounded_atan_pos_lower_step5_object_q_def:
  bounded_atan_pos_lower_step5_object_q point =
    bounded_object_q_interval_add_cv
      (bounded_analytic_source_q_interval_cv 1 0 4)
      (bounded_object_q_interval_mul_cv
        (bounded_atan_object_q_square point)
        (bounded_atan_pos_lower_step7_object_q point))
End

Definition bounded_atan_pos_lower_step3_object_q_def:
  bounded_atan_pos_lower_step3_object_q point =
    bounded_object_q_interval_add_cv
      (bounded_analytic_source_q_interval_cv 0 1 2)
      (bounded_object_q_interval_mul_cv
        (bounded_atan_object_q_square point)
        (bounded_atan_pos_lower_step5_object_q point))
End

Definition bounded_atan_pos_lower_body_object_q_def:
  bounded_atan_pos_lower_body_object_q point =
    bounded_object_q_interval_add_cv
      (bounded_analytic_source_q_interval_cv 1 0 0)
      (bounded_object_q_interval_mul_cv
        (bounded_atan_object_q_square point)
        (bounded_atan_pos_lower_step3_object_q point))
End

Definition bounded_atan_pos_lower_object_q_def:
  bounded_atan_pos_lower_object_q point =
    bounded_object_q_interval_mul_cv point
      (bounded_atan_pos_lower_body_object_q point)
End

Theorem bounded_interval64_atan_pos_lower_covers_object_q:
  bounded_interval64_covers_object_q
      (BoundedInterval64
        (BoundedSigned64 F magnitude) (BoundedSigned64 F magnitude))
      object_point /\
  bounded_interval64_atan_pos_lower magnitude = SOME result ==>
  bounded_interval64_covers_object_q result
    (bounded_atan_pos_lower_object_q object_point)
Proof
  strip_tac
  >> fs [compute_boundedAtanTheory.bounded_interval64_atan_pos_lower_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded_interval64_mul
          (BoundedInterval64 (BoundedSigned64 F magnitude)
            (BoundedSigned64 F magnitude))
          (BoundedInterval64 (BoundedSigned64 F magnitude)
            (BoundedSigned64 F magnitude)) = SOME square`
  >> rename1
       `bounded_interval64_mul_add square bounded_atan_neg_eleventh
          bounded_atan_pos_ninth = SOME step9`
  >> rename1
       `bounded_interval64_mul_add square step9 bounded_atan_neg_seventh =
          SOME step7`
  >> rename1
       `bounded_interval64_mul_add square step7 bounded_atan_pos_fifth =
          SOME step5`
  >> rename1
       `bounded_interval64_mul_add square step5 bounded_atan_neg_third =
          SOME step3`
  >> rename1
       `bounded_interval64_mul_add square step3 bounded_atan_one =
          SOME body`
  >> `bounded_interval64_covers_object_q square
        (bounded_atan_object_q_square object_point)` by
       (mp_tac
          (Q.INST
            [`left` |->
               `BoundedInterval64
                  (BoundedSigned64 F magnitude)
                  (BoundedSigned64 F magnitude)`,
             `left_object_interval` |-> `object_point`,
             `right` |->
               `BoundedInterval64
                  (BoundedSigned64 F magnitude)
                  (BoundedSigned64 F magnitude)`,
             `right_object_interval` |-> `object_point`,
             `result` |-> `square`]
            compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q)
        >> asm_rewrite_tac [bounded_atan_object_q_square_def])
  >> `bounded_interval64_covers_object_q step9
        (bounded_atan_pos_lower_step9_object_q object_point)` by
       (mp_tac
          (Q.INST
            [`scalar` |-> `square`,
             `object_scalar` |->
               `bounded_atan_object_q_square object_point`,
             `accumulator` |-> `bounded_atan_neg_eleventh`,
             `object_accumulator` |->
               `bounded_analytic_source_q_interval_cv 0 1 10`,
             `addend` |-> `bounded_atan_pos_ninth`,
             `object_addend` |->
               `bounded_analytic_source_q_interval_cv 1 0 8`,
             `result` |-> `step9`]
            bounded_interval64_mul_add_covers_object_q)
        >> asm_rewrite_tac
             [bounded_atan_pos_lower_step9_object_q_def,
              bounded_atan_neg_eleventh_covers_object_q,
              bounded_atan_pos_ninth_covers_object_q])
  >> `bounded_interval64_covers_object_q step7
        (bounded_atan_pos_lower_step7_object_q object_point)` by
       (mp_tac
          (Q.INST
            [`scalar` |-> `square`,
             `object_scalar` |->
               `bounded_atan_object_q_square object_point`,
             `accumulator` |-> `step9`,
             `object_accumulator` |->
               `bounded_atan_pos_lower_step9_object_q object_point`,
             `addend` |-> `bounded_atan_neg_seventh`,
             `object_addend` |->
               `bounded_analytic_source_q_interval_cv 0 1 6`,
             `result` |-> `step7`]
            bounded_interval64_mul_add_covers_object_q)
        >> asm_rewrite_tac
             [bounded_atan_pos_lower_step7_object_q_def,
              bounded_atan_neg_seventh_covers_object_q])
  >> `bounded_interval64_covers_object_q step5
        (bounded_atan_pos_lower_step5_object_q object_point)` by
       (mp_tac
          (Q.INST
            [`scalar` |-> `square`,
             `object_scalar` |->
               `bounded_atan_object_q_square object_point`,
             `accumulator` |-> `step7`,
             `object_accumulator` |->
               `bounded_atan_pos_lower_step7_object_q object_point`,
             `addend` |-> `bounded_atan_pos_fifth`,
             `object_addend` |->
               `bounded_analytic_source_q_interval_cv 1 0 4`,
             `result` |-> `step5`]
            bounded_interval64_mul_add_covers_object_q)
        >> asm_rewrite_tac
             [bounded_atan_pos_lower_step5_object_q_def,
              bounded_atan_pos_fifth_covers_object_q])
  >> `bounded_interval64_covers_object_q step3
        (bounded_atan_pos_lower_step3_object_q object_point)` by
       (mp_tac
          (Q.INST
            [`scalar` |-> `square`,
             `object_scalar` |->
               `bounded_atan_object_q_square object_point`,
             `accumulator` |-> `step5`,
             `object_accumulator` |->
               `bounded_atan_pos_lower_step5_object_q object_point`,
             `addend` |-> `bounded_atan_neg_third`,
             `object_addend` |->
               `bounded_analytic_source_q_interval_cv 0 1 2`,
             `result` |-> `step3`]
            bounded_interval64_mul_add_covers_object_q)
        >> asm_rewrite_tac
             [bounded_atan_pos_lower_step3_object_q_def,
              bounded_atan_neg_third_covers_object_q])
  >> `bounded_interval64_covers_object_q body
        (bounded_atan_pos_lower_body_object_q object_point)` by
       (mp_tac
          (Q.INST
            [`scalar` |-> `square`,
             `object_scalar` |->
               `bounded_atan_object_q_square object_point`,
             `accumulator` |-> `step3`,
             `object_accumulator` |->
               `bounded_atan_pos_lower_step3_object_q object_point`,
             `addend` |-> `bounded_atan_one`,
             `object_addend` |->
               `bounded_analytic_source_q_interval_cv 1 0 0`,
             `result` |-> `body`]
            bounded_interval64_mul_add_covers_object_q)
        >> asm_rewrite_tac
             [bounded_atan_pos_lower_body_object_q_def,
              compute_boundedAnalyticObjectRefinementTheory.bounded_atan_one_covers_object_q_one])
  >> mp_tac
       (Q.INST
         [`left` |->
            `BoundedInterval64
               (BoundedSigned64 F magnitude)
               (BoundedSigned64 F magnitude)`,
          `left_object_interval` |-> `object_point`,
          `right` |-> `body`,
          `right_object_interval` |->
            `bounded_atan_pos_lower_body_object_q object_point`,
          `result` |-> `result`]
         compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q)
  >> asm_rewrite_tac [bounded_atan_pos_lower_object_q_def]
QED

Definition bounded_atan_pos_upper_step11_object_q_def:
  bounded_atan_pos_upper_step11_object_q point =
    bounded_object_q_interval_add_cv
      (bounded_analytic_source_q_interval_cv 0 1 10)
      (bounded_object_q_interval_mul_cv
        (bounded_atan_object_q_square point)
        (bounded_analytic_source_q_interval_cv 1 0 12))
End

Definition bounded_atan_pos_upper_step9_object_q_def:
  bounded_atan_pos_upper_step9_object_q point =
    bounded_object_q_interval_add_cv
      (bounded_analytic_source_q_interval_cv 1 0 8)
      (bounded_object_q_interval_mul_cv
        (bounded_atan_object_q_square point)
        (bounded_atan_pos_upper_step11_object_q point))
End

Definition bounded_atan_pos_upper_step7_object_q_def:
  bounded_atan_pos_upper_step7_object_q point =
    bounded_object_q_interval_add_cv
      (bounded_analytic_source_q_interval_cv 0 1 6)
      (bounded_object_q_interval_mul_cv
        (bounded_atan_object_q_square point)
        (bounded_atan_pos_upper_step9_object_q point))
End

Definition bounded_atan_pos_upper_step5_object_q_def:
  bounded_atan_pos_upper_step5_object_q point =
    bounded_object_q_interval_add_cv
      (bounded_analytic_source_q_interval_cv 1 0 4)
      (bounded_object_q_interval_mul_cv
        (bounded_atan_object_q_square point)
        (bounded_atan_pos_upper_step7_object_q point))
End

Definition bounded_atan_pos_upper_step3_object_q_def:
  bounded_atan_pos_upper_step3_object_q point =
    bounded_object_q_interval_add_cv
      (bounded_analytic_source_q_interval_cv 0 1 2)
      (bounded_object_q_interval_mul_cv
        (bounded_atan_object_q_square point)
        (bounded_atan_pos_upper_step5_object_q point))
End

Definition bounded_atan_pos_upper_body_object_q_def:
  bounded_atan_pos_upper_body_object_q point =
    bounded_object_q_interval_add_cv
      (bounded_analytic_source_q_interval_cv 1 0 0)
      (bounded_object_q_interval_mul_cv
        (bounded_atan_object_q_square point)
        (bounded_atan_pos_upper_step3_object_q point))
End

Definition bounded_atan_pos_upper_object_q_def:
  bounded_atan_pos_upper_object_q point =
    bounded_object_q_interval_mul_cv point
      (bounded_atan_pos_upper_body_object_q point)
End

Theorem bounded_interval64_atan_pos_upper_covers_object_q:
  bounded_interval64_covers_object_q
      (BoundedInterval64
        (BoundedSigned64 F magnitude) (BoundedSigned64 F magnitude))
      object_point /\
  bounded_interval64_atan_pos_upper magnitude = SOME result ==>
  bounded_interval64_covers_object_q result
    (bounded_atan_pos_upper_object_q object_point)
Proof
  strip_tac
  >> fs [compute_boundedAtanTheory.bounded_interval64_atan_pos_upper_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded_interval64_mul
          (BoundedInterval64 (BoundedSigned64 F magnitude)
            (BoundedSigned64 F magnitude))
          (BoundedInterval64 (BoundedSigned64 F magnitude)
            (BoundedSigned64 F magnitude)) = SOME square`
  >> rename1
       `bounded_interval64_mul_add square bounded_atan_pos_thirteenth
          bounded_atan_neg_eleventh = SOME step11`
  >> rename1
       `bounded_interval64_mul_add square step11 bounded_atan_pos_ninth =
          SOME step9`
  >> rename1
       `bounded_interval64_mul_add square step9 bounded_atan_neg_seventh =
          SOME step7`
  >> rename1
       `bounded_interval64_mul_add square step7 bounded_atan_pos_fifth =
          SOME step5`
  >> rename1
       `bounded_interval64_mul_add square step5 bounded_atan_neg_third =
          SOME step3`
  >> rename1
       `bounded_interval64_mul_add square step3 bounded_atan_one =
          SOME body`
  >> `bounded_interval64_covers_object_q square
        (bounded_atan_object_q_square object_point)` by
       (mp_tac
          (Q.INST
            [`left` |->
               `BoundedInterval64
                  (BoundedSigned64 F magnitude)
                  (BoundedSigned64 F magnitude)`,
             `left_object_interval` |-> `object_point`,
             `right` |->
               `BoundedInterval64
                  (BoundedSigned64 F magnitude)
                  (BoundedSigned64 F magnitude)`,
             `right_object_interval` |-> `object_point`,
             `result` |-> `square`]
            compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q)
        >> asm_rewrite_tac [bounded_atan_object_q_square_def])
  >> `bounded_interval64_covers_object_q step11
        (bounded_atan_pos_upper_step11_object_q object_point)` by
       (mp_tac
          (Q.INST
            [`scalar` |-> `square`,
             `object_scalar` |->
               `bounded_atan_object_q_square object_point`,
             `accumulator` |-> `bounded_atan_pos_thirteenth`,
             `object_accumulator` |->
               `bounded_analytic_source_q_interval_cv 1 0 12`,
             `addend` |-> `bounded_atan_neg_eleventh`,
             `object_addend` |->
               `bounded_analytic_source_q_interval_cv 0 1 10`,
             `result` |-> `step11`]
            bounded_interval64_mul_add_covers_object_q)
        >> asm_rewrite_tac
             [bounded_atan_pos_upper_step11_object_q_def,
              bounded_atan_pos_thirteenth_covers_object_q,
              bounded_atan_neg_eleventh_covers_object_q])
  >> `bounded_interval64_covers_object_q step9
        (bounded_atan_pos_upper_step9_object_q object_point)` by
       (mp_tac
          (Q.INST
            [`scalar` |-> `square`,
             `object_scalar` |->
               `bounded_atan_object_q_square object_point`,
             `accumulator` |-> `step11`,
             `object_accumulator` |->
               `bounded_atan_pos_upper_step11_object_q object_point`,
             `addend` |-> `bounded_atan_pos_ninth`,
             `object_addend` |->
               `bounded_analytic_source_q_interval_cv 1 0 8`,
             `result` |-> `step9`]
            bounded_interval64_mul_add_covers_object_q)
        >> asm_rewrite_tac
             [bounded_atan_pos_upper_step9_object_q_def,
              bounded_atan_pos_ninth_covers_object_q])
  >> `bounded_interval64_covers_object_q step7
        (bounded_atan_pos_upper_step7_object_q object_point)` by
       (mp_tac
          (Q.INST
            [`scalar` |-> `square`,
             `object_scalar` |->
               `bounded_atan_object_q_square object_point`,
             `accumulator` |-> `step9`,
             `object_accumulator` |->
               `bounded_atan_pos_upper_step9_object_q object_point`,
             `addend` |-> `bounded_atan_neg_seventh`,
             `object_addend` |->
               `bounded_analytic_source_q_interval_cv 0 1 6`,
             `result` |-> `step7`]
            bounded_interval64_mul_add_covers_object_q)
        >> asm_rewrite_tac
             [bounded_atan_pos_upper_step7_object_q_def,
              bounded_atan_neg_seventh_covers_object_q])
  >> `bounded_interval64_covers_object_q step5
        (bounded_atan_pos_upper_step5_object_q object_point)` by
       (mp_tac
          (Q.INST
            [`scalar` |-> `square`,
             `object_scalar` |->
               `bounded_atan_object_q_square object_point`,
             `accumulator` |-> `step7`,
             `object_accumulator` |->
               `bounded_atan_pos_upper_step7_object_q object_point`,
             `addend` |-> `bounded_atan_pos_fifth`,
             `object_addend` |->
               `bounded_analytic_source_q_interval_cv 1 0 4`,
             `result` |-> `step5`]
            bounded_interval64_mul_add_covers_object_q)
        >> asm_rewrite_tac
             [bounded_atan_pos_upper_step5_object_q_def,
              bounded_atan_pos_fifth_covers_object_q])
  >> `bounded_interval64_covers_object_q step3
        (bounded_atan_pos_upper_step3_object_q object_point)` by
       (mp_tac
          (Q.INST
            [`scalar` |-> `square`,
             `object_scalar` |->
               `bounded_atan_object_q_square object_point`,
             `accumulator` |-> `step5`,
             `object_accumulator` |->
               `bounded_atan_pos_upper_step5_object_q object_point`,
             `addend` |-> `bounded_atan_neg_third`,
             `object_addend` |->
               `bounded_analytic_source_q_interval_cv 0 1 2`,
             `result` |-> `step3`]
            bounded_interval64_mul_add_covers_object_q)
        >> asm_rewrite_tac
             [bounded_atan_pos_upper_step3_object_q_def,
              bounded_atan_neg_third_covers_object_q])
  >> `bounded_interval64_covers_object_q body
        (bounded_atan_pos_upper_body_object_q object_point)` by
       (mp_tac
          (Q.INST
            [`scalar` |-> `square`,
             `object_scalar` |->
               `bounded_atan_object_q_square object_point`,
             `accumulator` |-> `step3`,
             `object_accumulator` |->
               `bounded_atan_pos_upper_step3_object_q object_point`,
             `addend` |-> `bounded_atan_one`,
             `object_addend` |->
               `bounded_analytic_source_q_interval_cv 1 0 0`,
             `result` |-> `body`]
            bounded_interval64_mul_add_covers_object_q)
        >> asm_rewrite_tac
             [bounded_atan_pos_upper_body_object_q_def,
              compute_boundedAnalyticObjectRefinementTheory.bounded_atan_one_covers_object_q_one])
  >> mp_tac
       (Q.INST
         [`left` |->
            `BoundedInterval64
               (BoundedSigned64 F magnitude)
               (BoundedSigned64 F magnitude)`,
          `left_object_interval` |-> `object_point`,
          `right` |-> `body`,
          `right_object_interval` |->
            `bounded_atan_pos_upper_body_object_q object_point`,
          `result` |-> `result`]
         compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q)
  >> asm_rewrite_tac [bounded_atan_pos_upper_object_q_def]
QED

val _ = export_theory ();
