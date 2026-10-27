(*****************************************************************************
 * Real-range refinement for the fixed-scale arctangent kernel.
 *****************************************************************************)
Theory compute_boundedAtanRangeRefinement
Ancestors
  compute_boundedAtanWordRefinement compute_boundedWordRealRefinement
  compute_boundedAtanPiRefinement
  compute_boundedAnalyticObjectCertificateRefinement
  compute_boundedAnalyticObjectInverseOperationRefinement
Libs
  bossLib preamble realLib RealField

open realTheory compute_boundedObjectQRealRefinementTheory

Definition bounded_atan_lower_step9_real_def:
  bounded_atan_lower_step9_real (x:real) =
    &1 / &9 + (x * x) * (-(&1) / &11)
End

Definition bounded_atan_lower_step7_real_def:
  bounded_atan_lower_step7_real (x:real) =
    -(&1) / &7 + (x * x) * bounded_atan_lower_step9_real x
End

Definition bounded_atan_lower_step5_real_def:
  bounded_atan_lower_step5_real (x:real) =
    &1 / &5 + (x * x) * bounded_atan_lower_step7_real x
End

Definition bounded_atan_lower_step3_real_def:
  bounded_atan_lower_step3_real (x:real) =
    -(&1) / &3 + (x * x) * bounded_atan_lower_step5_real x
End

Definition bounded_atan_lower_body_real_def:
  bounded_atan_lower_body_real (x:real) =
    &1 + (x * x) * bounded_atan_lower_step3_real x
End

Definition bounded_atan_upper_step11_real_def:
  bounded_atan_upper_step11_real (x:real) =
    -(&1) / &11 + (x * x) * (&1 / &13)
End

Definition bounded_atan_upper_step9_real_def:
  bounded_atan_upper_step9_real (x:real) =
    &1 / &9 + (x * x) * bounded_atan_upper_step11_real x
End

Definition bounded_atan_upper_step7_real_def:
  bounded_atan_upper_step7_real (x:real) =
    -(&1) / &7 + (x * x) * bounded_atan_upper_step9_real x
End

Definition bounded_atan_upper_step5_real_def:
  bounded_atan_upper_step5_real (x:real) =
    &1 / &5 + (x * x) * bounded_atan_upper_step7_real x
End

Definition bounded_atan_upper_step3_real_def:
  bounded_atan_upper_step3_real (x:real) =
    -(&1) / &3 + (x * x) * bounded_atan_upper_step5_real x
End

Definition bounded_atan_upper_body_real_def:
  bounded_atan_upper_body_real (x:real) =
    &1 + (x * x) * bounded_atan_upper_step3_real x
End

Definition bounded_atan_magnitude_interval_def:
  bounded_atan_magnitude_interval magnitude =
    BoundedInterval64 (BoundedSigned64 F magnitude)
      (BoundedSigned64 F magnitude)
End

Definition bounded_atan_magnitude_object_q_def:
  bounded_atan_magnitude_object_q magnitude =
    bounded_interval64_object_q_cv
      (bounded_atan_magnitude_interval magnitude)
End

Definition bounded_atan_magnitude_real_def:
  bounded_atan_magnitude_real magnitude =
    bounded_signed64_real (BoundedSigned64 F magnitude)
End

Theorem bounded_atan_magnitude_interval_valid:
  bounded_interval64_valid (bounded_atan_magnitude_interval magnitude)
Proof
  simp [bounded_atan_magnitude_interval_def,
        compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
QED

Theorem bounded_atan_magnitude_interval_covers_object_q:
  bounded_interval64_covers_object_q
    (bounded_atan_magnitude_interval magnitude)
    (bounded_atan_magnitude_object_q magnitude)
Proof
  rw [bounded_atan_magnitude_object_q_def]
  >> irule
       compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_covers_own_object_q
  >> MATCH_ACCEPT_TAC bounded_atan_magnitude_interval_valid
QED

Theorem bounded_atan_magnitude_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_magnitude_object_q magnitude)
    (bounded_atan_magnitude_real magnitude)
Proof
  simp [bounded_object_q_interval_represents_real_singleton_def,
        bounded_object_q_represents_real_def,
        bounded_atan_magnitude_object_q_def,
        bounded_atan_magnitude_interval_def,
        bounded_atan_magnitude_real_def,
        bounded_signed64_real_def, bounded_word_scale_real_def,
        bounded_int_fraction_real_def,
        compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_object_q_cv_def,
        compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_signed64_object_q_cv_decodes,
        compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def]
QED

Theorem bounded_atan_source_one_represents_real:
  bounded_object_q_interval_represents_real_singleton
    (bounded_analytic_source_q_interval_cv 1 0 0) (&1)
Proof
  mp_tac
    (Q.INST
      [`positive` |-> `1`, `negative` |-> `0`,
       `denominator_predecessor` |-> `0`]
      bounded_analytic_source_q_interval_cv_represents_real_singleton)
  >> simp [bounded_int_fraction_real_def]
QED

Theorem bounded_atan_source_neg_third_represents_real:
  bounded_object_q_interval_represents_real_singleton
    (bounded_analytic_source_q_interval_cv 0 1 2) (-(&1) / &3)
Proof
  mp_tac
    (Q.INST
      [`positive` |-> `0`, `negative` |-> `1`,
       `denominator_predecessor` |-> `2`]
      bounded_analytic_source_q_interval_cv_represents_real_singleton)
  >> simp [bounded_int_fraction_real_def]
QED

Theorem bounded_atan_source_pos_fifth_represents_real:
  bounded_object_q_interval_represents_real_singleton
    (bounded_analytic_source_q_interval_cv 1 0 4) (&1 / &5)
Proof
  mp_tac
    (Q.INST
      [`positive` |-> `1`, `negative` |-> `0`,
       `denominator_predecessor` |-> `4`]
      bounded_analytic_source_q_interval_cv_represents_real_singleton)
  >> simp [bounded_int_fraction_real_def]
QED

Theorem bounded_atan_source_neg_seventh_represents_real:
  bounded_object_q_interval_represents_real_singleton
    (bounded_analytic_source_q_interval_cv 0 1 6) (-(&1) / &7)
Proof
  mp_tac
    (Q.INST
      [`positive` |-> `0`, `negative` |-> `1`,
       `denominator_predecessor` |-> `6`]
      bounded_analytic_source_q_interval_cv_represents_real_singleton)
  >> simp [bounded_int_fraction_real_def]
QED

Theorem bounded_atan_source_pos_ninth_represents_real:
  bounded_object_q_interval_represents_real_singleton
    (bounded_analytic_source_q_interval_cv 1 0 8) (&1 / &9)
Proof
  mp_tac
    (Q.INST
      [`positive` |-> `1`, `negative` |-> `0`,
       `denominator_predecessor` |-> `8`]
      bounded_analytic_source_q_interval_cv_represents_real_singleton)
  >> simp [bounded_int_fraction_real_def]
QED

Theorem bounded_atan_source_neg_eleventh_represents_real:
  bounded_object_q_interval_represents_real_singleton
    (bounded_analytic_source_q_interval_cv 0 1 10) (-(&1) / &11)
Proof
  mp_tac
    (Q.INST
      [`positive` |-> `0`, `negative` |-> `1`,
       `denominator_predecessor` |-> `10`]
      bounded_analytic_source_q_interval_cv_represents_real_singleton)
  >> simp [bounded_int_fraction_real_def]
QED

Theorem bounded_atan_source_pos_thirteenth_represents_real:
  bounded_object_q_interval_represents_real_singleton
    (bounded_analytic_source_q_interval_cv 1 0 12) (&1 / &13)
Proof
  mp_tac
    (Q.INST
      [`positive` |-> `1`, `negative` |-> `0`,
       `denominator_predecessor` |-> `12`]
      bounded_analytic_source_q_interval_cv_represents_real_singleton)
  >> simp [bounded_int_fraction_real_def]
QED

Theorem bounded_atan_object_q_square_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_object_q_square point) (x * x)
Proof
  rw [bounded_atan_object_q_square_def]
  >> mp_tac
       (Q.INST
         [`left` |-> `point`, `right` |-> `point`,
          `left_value` |-> `x`, `right_value` |-> `x`]
         bounded_object_q_interval_mul_cv_represents_real_singleton)
  >> impl_tac
  >- simp []
  >> disch_then
       (fn th => MATCH_ACCEPT_TAC (REWRITE_RULE [GSYM POW_2] th))
QED

Theorem bounded_atan_object_q_interval_mul_add_represents_real:
  bounded_object_q_interval_represents_real_singleton scalar scalar_value /\
  bounded_object_q_interval_represents_real_singleton
    accumulator accumulator_value /\
  bounded_object_q_interval_represents_real_singleton addend addend_value ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_object_q_interval_add_cv addend
      (bounded_object_q_interval_mul_cv scalar accumulator))
    (addend_value + scalar_value * accumulator_value)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_object_q_interval_mul_cv scalar accumulator)
        (scalar_value * accumulator_value)` by
       (mp_tac
          (Q.INST
            [`left` |-> `scalar`, `right` |-> `accumulator`,
             `left_value` |-> `scalar_value`,
             `right_value` |-> `accumulator_value`]
            bounded_object_q_interval_mul_cv_represents_real_singleton)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`left` |-> `addend`,
          `right` |->
            `bounded_object_q_interval_mul_cv scalar accumulator`,
          `left_value` |-> `addend_value`,
          `right_value` |-> `scalar_value * accumulator_value`]
         bounded_object_q_interval_add_cv_represents_real_singleton)
  >> asm_rewrite_tac []
QED

Theorem bounded_atan_pos_lower_step9_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_pos_lower_step9_object_q point)
    (bounded_atan_lower_step9_real x)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_object_q_square point) (x * x)` by
       metis_tac [bounded_atan_object_q_square_represents_real]
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_object_q_interval_mul_cv
          (bounded_atan_object_q_square point)
          (bounded_analytic_source_q_interval_cv 0 1 10))
        ((x * x) * (-(&1) / &11))` by
       (mp_tac
          (Q.INST
            [`left` |-> `bounded_atan_object_q_square point`,
             `right` |->
               `bounded_analytic_source_q_interval_cv 0 1 10`,
             `left_value` |-> `x * x`,
             `right_value` |-> `-(&1) / &11`]
            bounded_object_q_interval_mul_cv_represents_real_singleton)
        >> asm_rewrite_tac
             [bounded_atan_source_neg_eleventh_represents_real])
  >> mp_tac
       (Q.INST
         [`left` |-> `bounded_analytic_source_q_interval_cv 1 0 8`,
          `right` |->
            `bounded_object_q_interval_mul_cv
              (bounded_atan_object_q_square point)
              (bounded_analytic_source_q_interval_cv 0 1 10)`,
          `left_value` |-> `&1 / &9`,
          `right_value` |-> `(x * x) * (-(&1) / &11)`]
         bounded_object_q_interval_add_cv_represents_real_singleton)
  >> asm_rewrite_tac
       [bounded_atan_source_pos_ninth_represents_real,
        bounded_atan_pos_lower_step9_object_q_def,
        bounded_atan_lower_step9_real_def]
QED

Theorem bounded_atan_pos_lower_step7_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_pos_lower_step7_object_q point)
    (bounded_atan_lower_step7_real x)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_object_q_square point) (x * x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_object_q_square_represents_real)
        >> asm_rewrite_tac [])
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_pos_lower_step9_object_q point)
        (bounded_atan_lower_step9_real x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_pos_lower_step9_object_q_represents_real)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`scalar` |-> `bounded_atan_object_q_square point`,
          `accumulator` |->
            `bounded_atan_pos_lower_step9_object_q point`,
          `addend` |->
            `bounded_analytic_source_q_interval_cv 0 1 6`,
          `scalar_value` |-> `x * x`,
          `accumulator_value` |-> `bounded_atan_lower_step9_real x`,
          `addend_value` |-> `-(&1) / &7`]
         bounded_atan_object_q_interval_mul_add_represents_real)
  >> asm_rewrite_tac
       [bounded_atan_source_neg_seventh_represents_real,
        bounded_atan_pos_lower_step7_object_q_def,
        bounded_atan_lower_step7_real_def]
QED

Theorem bounded_atan_pos_lower_step5_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_pos_lower_step5_object_q point)
    (bounded_atan_lower_step5_real x)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_object_q_square point) (x * x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_object_q_square_represents_real)
        >> asm_rewrite_tac [])
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_pos_lower_step7_object_q point)
        (bounded_atan_lower_step7_real x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_pos_lower_step7_object_q_represents_real)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`scalar` |-> `bounded_atan_object_q_square point`,
          `accumulator` |->
            `bounded_atan_pos_lower_step7_object_q point`,
          `addend` |->
            `bounded_analytic_source_q_interval_cv 1 0 4`,
          `scalar_value` |-> `x * x`,
          `accumulator_value` |-> `bounded_atan_lower_step7_real x`,
          `addend_value` |-> `&1 / &5`]
         bounded_atan_object_q_interval_mul_add_represents_real)
  >> asm_rewrite_tac
       [bounded_atan_source_pos_fifth_represents_real,
        bounded_atan_pos_lower_step5_object_q_def,
        bounded_atan_lower_step5_real_def]
QED

Theorem bounded_atan_pos_lower_step3_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_pos_lower_step3_object_q point)
    (bounded_atan_lower_step3_real x)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_object_q_square point) (x * x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_object_q_square_represents_real)
        >> asm_rewrite_tac [])
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_pos_lower_step5_object_q point)
        (bounded_atan_lower_step5_real x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_pos_lower_step5_object_q_represents_real)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`scalar` |-> `bounded_atan_object_q_square point`,
          `accumulator` |->
            `bounded_atan_pos_lower_step5_object_q point`,
          `addend` |->
            `bounded_analytic_source_q_interval_cv 0 1 2`,
          `scalar_value` |-> `x * x`,
          `accumulator_value` |-> `bounded_atan_lower_step5_real x`,
          `addend_value` |-> `-(&1) / &3`]
         bounded_atan_object_q_interval_mul_add_represents_real)
  >> asm_rewrite_tac
       [bounded_atan_source_neg_third_represents_real,
        bounded_atan_pos_lower_step3_object_q_def,
        bounded_atan_lower_step3_real_def]
QED

Theorem bounded_atan_pos_lower_body_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_pos_lower_body_object_q point)
    (bounded_atan_lower_body_real x)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_object_q_square point) (x * x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_object_q_square_represents_real)
        >> asm_rewrite_tac [])
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_pos_lower_step3_object_q point)
        (bounded_atan_lower_step3_real x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_pos_lower_step3_object_q_represents_real)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`scalar` |-> `bounded_atan_object_q_square point`,
          `accumulator` |->
            `bounded_atan_pos_lower_step3_object_q point`,
          `addend` |->
            `bounded_analytic_source_q_interval_cv 1 0 0`,
          `scalar_value` |-> `x * x`,
          `accumulator_value` |-> `bounded_atan_lower_step3_real x`,
          `addend_value` |-> `&1`]
         bounded_atan_object_q_interval_mul_add_represents_real)
  >> asm_rewrite_tac
       [bounded_atan_source_one_represents_real,
        bounded_atan_pos_lower_body_object_q_def,
        bounded_atan_lower_body_real_def]
QED

Theorem bounded_atan_lower_horner_real_identity:
  x * bounded_atan_lower_body_real x = bounded_atan_lower_real x
Proof
  rw [bounded_atan_lower_body_real_def,
      bounded_atan_lower_step3_real_def,
      bounded_atan_lower_step5_real_def,
      bounded_atan_lower_step7_real_def,
      bounded_atan_lower_step9_real_def,
      compute_boundedAtanRealRefinementTheory.bounded_atan_lower_real_def]
  >> REAL_FIELD_TAC
QED

Theorem bounded_atan_pos_lower_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_pos_lower_object_q point)
    (bounded_atan_lower_real x)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_pos_lower_body_object_q point)
        (bounded_atan_lower_body_real x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_pos_lower_body_object_q_represents_real)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`left` |-> `point`,
          `right` |-> `bounded_atan_pos_lower_body_object_q point`,
          `left_value` |-> `x`,
          `right_value` |-> `bounded_atan_lower_body_real x`]
         bounded_object_q_interval_mul_cv_represents_real_singleton)
  >> asm_rewrite_tac
       [bounded_atan_pos_lower_object_q_def,
        bounded_atan_lower_horner_real_identity]
QED

Theorem bounded_atan_pos_upper_step11_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_pos_upper_step11_object_q point)
    (bounded_atan_upper_step11_real x)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_object_q_square point) (x * x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_object_q_square_represents_real)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`scalar` |-> `bounded_atan_object_q_square point`,
          `accumulator` |->
            `bounded_analytic_source_q_interval_cv 1 0 12`,
          `addend` |->
            `bounded_analytic_source_q_interval_cv 0 1 10`,
          `scalar_value` |-> `x * x`,
          `accumulator_value` |-> `&1 / &13`,
          `addend_value` |-> `-(&1) / &11`]
         bounded_atan_object_q_interval_mul_add_represents_real)
  >> asm_rewrite_tac
       [bounded_atan_source_pos_thirteenth_represents_real,
        bounded_atan_source_neg_eleventh_represents_real,
        bounded_atan_pos_upper_step11_object_q_def,
        bounded_atan_upper_step11_real_def]
QED

Theorem bounded_atan_pos_upper_step9_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_pos_upper_step9_object_q point)
    (bounded_atan_upper_step9_real x)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_object_q_square point) (x * x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_object_q_square_represents_real)
        >> asm_rewrite_tac [])
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_pos_upper_step11_object_q point)
        (bounded_atan_upper_step11_real x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_pos_upper_step11_object_q_represents_real)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`scalar` |-> `bounded_atan_object_q_square point`,
          `accumulator` |->
            `bounded_atan_pos_upper_step11_object_q point`,
          `addend` |->
            `bounded_analytic_source_q_interval_cv 1 0 8`,
          `scalar_value` |-> `x * x`,
          `accumulator_value` |-> `bounded_atan_upper_step11_real x`,
          `addend_value` |-> `&1 / &9`]
         bounded_atan_object_q_interval_mul_add_represents_real)
  >> asm_rewrite_tac
       [bounded_atan_source_pos_ninth_represents_real,
        bounded_atan_pos_upper_step9_object_q_def,
        bounded_atan_upper_step9_real_def]
QED

Theorem bounded_atan_pos_upper_step7_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_pos_upper_step7_object_q point)
    (bounded_atan_upper_step7_real x)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_object_q_square point) (x * x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_object_q_square_represents_real)
        >> asm_rewrite_tac [])
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_pos_upper_step9_object_q point)
        (bounded_atan_upper_step9_real x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_pos_upper_step9_object_q_represents_real)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`scalar` |-> `bounded_atan_object_q_square point`,
          `accumulator` |->
            `bounded_atan_pos_upper_step9_object_q point`,
          `addend` |->
            `bounded_analytic_source_q_interval_cv 0 1 6`,
          `scalar_value` |-> `x * x`,
          `accumulator_value` |-> `bounded_atan_upper_step9_real x`,
          `addend_value` |-> `-(&1) / &7`]
         bounded_atan_object_q_interval_mul_add_represents_real)
  >> asm_rewrite_tac
       [bounded_atan_source_neg_seventh_represents_real,
        bounded_atan_pos_upper_step7_object_q_def,
        bounded_atan_upper_step7_real_def]
QED

Theorem bounded_atan_pos_upper_step5_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_pos_upper_step5_object_q point)
    (bounded_atan_upper_step5_real x)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_object_q_square point) (x * x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_object_q_square_represents_real)
        >> asm_rewrite_tac [])
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_pos_upper_step7_object_q point)
        (bounded_atan_upper_step7_real x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_pos_upper_step7_object_q_represents_real)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`scalar` |-> `bounded_atan_object_q_square point`,
          `accumulator` |->
            `bounded_atan_pos_upper_step7_object_q point`,
          `addend` |->
            `bounded_analytic_source_q_interval_cv 1 0 4`,
          `scalar_value` |-> `x * x`,
          `accumulator_value` |-> `bounded_atan_upper_step7_real x`,
          `addend_value` |-> `&1 / &5`]
         bounded_atan_object_q_interval_mul_add_represents_real)
  >> asm_rewrite_tac
       [bounded_atan_source_pos_fifth_represents_real,
        bounded_atan_pos_upper_step5_object_q_def,
        bounded_atan_upper_step5_real_def]
QED

Theorem bounded_atan_pos_upper_step3_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_pos_upper_step3_object_q point)
    (bounded_atan_upper_step3_real x)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_object_q_square point) (x * x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_object_q_square_represents_real)
        >> asm_rewrite_tac [])
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_pos_upper_step5_object_q point)
        (bounded_atan_upper_step5_real x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_pos_upper_step5_object_q_represents_real)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`scalar` |-> `bounded_atan_object_q_square point`,
          `accumulator` |->
            `bounded_atan_pos_upper_step5_object_q point`,
          `addend` |->
            `bounded_analytic_source_q_interval_cv 0 1 2`,
          `scalar_value` |-> `x * x`,
          `accumulator_value` |-> `bounded_atan_upper_step5_real x`,
          `addend_value` |-> `-(&1) / &3`]
         bounded_atan_object_q_interval_mul_add_represents_real)
  >> asm_rewrite_tac
       [bounded_atan_source_neg_third_represents_real,
        bounded_atan_pos_upper_step3_object_q_def,
        bounded_atan_upper_step3_real_def]
QED

Theorem bounded_atan_pos_upper_body_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_pos_upper_body_object_q point)
    (bounded_atan_upper_body_real x)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_object_q_square point) (x * x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_object_q_square_represents_real)
        >> asm_rewrite_tac [])
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_pos_upper_step3_object_q point)
        (bounded_atan_upper_step3_real x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_pos_upper_step3_object_q_represents_real)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`scalar` |-> `bounded_atan_object_q_square point`,
          `accumulator` |->
            `bounded_atan_pos_upper_step3_object_q point`,
          `addend` |->
            `bounded_analytic_source_q_interval_cv 1 0 0`,
          `scalar_value` |-> `x * x`,
          `accumulator_value` |-> `bounded_atan_upper_step3_real x`,
          `addend_value` |-> `&1`]
         bounded_atan_object_q_interval_mul_add_represents_real)
  >> asm_rewrite_tac
       [bounded_atan_source_one_represents_real,
        bounded_atan_pos_upper_body_object_q_def,
        bounded_atan_upper_body_real_def]
QED

Theorem bounded_atan_upper_horner_real_identity:
  x * bounded_atan_upper_body_real x = bounded_atan_upper_real x
Proof
  rw [bounded_atan_upper_body_real_def,
      bounded_atan_upper_step3_real_def,
      bounded_atan_upper_step5_real_def,
      bounded_atan_upper_step7_real_def,
      bounded_atan_upper_step9_real_def,
      bounded_atan_upper_step11_real_def,
      compute_boundedAtanRealRefinementTheory.bounded_atan_upper_real_def,
      compute_boundedAtanRealRefinementTheory.bounded_atan_lower_real_def]
  >> REAL_FIELD_TAC
QED

Theorem bounded_atan_pos_upper_object_q_represents_real:
  bounded_object_q_interval_represents_real_singleton point x ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_atan_pos_upper_object_q point)
    (bounded_atan_upper_real x)
Proof
  strip_tac
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_pos_upper_body_object_q point)
        (bounded_atan_upper_body_real x)` by
       (mp_tac
          (Q.INST [`point` |-> `point`, `x` |-> `x`]
            bounded_atan_pos_upper_body_object_q_represents_real)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`left` |-> `point`,
          `right` |-> `bounded_atan_pos_upper_body_object_q point`,
          `left_value` |-> `x`,
          `right_value` |-> `bounded_atan_upper_body_real x`]
         bounded_object_q_interval_mul_cv_represents_real_singleton)
  >> asm_rewrite_tac
       [bounded_atan_pos_upper_object_q_def,
        bounded_atan_upper_horner_real_identity]
QED

Theorem bounded_interval64_atan_pos_lower_contains_real:
  bounded_interval64_atan_pos_lower magnitude = SOME result ==>
  bounded_interval64_contains_real result
    (bounded_atan_lower_real (bounded_atan_magnitude_real magnitude))
Proof
  strip_tac
  >> `bounded_interval64_covers_object_q result
        (bounded_atan_pos_lower_object_q
          (bounded_atan_magnitude_object_q magnitude))` by
       (mp_tac
          (Q.INST
            [`magnitude` |-> `magnitude`,
             `object_point` |->
               `bounded_atan_magnitude_object_q magnitude`,
             `result` |-> `result`]
            bounded_interval64_atan_pos_lower_covers_object_q)
        >> asm_rewrite_tac
             [GSYM bounded_atan_magnitude_interval_def,
              bounded_atan_magnitude_interval_covers_object_q])
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_pos_lower_object_q
          (bounded_atan_magnitude_object_q magnitude))
        (bounded_atan_lower_real
          (bounded_atan_magnitude_real magnitude))` by
       (mp_tac
          (Q.INST
            [`point` |-> `bounded_atan_magnitude_object_q magnitude`,
             `x` |-> `bounded_atan_magnitude_real magnitude`]
            bounded_atan_pos_lower_object_q_represents_real)
        >> asm_rewrite_tac
             [bounded_atan_magnitude_object_q_represents_real])
  >> irule
       compute_boundedWordRealRefinementTheory.bounded_interval64_covers_object_q_singleton_contains_real
  >> qexists_tac
       `bounded_atan_pos_lower_object_q
          (bounded_atan_magnitude_object_q magnitude)`
  >> asm_rewrite_tac []
QED

Theorem bounded_interval64_atan_pos_upper_contains_real:
  bounded_interval64_atan_pos_upper magnitude = SOME result ==>
  bounded_interval64_contains_real result
    (bounded_atan_upper_real (bounded_atan_magnitude_real magnitude))
Proof
  strip_tac
  >> `bounded_interval64_covers_object_q result
        (bounded_atan_pos_upper_object_q
          (bounded_atan_magnitude_object_q magnitude))` by
       (mp_tac
          (Q.INST
            [`magnitude` |-> `magnitude`,
             `object_point` |->
               `bounded_atan_magnitude_object_q magnitude`,
             `result` |-> `result`]
            bounded_interval64_atan_pos_upper_covers_object_q)
        >> asm_rewrite_tac
             [GSYM bounded_atan_magnitude_interval_def,
              bounded_atan_magnitude_interval_covers_object_q])
  >> `bounded_object_q_interval_represents_real_singleton
        (bounded_atan_pos_upper_object_q
          (bounded_atan_magnitude_object_q magnitude))
        (bounded_atan_upper_real
          (bounded_atan_magnitude_real magnitude))` by
       (mp_tac
          (Q.INST
            [`point` |-> `bounded_atan_magnitude_object_q magnitude`,
             `x` |-> `bounded_atan_magnitude_real magnitude`]
            bounded_atan_pos_upper_object_q_represents_real)
        >> asm_rewrite_tac
             [bounded_atan_magnitude_object_q_represents_real])
  >> irule
       compute_boundedWordRealRefinementTheory.bounded_interval64_covers_object_q_singleton_contains_real
  >> qexists_tac
       `bounded_atan_pos_upper_object_q
          (bounded_atan_magnitude_object_q magnitude)`
  >> asm_rewrite_tac []
QED

Theorem bounded_atan_magnitude_real_nonnegative:
  &0 <= bounded_atan_magnitude_real magnitude
Proof
  simp [bounded_atan_magnitude_real_def, bounded_signed64_real_def,
        bounded_word_scale_real_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
        compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def,
        REAL_LE_DIV]
QED

Theorem bounded_interval64_atan_pos_results_enclose_atn:
  bounded_interval64_atan_pos_lower magnitude = SOME lower_result /\
  bounded_interval64_atan_pos_upper magnitude = SOME upper_result ==>
  bounded_signed64_real (bounded_interval64_lower lower_result) <=
    atn (bounded_atan_magnitude_real magnitude) /\
  atn (bounded_atan_magnitude_real magnitude) <=
    bounded_signed64_real (bounded_interval64_upper upper_result)
Proof
  strip_tac
  >> `bounded_interval64_contains_real lower_result
        (bounded_atan_lower_real
          (bounded_atan_magnitude_real magnitude))` by
       metis_tac [bounded_interval64_atan_pos_lower_contains_real]
  >> `bounded_interval64_contains_real upper_result
        (bounded_atan_upper_real
          (bounded_atan_magnitude_real magnitude))` by
       metis_tac [bounded_interval64_atan_pos_upper_contains_real]
  >> mp_tac
       (Q.INST [`x` |-> `bounded_atan_magnitude_real magnitude`]
         compute_boundedAtanRealRefinementTheory.bounded_atan_alternating_bounds_nonnegative)
  >> impl_tac
  >- MATCH_ACCEPT_TAC bounded_atan_magnitude_real_nonnegative
  >> fs [bounded_interval64_contains_real_def]
  >> metis_tac [REAL_LE_TRANS]
QED

Theorem bounded_interval64_atan_positive_unit_contains_real:
  word_lo magnitude bounded_atan_scale /\
  bounded_interval64_atan_unit
    (bounded_atan_magnitude_interval magnitude) = SOME result ==>
  bounded_interval64_contains_real result
    (atn (bounded_atan_magnitude_real magnitude))
Proof
  strip_tac
  >> fs [compute_boundedAtanTheory.bounded_interval64_atan_unit_def,
         compute_boundedAtanTheory.bounded_interval64_atan_unit_lower_def,
         compute_boundedAtanTheory.bounded_interval64_atan_unit_upper_def,
         bounded_atan_magnitude_interval_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
         compute_boundedIntervalTheory.bounded_interval64_lower_def,
         compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_interval64_atan_pos_results_enclose_atn
  >> fs [bounded_interval64_contains_real_def,
         compute_boundedIntervalTheory.bounded_interval64_lower_def,
         compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Theorem bounded_atan_neg:
  atn (-x) = -(atn x)
Proof
  mp_tac (Q.SPEC `x` transcTheory.ATN_BOUNDS)
  >> strip_tac
  >> mp_tac (Q.SPEC `-(atn x)` transcTheory.TAN_ATN)
  >> impl_tac
  >- REAL_ASM_ARITH_TAC
  >> simp [transcTheory.TAN_NEG, transcTheory.ATN_TAN]
QED

Theorem bounded_signed64_neg_real:
  bounded_signed64_real (bounded_signed64_neg value) =
    -(bounded_signed64_real value)
Proof
  rw [bounded_signed64_real_def]
  >> rw
       [compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_value,
        intrealTheory.real_of_int_neg]
  >> simp [real_div]
QED

Theorem bounded_atan_negative_reciprocal_algebra:
  !a b p:real. -a = p - -b ==> a = -b - p
Proof
  REAL_ARITH_TAC
QED

Theorem bounded_atan_negative_reciprocal_identity:
  x < &0 ==> atn x = atn (-(inv x)) - pi / &2
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`x` |-> `-x`]
         compute_boundedAtanPiRefinementTheory.bounded_atan_positive_reciprocal_identity)
  >> impl_tac >- REAL_ASM_ARITH_TAC
  >> rw [bounded_atan_neg, REAL_INV_NEG]
  >> metis_tac [bounded_atan_negative_reciprocal_algebra]
QED

Theorem bounded_atan_negative_magnitude_real:
  bounded_signed64_real (BoundedSigned64 T magnitude) =
    -(bounded_atan_magnitude_real magnitude)
Proof
  simp [bounded_atan_magnitude_real_def, bounded_signed64_real_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
        intrealTheory.real_of_int_neg, real_div]
QED

Theorem bounded_atan_positive_magnitude_real:
  bounded_signed64_real (BoundedSigned64 F magnitude) =
    bounded_atan_magnitude_real magnitude
Proof
  simp [bounded_atan_magnitude_real_def, bounded_signed64_real_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
QED

Theorem bounded_atan_signed_zero_real:
  bounded_signed64_real (BoundedSigned64 T 0w) =
    bounded_signed64_real (BoundedSigned64 F 0w)
Proof
  simp [bounded_signed64_real_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
QED

Theorem bounded_interval64_atan_pos_lower_endpoint_sound:
  bounded_interval64_atan_pos_lower magnitude = SOME enclosure ==>
  bounded_signed64_real (bounded_interval64_lower enclosure) <=
    atn (bounded_signed64_real (BoundedSigned64 F magnitude))
Proof
  strip_tac
  >> `bounded_interval64_contains_real enclosure
        (bounded_atan_lower_real
          (bounded_atan_magnitude_real magnitude))` by
       metis_tac [bounded_interval64_atan_pos_lower_contains_real]
  >> mp_tac
       (Q.INST [`x` |-> `bounded_atan_magnitude_real magnitude`]
         compute_boundedAtanRealRefinementTheory.bounded_atan_alternating_bounds_nonnegative)
  >> impl_tac
  >- MATCH_ACCEPT_TAC bounded_atan_magnitude_real_nonnegative
  >> fs [bounded_interval64_contains_real_def]
  >> metis_tac [REAL_LE_TRANS, bounded_atan_positive_magnitude_real]
QED

Theorem bounded_interval64_atan_pos_upper_endpoint_sound:
  bounded_interval64_atan_pos_upper magnitude = SOME enclosure ==>
  atn (bounded_signed64_real (BoundedSigned64 F magnitude)) <=
    bounded_signed64_real (bounded_interval64_upper enclosure)
Proof
  strip_tac
  >> `bounded_interval64_contains_real enclosure
        (bounded_atan_upper_real
          (bounded_atan_magnitude_real magnitude))` by
       metis_tac [bounded_interval64_atan_pos_upper_contains_real]
  >> mp_tac
       (Q.INST [`x` |-> `bounded_atan_magnitude_real magnitude`]
         compute_boundedAtanRealRefinementTheory.bounded_atan_alternating_bounds_nonnegative)
  >> impl_tac
  >- MATCH_ACCEPT_TAC bounded_atan_magnitude_real_nonnegative
  >> fs [bounded_interval64_contains_real_def]
  >> metis_tac [REAL_LE_TRANS, bounded_atan_positive_magnitude_real]
QED

Theorem bounded_interval64_atan_neg_lower_endpoint_sound:
  bounded_interval64_atan_pos_upper magnitude = SOME enclosure ==>
  bounded_signed64_real
      (bounded_signed64_neg (bounded_interval64_upper enclosure)) <=
    atn (bounded_signed64_real (BoundedSigned64 T magnitude))
Proof
  strip_tac
  >> `atn (bounded_signed64_real (BoundedSigned64 F magnitude)) <=
        bounded_signed64_real (bounded_interval64_upper enclosure)` by
       metis_tac [bounded_interval64_atan_pos_upper_endpoint_sound]
  >> fs [bounded_signed64_neg_real,
         bounded_atan_negative_magnitude_real,
         bounded_atan_positive_magnitude_real, bounded_atan_neg]
QED

Theorem bounded_interval64_atan_neg_upper_endpoint_sound:
  bounded_interval64_atan_pos_lower magnitude = SOME enclosure ==>
  atn (bounded_signed64_real (BoundedSigned64 T magnitude)) <=
    bounded_signed64_real
      (bounded_signed64_neg (bounded_interval64_lower enclosure))
Proof
  strip_tac
  >> `bounded_signed64_real (bounded_interval64_lower enclosure) <=
        atn (bounded_signed64_real (BoundedSigned64 F magnitude))` by
       metis_tac [bounded_interval64_atan_pos_lower_endpoint_sound]
  >> fs [bounded_signed64_neg_real,
         bounded_atan_negative_magnitude_real,
         bounded_atan_positive_magnitude_real, bounded_atan_neg]
QED

Theorem bounded_interval64_atan_unit_lower_sound:
  bounded_interval64_atan_unit_lower endpoint = SOME output ==>
  bounded_signed64_real output <= atn (bounded_signed64_real endpoint)
Proof
  Cases_on `endpoint`
  >> rename1 `BoundedSigned64 negative magnitude`
  >> Cases_on `negative`
  >> fs [compute_boundedAtanTheory.bounded_interval64_atan_unit_lower_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac
       [bounded_interval64_atan_pos_lower_endpoint_sound,
        bounded_interval64_atan_neg_lower_endpoint_sound,
        bounded_atan_negative_magnitude_real,
        bounded_atan_signed_zero_real,
        bounded_atan_magnitude_real_def,
        compute_boundedAtanRealRefinementTheory.bounded_atan_zero]
QED

Theorem bounded_interval64_atan_unit_upper_sound:
  bounded_interval64_atan_unit_upper endpoint = SOME output ==>
  atn (bounded_signed64_real endpoint) <= bounded_signed64_real output
Proof
  Cases_on `endpoint`
  >> rename1 `BoundedSigned64 negative magnitude`
  >> Cases_on `negative`
  >> fs [compute_boundedAtanTheory.bounded_interval64_atan_unit_upper_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac
       [bounded_interval64_atan_pos_upper_endpoint_sound,
        bounded_interval64_atan_neg_upper_endpoint_sound,
        bounded_atan_negative_magnitude_real,
        bounded_atan_signed_zero_real,
        bounded_atan_magnitude_real_def,
        compute_boundedAtanRealRefinementTheory.bounded_atan_zero]
QED

Theorem bounded_interval64_atan_unit_contains_real:
  bounded_interval64_contains_real input value /\
  bounded_interval64_atan_unit input = SOME result ==>
  bounded_interval64_contains_real result (atn value)
Proof
  strip_tac
  >> fs [compute_boundedAtanTheory.bounded_interval64_atan_unit_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_interval64_atan_unit_lower_sound
  >> imp_res_tac bounded_interval64_atan_unit_upper_sound
  >> fs [bounded_interval64_contains_real_def,
         compute_boundedIntervalTheory.bounded_interval64_lower_def,
         compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> `atn
        (bounded_signed64_real (bounded_interval64_lower input)) <=
      atn value` by
       metis_tac
         [compute_boundedAtanPiRefinementTheory.bounded_atan_mono]
  >> `atn value <=
      atn (bounded_signed64_real (bounded_interval64_upper input))` by
       metis_tac
         [compute_boundedAtanPiRefinementTheory.bounded_atan_mono]
  >> metis_tac [REAL_LE_TRANS]
QED

Theorem bounded_interval64_neg_contains_real:
  bounded_interval64_contains_real source value ==>
  bounded_interval64_contains_real
    (bounded_interval64_neg source) (-value)
Proof
  Cases_on `source`
  >> simp
       [bounded_interval64_contains_real_def,
        compute_boundedIntervalAddTheory.bounded_interval64_neg_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        bounded_signed64_neg_real]
QED

Theorem bounded_interval64_add_contains_real:
  bounded_interval64_contains_real left left_value /\
  bounded_interval64_contains_real right right_value /\
  bounded_interval64_add left right = SOME result ==>
  bounded_interval64_contains_real result (left_value + right_value)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedIntervalAddTheory.bounded_interval64_add_value
  >> fs [bounded_interval64_contains_real_def,
         bounded_signed64_real_def, intrealTheory.real_of_int_add,
         real_div, REAL_ADD_RDISTRIB]
  >> REAL_ASM_ARITH_TAC
QED

Theorem bounded_signed64_neg_involutive:
  bounded_signed64_normalized value ==>
  bounded_signed64_neg (bounded_signed64_neg value) = value
Proof
  Cases_on `value`
  >> rename1 `BoundedSigned64 negative magnitude`
  >> Cases_on `negative`
  >> Cases_on `magnitude = 0w`
  >> simp
       [compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_make_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def]
QED

Theorem bounded_interval64_neg_involutive:
  bounded_interval64_valid source ==>
  bounded_interval64_neg (bounded_interval64_neg source) = source
Proof
  Cases_on `source`
  >> simp
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalAddTheory.bounded_interval64_neg_def,
        bounded_signed64_neg_involutive]
QED

Theorem bounded_atan_word_scale_int_positive:
  (0:int) < bounded_word_scale_int
Proof
  simp
       [compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def]
QED

Theorem bounded_atan_word_scale_int_squared:
  (bounded_word_scale_int:int) * bounded_word_scale_int =
    1208925819614629174706176
Proof
  simp
       [compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def]
QED

Theorem bounded_interval64_positive_inv_certificate_singleton_contains_real:
  bounded_interval64_inv_certificate
      (BoundedInterval64 endpoint endpoint) output /\
  bounded_signed64_strict_positive endpoint ==>
  bounded_interval64_contains_real output
    (inv (bounded_signed64_real endpoint))
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`input` |-> `BoundedInterval64 endpoint endpoint`,
          `output` |-> `output`]
         compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_inv_certificate_positive_components)
  >> impl_tac
  >- simp [compute_boundedIntervalTheory.bounded_interval64_lower_def]
  >> strip_tac
  >> fs [compute_boundedIntervalTheory.bounded_interval64_lower_def,
         compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> `bounded_int_fraction_real
        (bounded_signed64_to_int (bounded_interval64_lower output),
         bounded_word_scale_int) <=
      bounded_int_fraction_real
        (bounded_word_scale_int,bounded_signed64_to_int endpoint)` by
       (irule bounded_int_fraction_real_le
        >> asm_rewrite_tac
             [bounded_atan_word_scale_int_positive,
              bounded_atan_word_scale_int_squared,
              compute_boundedIntervalTheory.bounded_interval64_lower_def,
              compute_boundedIntervalTheory.bounded_interval64_upper_def])
  >> `bounded_int_fraction_real
        (bounded_word_scale_int,bounded_signed64_to_int endpoint) <=
      bounded_int_fraction_real
        (bounded_signed64_to_int (bounded_interval64_upper output),
         bounded_word_scale_int)` by
       (irule bounded_int_fraction_real_le
        >> asm_rewrite_tac
             [bounded_atan_word_scale_int_positive,
              bounded_atan_word_scale_int_squared,
              compute_boundedIntervalTheory.bounded_interval64_lower_def,
              compute_boundedIntervalTheory.bounded_interval64_upper_def])
  >> `bounded_int_fraction_real
        (bounded_word_scale_int,bounded_signed64_to_int endpoint) =
      inv (bounded_signed64_real endpoint)` by
       (rw [bounded_int_fraction_real_def, bounded_signed64_real_def,
            bounded_word_scale_real_def]
        >> `real_of_int (bounded_signed64_to_int endpoint) <> 0` by
             (simp [GSYM intrealTheory.real_of_int_lt]
              >> intLib.ARITH_TAC)
        >> REAL_ASM_FIELD_TAC)
  >> fs [bounded_interval64_contains_real_def,
         bounded_signed64_real_def, bounded_word_scale_real_def,
         bounded_int_fraction_real_def]
QED

Theorem bounded_interval64_negative_inv_certificate_singleton_contains_real:
  bounded_interval64_inv_certificate
      (BoundedInterval64 endpoint endpoint) output /\
  bounded_signed64_strict_negative endpoint ==>
  bounded_interval64_contains_real output
    (inv (bounded_signed64_real endpoint))
Proof
  strip_tac
  >> `bounded_interval64_valid output` by
       metis_tac
         [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_inv_certificate_valid_components]
  >> `bounded_interval64_inv_certificate
        (bounded_interval64_neg
          (BoundedInterval64 endpoint endpoint))
        (bounded_interval64_neg output)` by
       (irule
          compute_boundedAnalyticObjectInverseOperationRefinementTheory.bounded_interval64_inv_certificate_negative_negates
        >> simp [compute_boundedIntervalTheory.bounded_interval64_upper_def])
  >> `bounded_signed64_strict_positive
        (bounded_signed64_neg endpoint)` by
       metis_tac
         [compute_boundedAnalyticObjectInverseOperationRefinementTheory.bounded_signed64_strict_negative_neg_positive]
  >> `bounded_interval64_contains_real
        (bounded_interval64_neg output)
        (inv (bounded_signed64_real
          (bounded_signed64_neg endpoint)))` by
       (irule
          bounded_interval64_positive_inv_certificate_singleton_contains_real
        >> qpat_x_assum
             `bounded_interval64_inv_certificate
               (bounded_interval64_neg
                 (BoundedInterval64 endpoint endpoint))
               (bounded_interval64_neg output)` mp_tac
        >> simp
             [compute_boundedIntervalAddTheory.bounded_interval64_neg_def])
  >> `bounded_interval64_contains_real
        (bounded_interval64_neg (bounded_interval64_neg output))
        (-(inv (bounded_signed64_real
          (bounded_signed64_neg endpoint))))` by
       metis_tac [bounded_interval64_neg_contains_real]
  >> fs [bounded_interval64_neg_involutive, bounded_signed64_neg_real,
         REAL_INV_NEG]
  >> metis_tac [bounded_interval64_neg_involutive]
QED

Theorem bounded_interval64_atan_negative_unit_contains_real:
  magnitude <> 0w /\
  word_lo magnitude bounded_atan_scale /\
  bounded_interval64_atan_unit
    (BoundedInterval64 (BoundedSigned64 T magnitude)
      (BoundedSigned64 T magnitude)) = SOME result ==>
  bounded_interval64_contains_real result
    (atn (bounded_signed64_real (BoundedSigned64 T magnitude)))
Proof
  strip_tac
  >> fs [compute_boundedAtanTheory.bounded_interval64_atan_unit_def,
         compute_boundedAtanTheory.bounded_interval64_atan_unit_lower_def,
         compute_boundedAtanTheory.bounded_interval64_atan_unit_upper_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
         compute_boundedIntervalTheory.bounded_interval64_lower_def,
         compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_interval64_atan_pos_results_enclose_atn
  >> fs [bounded_interval64_contains_real_def,
         compute_boundedIntervalTheory.bounded_interval64_lower_def,
         compute_boundedIntervalTheory.bounded_interval64_upper_def,
         bounded_signed64_neg_real,
         bounded_atan_negative_magnitude_real,
         bounded_atan_neg]
  >> REAL_ASM_ARITH_TAC
QED

Theorem bounded_interval64_atan_unit_some_input_valid:
  bounded_interval64_atan_unit input = SOME result ==>
  bounded_interval64_valid input
Proof
  rw [compute_boundedAtanTheory.bounded_interval64_atan_unit_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_interval64_atan_unit_singleton_contains_real:
  word_lo (bounded_signed64_magnitude endpoint) bounded_atan_scale /\
  bounded_interval64_atan_unit (BoundedInterval64 endpoint endpoint) =
    SOME result ==>
  bounded_interval64_contains_real result
    (atn (bounded_signed64_real endpoint))
Proof
  Cases_on `endpoint`
  >> rename1 `BoundedSigned64 negative magnitude`
  >> strip_tac
  >> `bounded_interval64_valid
        (BoundedInterval64 (BoundedSigned64 negative magnitude)
          (BoundedSigned64 negative magnitude))` by
       metis_tac [bounded_interval64_atan_unit_some_input_valid]
  >> Cases_on `negative`
  >> fs [compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
         compute_boundedIntervalTheory.bounded_interval64_valid_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def]
  >> metis_tac
       [bounded_interval64_atan_positive_unit_contains_real,
        bounded_interval64_atan_negative_unit_contains_real,
        bounded_atan_magnitude_interval_def,
        bounded_atan_magnitude_real_def]
QED

Theorem bounded_signed64_strict_positive_real:
  bounded_signed64_strict_positive endpoint ==>
  &0 < bounded_signed64_real endpoint
Proof
  strip_tac
  >> fs [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_correct]
  >> rw [bounded_signed64_real_def, bounded_word_scale_real_def,
         compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def]
  >> once_rewrite_tac
       [GSYM (Q.INST [`n` |-> `0`] intrealTheory.real_of_int_num)]
  >> rw [intrealTheory.real_of_int_lt]
QED

Theorem bounded_signed64_strict_negative_real:
  bounded_signed64_strict_negative endpoint ==>
  bounded_signed64_real endpoint < &0
Proof
  strip_tac
  >> fs [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_correct]
  >> rw [bounded_signed64_real_def, bounded_word_scale_real_def,
         compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def]
  >> once_rewrite_tac
       [GSYM (Q.INST [`n` |-> `0`] intrealTheory.real_of_int_num)]
  >> rw [intrealTheory.real_of_int_lt]
QED

Theorem bounded_interval64_singleton_contains_real:
  bounded_interval64_contains_real
    (BoundedInterval64 endpoint endpoint) (bounded_signed64_real endpoint)
Proof
  simp [bounded_interval64_contains_real_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Theorem bounded_interval64_atan_positive_outer_contains_real:
  bounded_signed64_strict_positive endpoint /\
  bounded_interval64_inv_certificate
    (BoundedInterval64 endpoint endpoint) reciprocal /\
  bounded_interval64_atan_unit reciprocal = SOME reduced_atan /\
  bounded_interval64_add bounded_atan_pi_half
    (bounded_interval64_neg reduced_atan) = SOME result ==>
  bounded_interval64_contains_real result
    (atn (bounded_signed64_real endpoint))
Proof
  strip_tac
  >> `bounded_interval64_contains_real reciprocal
        (inv (bounded_signed64_real endpoint))` by
       metis_tac
         [bounded_interval64_positive_inv_certificate_singleton_contains_real]
  >> `bounded_interval64_contains_real reduced_atan
        (atn (inv (bounded_signed64_real endpoint)))` by
       metis_tac [bounded_interval64_atan_unit_contains_real]
  >> `bounded_interval64_contains_real
        (bounded_interval64_neg reduced_atan)
        (-(atn (inv (bounded_signed64_real endpoint))))` by
       metis_tac [bounded_interval64_neg_contains_real]
  >> `bounded_interval64_contains_real bounded_atan_pi_half (pi / &2)` by
       MATCH_ACCEPT_TAC
         compute_boundedAtanPiRefinementTheory.bounded_atan_pi_half_contains_real
  >> `bounded_interval64_contains_real result
        (pi / &2 + -(atn (inv (bounded_signed64_real endpoint))))` by
       metis_tac [bounded_interval64_add_contains_real]
  >> `&0 < bounded_signed64_real endpoint` by
       metis_tac [bounded_signed64_strict_positive_real]
  >> mp_tac
       (Q.INST [`x` |-> `bounded_signed64_real endpoint`]
         compute_boundedAtanPiRefinementTheory.bounded_atan_positive_reciprocal_identity)
  >> asm_rewrite_tac [real_sub]
  >> metis_tac []
QED

Theorem bounded_interval64_atan_negative_outer_contains_real:
  bounded_signed64_strict_negative endpoint /\
  bounded_interval64_inv_certificate
    (BoundedInterval64 endpoint endpoint) reciprocal /\
  bounded_interval64_atan_unit
    (bounded_interval64_neg reciprocal) = SOME reduced_atan /\
  bounded_interval64_add reduced_atan
    (bounded_interval64_neg bounded_atan_pi_half) = SOME result ==>
  bounded_interval64_contains_real result
    (atn (bounded_signed64_real endpoint))
Proof
  strip_tac
  >> `bounded_interval64_contains_real reciprocal
        (inv (bounded_signed64_real endpoint))` by
       metis_tac
         [bounded_interval64_negative_inv_certificate_singleton_contains_real]
  >> `bounded_interval64_contains_real
        (bounded_interval64_neg reciprocal)
        (-(inv (bounded_signed64_real endpoint)))` by
       metis_tac [bounded_interval64_neg_contains_real]
  >> `bounded_interval64_contains_real reduced_atan
        (atn (-(inv (bounded_signed64_real endpoint))))` by
       metis_tac [bounded_interval64_atan_unit_contains_real]
  >> `bounded_interval64_contains_real
        (bounded_interval64_neg bounded_atan_pi_half) (-(pi / &2))` by
       metis_tac
         [bounded_interval64_neg_contains_real,
          compute_boundedAtanPiRefinementTheory.bounded_atan_pi_half_contains_real]
  >> `bounded_interval64_contains_real result
        (atn (-(inv (bounded_signed64_real endpoint))) + -(pi / &2))` by
       metis_tac [bounded_interval64_add_contains_real]
  >> `bounded_signed64_real endpoint < &0` by
       metis_tac [bounded_signed64_strict_negative_real]
  >> mp_tac
       (Q.INST [`x` |-> `bounded_signed64_real endpoint`]
         bounded_atan_negative_reciprocal_identity)
  >> asm_rewrite_tac [real_sub]
  >> metis_tac []
QED

Theorem bounded_atan_outer_positive_endpoint:
  ~word_lo magnitude bounded_atan_scale /\
  magnitude <> bounded_atan_scale ==>
  bounded_signed64_strict_positive (BoundedSigned64 F magnitude)
Proof
  strip_tac
  >> `magnitude <> 0w` by
       (CCONTR_TAC
        >> fs [compute_boundedAtanTheory.bounded_atan_scale_def,
               compute_boundedAtanTheory.bounded_atan_word64_def])
  >> simp
       [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def]
QED

Theorem bounded_atan_outer_negative_endpoint:
  ~word_lo magnitude bounded_atan_scale /\
  magnitude <> bounded_atan_scale ==>
  bounded_signed64_strict_negative (BoundedSigned64 T magnitude)
Proof
  strip_tac
  >> `magnitude <> 0w` by
       (CCONTR_TAC
        >> fs [compute_boundedAtanTheory.bounded_atan_scale_def,
               compute_boundedAtanTheory.bounded_atan_word64_def])
  >> simp
       [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def]
QED

Theorem bounded_interval64_atan_positive_range_point_contains_real:
  bounded_interval64_atan_range_point
    (BoundedSigned64 F magnitude) reciprocal = SOME result ==>
  bounded_interval64_contains_real result
    (atn (bounded_signed64_real (BoundedSigned64 F magnitude)))
Proof
  rw [compute_boundedAtanTheory.bounded_interval64_atan_range_point_def,
      compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
      compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def]
  >- (irule bounded_interval64_atan_unit_singleton_contains_real
      >> asm_simp_tac (srw_ss())
           [compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def])
  >> Cases_on `reciprocal`
  >> gvs []
  >> every_case_tac
  >> gvs []
  >> metis_tac
       [bounded_interval64_atan_positive_outer_contains_real,
        bounded_atan_outer_positive_endpoint]
QED

Theorem bounded_interval64_atan_negative_range_point_contains_real:
  bounded_interval64_atan_range_point
    (BoundedSigned64 T magnitude) reciprocal = SOME result ==>
  bounded_interval64_contains_real result
    (atn (bounded_signed64_real (BoundedSigned64 T magnitude)))
Proof
  rw [compute_boundedAtanTheory.bounded_interval64_atan_range_point_def,
      compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
      compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def]
  >- (irule bounded_interval64_atan_unit_singleton_contains_real
      >> asm_simp_tac (srw_ss())
           [compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def])
  >> Cases_on `reciprocal`
  >> gvs []
  >> `magnitude <> 0w` by
       (CCONTR_TAC
        >> fs [compute_boundedAtanTheory.bounded_atan_scale_def,
               compute_boundedAtanTheory.bounded_atan_word64_def])
  >> fs []
  >> Cases_on `bounded_interval64_atan_unit (bounded_interval64_neg x)`
  >> gvs []
  >> metis_tac
       [bounded_interval64_atan_negative_outer_contains_real,
        bounded_atan_outer_negative_endpoint]
QED

Theorem bounded_interval64_atan_range_point_contains_real:
  bounded_interval64_atan_range_point endpoint reciprocal = SOME result ==>
  bounded_interval64_contains_real result
    (atn (bounded_signed64_real endpoint))
Proof
  Cases_on `endpoint`
  >> rename1 `BoundedSigned64 negative magnitude`
  >> Cases_on `negative`
  >> metis_tac
       [bounded_interval64_atan_positive_range_point_contains_real,
        bounded_interval64_atan_negative_range_point_contains_real]
QED

Theorem bounded_interval64_atan_range_contains_real:
  bounded_interval64_contains_real input value /\
  bounded_interval64_atan_range input
    lower_reciprocal upper_reciprocal = SOME result ==>
  bounded_interval64_contains_real result (atn value)
Proof
  Cases_on `input`
  >> rename1 `BoundedInterval64 input_lower input_upper`
  >> rw [compute_boundedAtanTheory.bounded_interval64_atan_range_def]
  >> every_case_tac
  >> gvs [bounded_interval64_contains_real_def,
          compute_boundedIntervalTheory.bounded_interval64_lower_def,
          compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> `bounded_interval64_contains_real x'
        (atn (bounded_signed64_real input_lower))` by
       metis_tac [bounded_interval64_atan_range_point_contains_real]
  >> `bounded_interval64_contains_real x
        (atn (bounded_signed64_real input_upper))` by
       metis_tac [bounded_interval64_atan_range_point_contains_real]
  >> `atn (bounded_signed64_real input_lower) <= atn value` by
       metis_tac [compute_boundedAtanPiRefinementTheory.bounded_atan_mono]
  >> `atn value <= atn (bounded_signed64_real input_upper)` by
       metis_tac [compute_boundedAtanPiRefinementTheory.bounded_atan_mono]
  >> fs [bounded_interval64_contains_real_def]
  >> metis_tac [REAL_LE_TRANS]
QED

val _ = export_theory ();
