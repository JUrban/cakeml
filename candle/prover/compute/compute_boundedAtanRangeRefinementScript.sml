(*****************************************************************************
 * Real-range refinement for the fixed-scale arctangent kernel.
 *****************************************************************************)
Theory compute_boundedAtanRangeRefinement
Ancestors
  compute_boundedAtanWordRefinement compute_boundedWordRealRefinement
  compute_boundedAnalyticObjectCertificateRefinement
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

val _ = export_theory ();
