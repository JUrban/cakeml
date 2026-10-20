(*****************************************************************************
 * Exact source conversion of a completed fixed-decimal sqrt operand.
 *
 * The actual-operand contract represents a positive fixed interval as the
 * canonical rational interval with denominator 10^12.  These lemmas show
 * that the unchanged source rational-to-fixed conversion recovers precisely
 * the interval that was produced by Taylor completion.
 *****************************************************************************)
Theory compute_boundedCase10173ActualSqrtConversion
Ancestors
  compute_boundedCase10173ActualSqrtOperand
Libs
  bossLib preamble wordsLib

Theorem bounded_case10173_positive_endpoint64_q_floor_self:
  bounded_object_positive_q_floor64_decimal
      (bounded_case10173_positive_endpoint64_q_cv
        (BoundedSigned64 F magnitude)) =
    SOME (BoundedSigned64 F magnitude)
Proof
  qspec_then `magnitude` assume_tac wordsTheory.w2n_lt
  >>
  simp
    [compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_positive_endpoint64_q_cv_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_decimal_natural_floor64_def,
     compute_boundedTheory.bounded_word_base_def,
     wordsTheory.dimword_64]
QED

Theorem bounded_case10173_positive_endpoint64_q_ceil_self:
  bounded_object_positive_q_ceil64_decimal
      (bounded_case10173_positive_endpoint64_q_cv
        (BoundedSigned64 F magnitude)) =
    SOME (BoundedSigned64 F magnitude)
Proof
  qspec_then `magnitude` assume_tac wordsTheory.w2n_lt
  >>
  simp
    [compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_positive_endpoint64_q_cv_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_decimal_natural_ceil64_def,
     compute_boundedTheory.bounded_word_base_def,
     wordsTheory.dimword_64]
QED

Theorem bounded_case10173_positive_interval64_q_conversion:
  bounded_interval64_valid interval /\
  bounded_case10173_positive_interval64_q_cv interval = SOME input ==>
  bounded_object_positive_q_interval64_decimal input = SOME interval
Proof
  Cases_on `interval`
  >> Cases_on `b`
  >> Cases_on `b0`
  >> Cases_on `b'`
  >> Cases_on `b`
  >> rw
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_positive_interval64_q_cv_def]
  >> gvs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_def,
        bounded_case10173_positive_endpoint64_q_floor_self,
        bounded_case10173_positive_endpoint64_q_ceil_self]
QED

val _ = export_theory ();
