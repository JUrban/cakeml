(*****************************************************************************
 * Real semantics for scale-2^40 word intervals and their exact rational
 * enclosure contract.
 *****************************************************************************)
Theory compute_boundedWordRealRefinement
Ancestors
  compute_boundedObjectQRealRefinement
Libs
  bossLib preamble realLib RealField

open realTheory

Definition bounded_word_scale_real_def:
  bounded_word_scale_real =
    real_of_int bounded_word_scale_int
End

Definition bounded_signed64_real_def:
  bounded_signed64_real value =
    real_of_int (bounded_signed64_to_int value) /
      bounded_word_scale_real
End

Definition bounded_interval64_contains_real_def:
  bounded_interval64_contains_real interval value <=>
    bounded_signed64_real (bounded_interval64_lower interval) <= value /\
    value <= bounded_signed64_real (bounded_interval64_upper interval)
End

Theorem bounded_int_fraction_real_le:
  0 < left_denominator /\ 0 < right_denominator /\
  left_numerator * right_denominator <=
    right_numerator * left_denominator ==>
  bounded_int_fraction_real (left_numerator,left_denominator) <=
    bounded_int_fraction_real (right_numerator,right_denominator)
Proof
  strip_tac
  >> `(&0:real) < real_of_int left_denominator` by
       (once_rewrite_tac
          [GSYM (Q.INST [`n` |-> `0`] intrealTheory.real_of_int_num)]
        >> rw [intrealTheory.real_of_int_lt])
  >> `(&0:real) < real_of_int right_denominator` by
       (once_rewrite_tac
          [GSYM (Q.INST [`n` |-> `0`] intrealTheory.real_of_int_num)]
        >> rw [intrealTheory.real_of_int_lt])
  >> PURE_REWRITE_TAC [bounded_int_fraction_real_def]
  >> irule
       (iffRL
         (MATCH_MP REAL_LE_LDIV_EQ
           (ASSUME ``(&0:real) < real_of_int left_denominator``)))
  >> `real_of_int right_numerator / real_of_int right_denominator *
        real_of_int left_denominator =
      (real_of_int right_numerator * real_of_int left_denominator) /
        real_of_int right_denominator` by REAL_ASM_FIELD_TAC
  >> asm_rewrite_tac []
  >> irule
       (iffRL
         (MATCH_MP REAL_LE_RDIV_EQ
           (ASSUME ``(&0:real) < real_of_int right_denominator``)))
  >> metis_tac
       [intrealTheory.real_of_int_le,
        intrealTheory.real_of_int_mul, REAL_MUL_COMM]
QED

Theorem bounded_interval64_covers_object_q_singleton_contains_real:
  bounded_interval64_covers_object_q interval encoded /\
  bounded_object_q_interval_represents_real_singleton encoded value ==>
  bounded_interval64_contains_real interval value
Proof
  strip_tac
  >> fs [bounded_object_q_interval_represents_real_singleton_def]
  >> fs [bounded_object_q_represents_real_def]
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> `bounded_int_fraction_real
        (bounded_signed64_to_int (bounded_interval64_lower interval),
         bounded_word_scale_int) <=
      bounded_int_fraction_real (numerator,denominator)` by
       (irule bounded_int_fraction_real_le
        >> fs
             [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
              compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def,
              integerTheory.INT_MUL_COMM])
  >> `bounded_int_fraction_real (numerator',denominator') <=
      bounded_int_fraction_real
        (bounded_signed64_to_int (bounded_interval64_upper interval),
         bounded_word_scale_int)` by
       (irule bounded_int_fraction_real_le
        >> fs
             [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
              compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def,
              integerTheory.INT_MUL_COMM])
  >> rw [bounded_interval64_contains_real_def,
         bounded_signed64_real_def, bounded_word_scale_real_def]
  >> PURE_REWRITE_TAC [GSYM bounded_int_fraction_real_def]
  >> metis_tac []
QED

val _ = export_theory ();
