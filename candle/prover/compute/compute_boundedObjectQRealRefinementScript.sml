(*****************************************************************************
 * Real semantics for Candle's exact object-q witnesses.
 *
 * The fixed-word checker relates its outputs to exact rational [cv] objects.
 * This theory gives those objects a small, reusable real-number semantics so
 * analytic range theorems can consume them without normalising rationals or
 * rebuilding per-expression arithmetic proofs.
 *****************************************************************************)
Theory compute_boundedObjectQRealRefinement
Ancestors
  compute_boundedAnalyticObjectProductRefinement intreal
Libs
  bossLib preamble realLib RealField

Definition bounded_int_fraction_real_def:
  bounded_int_fraction_real
      ((numerator,denominator):int # int) =
    real_of_int numerator / real_of_int denominator
End

Definition bounded_object_q_represents_real_def:
  bounded_object_q_represents_real encoded value <=>
    ?numerator denominator.
      bounded_object_q_ints encoded = SOME (numerator,denominator) /\
      0 < denominator /\
      value = bounded_int_fraction_real (numerator,denominator)
End

Definition bounded_object_q_interval_represents_real_singleton_def:
  bounded_object_q_interval_represents_real_singleton encoded value <=>
    ?lower upper.
      encoded = Pair lower upper /\
      bounded_object_q_represents_real lower value /\
      bounded_object_q_represents_real upper value
End

Theorem bounded_int_fraction_real_mul:
  0 < SND left /\ 0 < SND right ==>
  bounded_int_fraction_real
      (bounded_int_fraction_mul left right) =
    bounded_int_fraction_real left * bounded_int_fraction_real right
Proof
  PairCases_on `left`
  >> PairCases_on `right`
  >> rw [bounded_int_fraction_real_def,
         compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def]
  >> `real_of_int left1 <> 0 /\ real_of_int right1 <> 0` by
       (simp [GSYM intrealTheory.real_of_int_lt]
        >> intLib.ARITH_TAC)
  >> simp [intrealTheory.real_of_int_mul]
  >> REAL_ASM_FIELD_TAC
QED

Theorem bounded_int_fraction_real_add:
  0 < left_denominator /\ 0 < right_denominator ==>
  bounded_int_fraction_real
      (left_numerator * right_denominator +
         right_numerator * left_denominator,
       left_denominator * right_denominator) =
    bounded_int_fraction_real (left_numerator,left_denominator) +
    bounded_int_fraction_real (right_numerator,right_denominator)
Proof
  strip_tac
  >> `real_of_int left_denominator <> 0 /\
      real_of_int right_denominator <> 0` by
       (simp [GSYM intrealTheory.real_of_int_lt]
        >> intLib.ARITH_TAC)
  >> simp [bounded_int_fraction_real_def,
           intrealTheory.real_of_int_add,
           intrealTheory.real_of_int_mul]
  >> REAL_ASM_FIELD_TAC
QED

Theorem bounded_analytic_source_q_cv_represents_real:
  bounded_object_q_represents_real
    (bounded_analytic_source_q_cv positive negative
      denominator_predecessor)
    (bounded_int_fraction_real
      ((&positive:int) - &negative,
       &(SUC denominator_predecessor):int))
Proof
  rw [bounded_object_q_represents_real_def]
  >> qexistsl_tac
       [`(&positive:int) - &negative`,
        `&(SUC denominator_predecessor):int`]
  >> simp
       [compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_decodes]
QED

Theorem bounded_analytic_source_q_interval_cv_represents_real_singleton:
  bounded_object_q_interval_represents_real_singleton
    (bounded_analytic_source_q_interval_cv positive negative
      denominator_predecessor)
    (bounded_int_fraction_real
      ((&positive:int) - &negative,
       &(SUC denominator_predecessor):int))
Proof
  simp [bounded_object_q_interval_represents_real_singleton_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
        bounded_analytic_source_q_cv_represents_real]
QED

Theorem bounded_object_q_add_cv_represents_real:
  bounded_object_q_represents_real left left_value /\
  bounded_object_q_represents_real right right_value ==>
  bounded_object_q_represents_real
    (bounded_object_q_add_cv left right)
    (left_value + right_value)
Proof
  rw [bounded_object_q_represents_real_def]
  >> qexistsl_tac
       [`numerator * denominator' + numerator' * denominator`,
        `denominator * denominator'`]
  >> `0 < denominator * denominator'` by
       (match_mp_tac
          (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
        >> simp [])
  >> simp
       [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes,
        bounded_int_fraction_real_add]
QED

Theorem bounded_object_q_mul_cv_represents_real:
  bounded_object_q_represents_real left left_value /\
  bounded_object_q_represents_real right right_value ==>
  bounded_object_q_represents_real
    (bounded_object_q_mul_cv left right)
    (left_value * right_value)
Proof
  rw [bounded_object_q_represents_real_def]
  >> qexistsl_tac
       [`numerator * numerator'`, `denominator * denominator'`]
  >> `0 < denominator * denominator'` by
       (match_mp_tac
          (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
        >> simp [])
  >> conj_tac
  >- (mp_tac
        (Q.INST
          [`left_fraction` |-> `(numerator,denominator)`,
           `right_fraction` |-> `(numerator',denominator')`]
          bounded_object_q_mul_cv_decodes)
      >> simp [bounded_int_fraction_mul_def])
  >> conj_tac
  >- simp []
  >> mp_tac
       (Q.INST
         [`left` |-> `(numerator,denominator)`,
          `right` |-> `(numerator',denominator')`]
         bounded_int_fraction_real_mul)
  >> simp [bounded_int_fraction_mul_def]
QED

Theorem bounded_object_q_min_cv_represents_same_real:
  bounded_object_q_represents_real left value /\
  bounded_object_q_represents_real right value ==>
  bounded_object_q_represents_real
    (bounded_object_q_min_cv left right) value
Proof
  rw [bounded_object_q_min_cv_def]
QED

Theorem bounded_object_q_max_cv_represents_same_real:
  bounded_object_q_represents_real left value /\
  bounded_object_q_represents_real right value ==>
  bounded_object_q_represents_real
    (bounded_object_q_max_cv left right) value
Proof
  rw [bounded_object_q_max_cv_def]
QED

Theorem bounded_object_q_min4_cv_represents_same_real:
  bounded_object_q_represents_real q1 value /\
  bounded_object_q_represents_real q2 value /\
  bounded_object_q_represents_real q3 value /\
  bounded_object_q_represents_real q4 value ==>
  bounded_object_q_represents_real
    (bounded_object_q_min4_cv q1 q2 q3 q4) value
Proof
  strip_tac
  >> fs [bounded_object_q_min4_cv_def]
  >> irule bounded_object_q_min_cv_represents_same_real
  >> conj_tac
  >> irule bounded_object_q_min_cv_represents_same_real
  >> simp []
QED

Theorem bounded_object_q_max4_cv_represents_same_real:
  bounded_object_q_represents_real q1 value /\
  bounded_object_q_represents_real q2 value /\
  bounded_object_q_represents_real q3 value /\
  bounded_object_q_represents_real q4 value ==>
  bounded_object_q_represents_real
    (bounded_object_q_max4_cv q1 q2 q3 q4) value
Proof
  strip_tac
  >> fs [bounded_object_q_max4_cv_def]
  >> irule bounded_object_q_max_cv_represents_same_real
  >> conj_tac
  >> irule bounded_object_q_max_cv_represents_same_real
  >> simp []
QED

Theorem bounded_object_q_interval_add_cv_represents_real_singleton:
  bounded_object_q_interval_represents_real_singleton left left_value /\
  bounded_object_q_interval_represents_real_singleton right right_value ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_object_q_interval_add_cv left right)
    (left_value + right_value)
Proof
  rw [bounded_object_q_interval_represents_real_singleton_def]
  >> simp
       [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_add_cv_def]
  >> metis_tac [bounded_object_q_add_cv_represents_real]
QED

Theorem bounded_object_q_interval_mul_cv_represents_real_singleton:
  bounded_object_q_interval_represents_real_singleton left left_value /\
  bounded_object_q_interval_represents_real_singleton right right_value ==>
  bounded_object_q_interval_represents_real_singleton
    (bounded_object_q_interval_mul_cv left right)
    (left_value * right_value)
Proof
  rw [bounded_object_q_interval_represents_real_singleton_def]
  >> simp [bounded_object_q_interval_mul_cv_def]
  >> metis_tac
       [bounded_object_q_mul_cv_represents_real,
        bounded_object_q_min4_cv_represents_same_real,
        bounded_object_q_max4_cv_represents_same_real]
QED

val _ = export_theory ();
