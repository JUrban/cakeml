(*****************************************************************************
 * Source-rational bridge from generic scale-2^40 preparation to the
 * existing Candle object-q interval contract.
 *
 * This is the first semantic seam above structural plan refinement.  It
 * proves that a successfully prepared constant encloses the exact canonical
 * source rational expected by the object-level checker; no rounded object
 * value or case-specific constant table is introduced.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectRefinement
Ancestors
  compute_boundedAnalyticPreparedPlanSound
  compute_boundedObjectIntervalRelation
Libs
  bossLib preamble intLib

Definition bounded_analytic_source_q_cv_def:
  bounded_analytic_source_q_cv positive negative denominator_predecessor =
    Pair (Pair (Num positive) (Num negative))
      (Num denominator_predecessor)
End

Theorem bounded_analytic_source_q_cv_decodes[simp]:
  bounded_object_q_ints
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor) =
    SOME ((&positive:int) - &negative,
          &(SUC denominator_predecessor):int)
Proof
  simp [bounded_analytic_source_q_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
QED

Theorem bounded_analytic_rational_constant64_covers_object_q:
  bounded_analytic_rational_constant64 positive negative
      denominator_predecessor = SOME interval ==>
  bounded_interval64_covers_object_q interval
    (Pair
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor)
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor))
Proof
  strip_tac
  >> drule bounded_analytic_rational_constant64_covers
  >> rw [bounded_analytic_rational_interval_covers_def,
         compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
         compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
         bounded_analytic_source_q_cv_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
         compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def,
         compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_scale40_def]
QED

val _ = export_theory ();
