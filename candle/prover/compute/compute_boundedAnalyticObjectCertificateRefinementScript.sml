(*****************************************************************************
 * Exact object-q witnesses for supplied scale-2^40 certificate intervals.
 *
 * Nonlinear preparation supplies word intervals for values and derivatives.
 * This proof-only representation bridge exposes those endpoints as exact
 * rationals, so operation-specific certificate soundness can feed the shared
 * unary Taylor refinement without trusting a conversion or changing runtime
 * code.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectCertificateRefinement
Ancestors
  compute_boundedAnalyticObjectUnaryRefinement
Libs
  bossLib preamble intLib

Definition bounded_signed64_object_q_cv_def:
  bounded_signed64_object_q_cv value =
    Pair (bounded_signed64_object_cv value) (Num 1099511627775)
End

Definition bounded_interval64_object_q_cv_def:
  bounded_interval64_object_q_cv (BoundedInterval64 lower upper) =
    Pair (bounded_signed64_object_q_cv lower)
      (bounded_signed64_object_q_cv upper)
End

Theorem bounded_signed64_object_q_cv_decodes[simp]:
  bounded_object_q_ints (bounded_signed64_object_q_cv value) =
    SOME (bounded_signed64_to_int value,(&1099511627776:int))
Proof
  simp [bounded_signed64_object_q_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def]
QED

Theorem bounded_interval64_object_q_cv_decodes[simp]:
  bounded_object_q_interval_ints (bounded_interval64_object_q_cv interval) =
    SOME
      ((bounded_signed64_to_int (bounded_interval64_lower interval),
        (&1099511627776:int)),
       (bounded_signed64_to_int (bounded_interval64_upper interval),
        (&1099511627776:int)))
Proof
  Cases_on `interval`
  >> simp [bounded_interval64_object_q_cv_def,
           compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
           compute_boundedIntervalTheory.bounded_interval64_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Theorem bounded_interval64_covers_own_object_q:
  bounded_interval64_valid interval ==>
  bounded_interval64_covers_object_q interval
    (bounded_interval64_object_q_cv interval)
Proof
  `!x y:int. x <= y ==>
      x * 1099511627776 <= y * 1099511627776` by intLib.ARITH_TAC
  >> Cases_on `interval`
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def,
        compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
  >> metis_tac []
QED

val _ = export_theory ();
