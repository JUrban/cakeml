(*****************************************************************************
 * Representation invariants for the source-faithful absolute-upper helper.
 *****************************************************************************)
Theory compute_boundedPackedObjectPrimitiveAbsContract
Ancestors
  compute_boundedPackedObjectPrimitiveAbsEval
Libs
  bossLib preamble

Theorem bounded_packed_q_max_encoded:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right ==>
  bounded_object_q_encoded (bounded_object_q_max_cv left right)
Proof
  rw
    [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max_cv_def]
QED

Theorem bounded_packed_q_source_abs_upper_encoded:
  bounded_packed_q_interval_encoded object_interval ==>
  bounded_object_q_encoded
    (bounded_packed_q_source_abs_upper_cv object_interval)
Proof
  rw
    [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> simp
       [compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_q_source_abs_upper_cv_def]
  >> irule bounded_packed_q_max_encoded
  >> simp
       [compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_q_neg_encoded]
QED

val _ = export_theory ();
