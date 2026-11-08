(*****************************************************************************
 * Semantic input contract for the first genuine atan instruction.
 *
 * The producer recompletes a constant Taylor state before atan, so its value
 * bound is generally a different rational encoding of its center.  The
 * authenticated box input must enclose that value, not merely match bytes.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAtanInputContract
Ancestors
  compute_boundedCase16594ObjectSource8SemanticShape
  compute_boundedObjectIntervalEnclosesEquivalence
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_source8_center_encoded:
  bounded_object_q_interval_encoded
    (bounded_object_q_taylor_center bounded_case16594_object_source8_result)
Proof
  mp_tac bounded_case16594_object_source8_semantic_valid
  >> Cases_on `bounded_case16594_object_source8_result`
  >> simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def]
  >> metis_tac
       [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded]
QED

Theorem bounded_case16594_object_source8_value_bound_encoded:
  bounded_object_q_interval_encoded
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source8_result)
Proof
  mp_tac bounded_case16594_object_source8_semantic_valid
  >> Cases_on `bounded_case16594_object_source8_result`
  >> simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_value_bound_def]
  >> metis_tac
       [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded]
QED

Theorem bounded_case16594_object_atan_center_input_encoded:
  bounded_object_q_interval_encoded
    bounded_case16594_object_cell0_atan_center_input_cv
Proof
  rw
    [compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_input_cv_def,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> EVAL_TAC
  >> simp []
QED

Theorem bounded_case16594_object_source8_value_bound_certificate_encloses:
  bounded_object_q_interval_encloses
    bounded_case16594_object_cell0_atan_box_input_cv
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source8_result)
Proof
  rewrite_tac
    [compute_boundedCase16594ObjectAtanCertificateRelationsTheory.bounded_case16594_object_atan_inputs_identical]
  >> irule bounded_object_q_interval_encloses_equiv_inner
  >> simp
       [bounded_case16594_object_atan_center_input_encoded,
        bounded_case16594_object_source8_value_bound_encoded]
  >> qexists_tac
       `bounded_object_q_taylor_center
          bounded_case16594_object_source8_result`
  >> simp
       [bounded_case16594_object_source8_center_encoded,
        compute_boundedCase16594ObjectSource8SemanticShapeTheory.bounded_case16594_object_source8_value_bound_center_equiv,
        compute_boundedCase16594ObjectSource8SemanticShapeTheory.bounded_case16594_object_source8_center_certificate_encloses]
QED

val _ = export_theory ();
