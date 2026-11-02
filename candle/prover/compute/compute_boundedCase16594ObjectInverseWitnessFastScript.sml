(*****************************************************************************
 * Genuine case-16594 object inverse-derivative fast-witness gate.
 *
 * The reciprocal interval below is the exact first inverse payload extracted
 * by compute_boundedCase16594PackedSourceCell0InverseDiagnostic.  Keeping the
 * small payload local avoids rebuilding or mixing the stale parent theory
 * graph that produced the frozen diagnostic.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectInverseWitnessFast
Ancestors
  compute_boundedObjectIntervalInverseWitnessFast
Libs
  bossLib preamble

Definition bounded_case16594_first_inverse_reciprocal_def:
  bounded_case16594_first_inverse_reciprocal =
    Pair
      (Pair (Pair (Num 583091134019) (Num 0)) (Num 549755813887))
      (Pair (Pair (Num 291561029025) (Num 0)) (Num 274877906943))
End

Definition bounded_case16594_first_inverse_derivative_def:
  bounded_case16594_first_inverse_derivative =
    Pair
      (Pair
        (Pair (Num 0) (Num 85007833646116892450625))
        (Num 75557863725914323419135))
      (Pair
        (Pair (Num 0) (Num 339995270571563419092361))
        (Num 302231454903657293676543))
End

Theorem bounded_case16594_first_inverse_reciprocal_encoded:
  bounded_packed_q_interval_encoded
    bounded_case16594_first_inverse_reciprocal
Proof
  simp
    [bounded_case16594_first_inverse_reciprocal_def,
     compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def,
     compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
QED

Theorem bounded_case16594_first_inverse_derivative_exact:
  bounded_case16594_first_inverse_derivative =
    bounded_object_q_interval_neg_cv
      (bounded_object_q_interval_mul_cv
        bounded_case16594_first_inverse_reciprocal
        bounded_case16594_first_inverse_reciprocal)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_first_inverse_derivative_fast_hit:
  bounded_object_interval_inverse_witness_fast_eval
    bounded_object_interval_inverse_witness_ceqs
    (App «candle_cv_q_packed_object_inverse_derivative_witness»
      [from_cv bounded_case16594_first_inverse_reciprocal;
       from_cv bounded_case16594_first_inverse_derivative]) =
    SOME (Num 1)
Proof
  rewrite_tac [bounded_case16594_first_inverse_derivative_exact]
  >> irule bounded_object_interval_inverse_witness_fast_eval_hit
  >> ACCEPT_TAC bounded_case16594_first_inverse_reciprocal_encoded
QED

Theorem bounded_case16594_first_inverse_derivative_ordinary_eval:
  compute_eval compute_default_clock
      bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_packed_object_inverse_derivative_witness»
        [from_cv bounded_case16594_first_inverse_reciprocal;
         from_cv bounded_case16594_first_inverse_derivative])
      (refs:hol_refs) =
    (M_success (from_cv (Num 1)),refs)
Proof
  rewrite_tac [bounded_case16594_first_inverse_derivative_exact]
  >> irule object_inverse_witness_entry_eval
  >> simp [bounded_case16594_first_inverse_reciprocal_encoded]
QED

Theorem bounded_case16594_first_inverse_derivative_changed_rejected:
  bounded_object_interval_inverse_witness_fast_eval
    bounded_object_interval_inverse_witness_ceqs
    (App «candle_cv_q_packed_object_inverse_derivative_witness»
      [from_cv bounded_case16594_first_inverse_reciprocal;
       from_cv (Num 0)]) = NONE
Proof
  irule
    bounded_object_interval_inverse_witness_fast_eval_rejects_changed_candidate
  >> EVAL_TAC
QED

val _ = export_theory ();
