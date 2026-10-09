(*****************************************************************************
 * Exact negation and checked addition for stored fixed-scale intervals.
 *
 * These operations contain no rounding: endpoint negation reverses the
 * bounds, while addition combines corresponding bounds through the checked
 * signed-endpoint accumulator.  External invalid intervals and endpoint
 * overflow fail closed.
 *****************************************************************************)
Theory compute_boundedIntervalAdd
Ancestors
  compute_boundedInterval compute_boundedSignedEndpointAdd
  compute_boundedSignedEndpoint
Libs
  bossLib intLib

Definition bounded_interval64_neg_def:
  bounded_interval64_neg (BoundedInterval64 lower upper) =
    BoundedInterval64
      (bounded_signed64_neg upper)
      (bounded_signed64_neg lower)
End

Definition bounded_interval64_add_unchecked_def:
  bounded_interval64_add_unchecked
      (BoundedInterval64 left_lower left_upper)
      (BoundedInterval64 right_lower right_upper) =
    case bounded_signed64_add left_lower right_lower of
    | NONE => NONE
    | SOME lower =>
        case bounded_signed64_add left_upper right_upper of
        | NONE => NONE
        | SOME upper => SOME (BoundedInterval64 lower upper)
End

Definition bounded_interval64_add_def:
  bounded_interval64_add left right =
    if bounded_interval64_valid left ∧ bounded_interval64_valid right then
      bounded_interval64_add_unchecked left right
    else NONE
End

Theorem bounded_interval64_neg_valid:
  bounded_interval64_valid source ⇒
  bounded_interval64_valid (bounded_interval64_neg source)
Proof
  Cases_on `source`
  >> rw [bounded_interval64_neg_def, bounded_interval64_valid_def]
  >> fs [bounded_signed64_le_correct,
         bounded_signed64_neg_value,
         bounded_signed64_neg_normalized]
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_neg_value:
  bounded_signed64_to_int
      (bounded_interval64_lower (bounded_interval64_neg source)) =
    -bounded_signed64_to_int (bounded_interval64_upper source) ∧
  bounded_signed64_to_int
      (bounded_interval64_upper (bounded_interval64_neg source)) =
    -bounded_signed64_to_int (bounded_interval64_lower source)
Proof
  Cases_on `source`
  >> simp [bounded_interval64_neg_def,
           bounded_interval64_lower_def, bounded_interval64_upper_def,
           bounded_signed64_neg_value]
QED

Theorem bounded_interval64_add_unchecked_endpoints:
  bounded_interval64_add_unchecked left right = SOME result ⇒
  bounded_signed64_normalized (bounded_interval64_lower result) ∧
  bounded_signed64_normalized (bounded_interval64_upper result) ∧
  bounded_signed64_to_int (bounded_interval64_lower result) =
    bounded_signed64_to_int (bounded_interval64_lower left) +
    bounded_signed64_to_int (bounded_interval64_lower right) ∧
  bounded_signed64_to_int (bounded_interval64_upper result) =
    bounded_signed64_to_int (bounded_interval64_upper left) +
    bounded_signed64_to_int (bounded_interval64_upper right)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `result`
  >> rename1
       `bounded_interval64_add_unchecked
          (BoundedInterval64 ll lu) (BoundedInterval64 rl ru) =
        SOME (BoundedInterval64 ol ou)`
  >> rw [bounded_interval64_add_unchecked_def]
  >> Cases_on `bounded_signed64_add ll rl`
  >> Cases_on `bounded_signed64_add lu ru`
  >> gvs [bounded_interval64_lower_def, bounded_interval64_upper_def]
  >> imp_res_tac bounded_signed64_add_value
  >> fs []
QED

Theorem bounded_interval64_add_unchecked_valid:
  bounded_interval64_valid left ∧ bounded_interval64_valid right ∧
  bounded_interval64_add_unchecked left right = SOME result ⇒
  bounded_interval64_valid result
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `result`
  >> strip_tac
  >> imp_res_tac bounded_interval64_add_unchecked_endpoints
  >> fs [bounded_interval64_valid_def,
         bounded_interval64_lower_def, bounded_interval64_upper_def,
         bounded_signed64_le_correct]
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_add_value:
  bounded_interval64_add left right = SOME result ⇒
  bounded_interval64_valid result ∧
  bounded_signed64_to_int (bounded_interval64_lower result) =
    bounded_signed64_to_int (bounded_interval64_lower left) +
    bounded_signed64_to_int (bounded_interval64_lower right) ∧
  bounded_signed64_to_int (bounded_interval64_upper result) =
    bounded_signed64_to_int (bounded_interval64_upper left) +
    bounded_signed64_to_int (bounded_interval64_upper right)
Proof
  rw [bounded_interval64_add_def]
  >> imp_res_tac bounded_interval64_add_unchecked_endpoints
  >> metis_tac [bounded_interval64_add_unchecked_valid]
QED

Theorem bounded_interval64_neg_contains_int:
  bounded_interval64_contains_int source value ⇒
  bounded_interval64_contains_int
    (bounded_interval64_neg source) (-value)
Proof
  Cases_on `source`
  >> simp [bounded_interval64_contains_int_def,
           bounded_interval64_neg_def,
           bounded_signed64_neg_value]
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_add_contains_int:
  bounded_interval64_contains_int left left_value ∧
  bounded_interval64_contains_int right right_value ∧
  bounded_interval64_add left right = SOME result ⇒
  bounded_interval64_contains_int result (left_value + right_value)
Proof
  strip_tac
  >> imp_res_tac bounded_interval64_add_value
  >> Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `result`
  >> fs [bounded_interval64_contains_int_def,
         bounded_interval64_lower_def,
         bounded_interval64_upper_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_add_rejects_invalid:
  ¬bounded_interval64_valid left ∨ ¬bounded_interval64_valid right ⇒
  bounded_interval64_add left right = NONE
Proof
  rw [bounded_interval64_add_def]
  >> fs []
QED

Theorem bounded_interval64_add_closed_tests:
  bounded_interval64_neg
    (BoundedInterval64
      (BoundedSigned64 T 7w) (BoundedSigned64 F 3w)) =
    BoundedInterval64
      (BoundedSigned64 T 3w) (BoundedSigned64 F 7w) ∧
  bounded_interval64_add
    (BoundedInterval64
      (BoundedSigned64 T 7w) (BoundedSigned64 F 3w))
    (BoundedInterval64
      (BoundedSigned64 F 2w) (BoundedSigned64 F 5w)) =
    SOME
      (BoundedInterval64
        (BoundedSigned64 T 5w) (BoundedSigned64 F 8w)) ∧
  bounded_interval64_add
    (BoundedInterval64
      (BoundedSigned64 F (-1w)) (BoundedSigned64 F (-1w)))
    (BoundedInterval64
      (BoundedSigned64 F 1w) (BoundedSigned64 F 1w)) = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
