(*****************************************************************************
 * Shape-safe list operations for the fixed-width nonlinear jet executor.
 *
 * Gradients and compact symmetric Hessians are represented by fixed-length
 * lists at the program boundary (six and twenty-one entries respectively).
 * These total helpers make every shape mismatch and arithmetic overflow an
 * explicit NONE.  They are deliberately independent of case16594 and are
 * reusable by the complete checker and later nonlinear families.
 *****************************************************************************)
Theory compute_boundedIntervalList
Ancestors
  compute_boundedIntervalAdd compute_boundedInterval
Libs
  bossLib preamble

Definition bounded_interval64_zero_def:
  bounded_interval64_zero =
    BoundedInterval64
      (BoundedSigned64 F 0w) (BoundedSigned64 F 0w)
End

Definition bounded_interval64_is_zero_def:
  bounded_interval64_is_zero
      (BoundedInterval64
        (BoundedSigned64 lower_negative lower_magnitude)
        (BoundedSigned64 upper_negative upper_magnitude)) ⇔
    lower_magnitude = 0w ∧ upper_magnitude = 0w
End

Definition bounded_interval64_list_valid_def:
  bounded_interval64_list_valid values ⇔
    EVERY bounded_interval64_valid values
End

Definition bounded_interval64_list_neg_def:
  bounded_interval64_list_neg values =
    MAP bounded_interval64_neg values
End

Definition bounded_interval64_list_add_def:
  bounded_interval64_list_add [] [] = SOME [] ∧
  bounded_interval64_list_add [] (_::_) = NONE ∧
  bounded_interval64_list_add (_::_) [] = NONE ∧
  bounded_interval64_list_add (left::left_rest) (right::right_rest) =
    case bounded_interval64_add left right of
    | NONE => NONE
    | SOME value =>
        case bounded_interval64_list_add left_rest right_rest of
        | NONE => NONE
        | SOME rest => SOME (value::rest)
End

Definition bounded_interval64_list_scale_def:
  bounded_interval64_list_scale scalar [] = SOME [] ∧
  bounded_interval64_list_scale scalar (value::rest) =
    case bounded_interval64_mul scalar value of
    | NONE => NONE
    | SOME product =>
        case bounded_interval64_list_scale scalar rest of
        | NONE => NONE
        | SOME products => SOME (product::products)
End

Definition bounded_interval64_list_pairwise_mul_def:
  bounded_interval64_list_pairwise_mul [] [] = SOME [] ∧
  bounded_interval64_list_pairwise_mul [] (_::_) = NONE ∧
  bounded_interval64_list_pairwise_mul (_::_) [] = NONE ∧
  bounded_interval64_list_pairwise_mul
      (left::left_rest) (right::right_rest) =
    case bounded_interval64_mul left right of
    | NONE => NONE
    | SOME value =>
        case bounded_interval64_list_pairwise_mul left_rest right_rest of
        | NONE => NONE
        | SOME rest => SOME (value::rest)
End

Theorem bounded_interval64_zero_valid:
  bounded_interval64_valid bounded_interval64_zero ∧
  bounded_interval64_is_zero bounded_interval64_zero
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_interval64_list_neg_length:
  LENGTH (bounded_interval64_list_neg values) = LENGTH values
Proof
  simp [bounded_interval64_list_neg_def]
QED

Theorem bounded_interval64_list_neg_valid:
  bounded_interval64_list_valid values ⇒
  bounded_interval64_list_valid (bounded_interval64_list_neg values)
Proof
  rw [bounded_interval64_list_valid_def,
      bounded_interval64_list_neg_def, listTheory.EVERY_MAP]
  >> irule listTheory.EVERY_MONOTONIC
  >> qexists_tac `bounded_interval64_valid`
  >> rw []
  >> irule bounded_interval64_neg_valid
  >> fs []
QED

Theorem bounded_interval64_list_add_length:
  ∀left right result.
    bounded_interval64_list_add left right = SOME result ⇒
    LENGTH left = LENGTH right ∧ LENGTH result = LENGTH left
Proof
  Induct
  >> Cases_on `right`
  >> simp [bounded_interval64_list_add_def]
  >> rw []
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> fs []
QED

Theorem bounded_interval64_list_add_valid:
  ∀left right result.
    bounded_interval64_list_valid left ∧
    bounded_interval64_list_valid right ∧
    bounded_interval64_list_add left right = SOME result ⇒
    bounded_interval64_list_valid result
Proof
  Induct
  >> Cases_on `right`
  >> rw [bounded_interval64_list_valid_def,
         bounded_interval64_list_add_def]
  >> every_case_tac
  >> gvs []
  >> conj_tac
  >- (imp_res_tac bounded_interval64_add_value >> fs [])
  >> qpat_x_assum `∀right result. _`
       (qspecl_then [`t`, `x`] mp_tac)
  >> simp [bounded_interval64_list_valid_def]
QED

Theorem bounded_interval64_list_scale_length:
  ∀values scalar result.
    bounded_interval64_list_scale scalar values = SOME result ⇒
    LENGTH result = LENGTH values
Proof
  Induct
  >> rw [bounded_interval64_list_scale_def]
  >> Cases_on `bounded_interval64_mul scalar h`
  >> Cases_on `bounded_interval64_list_scale scalar values`
  >> gvs []
  >> res_tac
  >> fs []
QED

Theorem bounded_interval64_list_pairwise_mul_length:
  ∀left right result.
    bounded_interval64_list_pairwise_mul left right = SOME result ⇒
    LENGTH left = LENGTH right ∧ LENGTH result = LENGTH left
Proof
  Induct
  >> Cases_on `right`
  >> simp [bounded_interval64_list_pairwise_mul_def]
  >> rw []
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> fs []
QED

Theorem bounded_interval64_list_closed_tests:
  let one = BoundedInterval64
    (BoundedSigned64 F 1099511627776w)
    (BoundedSigned64 F 1099511627776w) in
  let minus_one = BoundedInterval64
    (BoundedSigned64 T 1099511627776w)
    (BoundedSigned64 T 1099511627776w) in
  bounded_interval64_list_neg [one;minus_one] = [minus_one;one] ∧
  bounded_interval64_list_add [one;minus_one] [minus_one;one] =
    SOME [bounded_interval64_zero;bounded_interval64_zero] ∧
  bounded_interval64_list_add [one] [one;one] = NONE ∧
  bounded_interval64_list_scale one [one;minus_one] =
    SOME [one;minus_one] ∧
  bounded_interval64_list_pairwise_mul [one;minus_one] [one;minus_one] =
    SOME [one;one]
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
