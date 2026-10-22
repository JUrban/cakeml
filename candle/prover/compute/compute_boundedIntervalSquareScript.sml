(*****************************************************************************
 * Checked directed square for stored fixed-scale intervals.
 *
 * Generic mixed-sign multiplication encloses x*x but loses the dependency
 * between its two arguments and can produce a negative lower endpoint.  A
 * true square of an interval crossing zero has exact lower endpoint zero and
 * upper endpoint max(lower^2,upper^2).  The one-sign cases retain the
 * established multiplication path.
 *****************************************************************************)
Theory compute_boundedIntervalSquare
Ancestors
  compute_boundedInterval
Libs
  bossLib preamble wordsLib

Definition bounded_interval64_square_unchecked_def:
  bounded_interval64_square_unchecked source =
    case source of
    | BoundedInterval64 lower upper =>
      if bounded_signed64_nonnegative lower ∨
         bounded_signed64_nonpositive upper
      then bounded_interval64_mul_unchecked source source
      else
        case bounded_scaled_mul_ceil64 lower lower of
        | NONE => NONE
        | SOME lower_square =>
          case bounded_scaled_mul_ceil64 upper upper of
          | NONE => NONE
          | SOME upper_square =>
              SOME
                (BoundedInterval64 (BoundedSigned64 F 0w)
                  (bounded_signed64_max lower_square upper_square))
End

Definition bounded_interval64_square_def:
  bounded_interval64_square source =
    if bounded_interval64_valid source then
      bounded_interval64_square_unchecked source
    else NONE
End

Theorem bounded_interval64_square_rejects_invalid:
  ¬bounded_interval64_valid source ⇒
  bounded_interval64_square source = NONE
Proof
  rw [bounded_interval64_square_def]
QED

Theorem bounded_interval64_square_crossing_shape:
  bounded_interval64_valid (BoundedInterval64 lower upper) ∧
  ¬bounded_signed64_nonnegative lower ∧
  ¬bounded_signed64_nonpositive upper ∧
  bounded_interval64_square (BoundedInterval64 lower upper) = SOME result ⇒
  ∃upper_square.
    result = BoundedInterval64 (BoundedSigned64 F 0w) upper_square ∧
    bounded_signed64_normalized upper_square
Proof
  rw [bounded_interval64_square_def,
      bounded_interval64_square_unchecked_def]
  >> Cases_on `bounded_scaled_mul_ceil64 lower lower`
  >> Cases_on `bounded_scaled_mul_ceil64 upper upper`
  >> gvs []
  >> imp_res_tac bounded_scaled_mul_ceil64_normalized
  >> simp
       [compute_boundedSignedEndpointTheory.bounded_signed64_max_def]
  >> every_case_tac
  >> fs []
QED

Theorem bounded_interval64_square_closed_tests:
  let scale = 1099511627776w in
  let n2 = BoundedSigned64 T (2w * scale) in
  let p3 = BoundedSigned64 F (3w * scale) in
  let p4 = BoundedSigned64 F (4w * scale) in
  let p9 = BoundedSigned64 F (9w * scale) in
  let genuine_crossing =
    BoundedInterval64 (BoundedSigned64 T 33939760703w)
      (BoundedSigned64 F 372457639893w) in
  bounded_interval64_square (BoundedInterval64 n2 p3) =
    SOME (BoundedInterval64 (BoundedSigned64 F 0w) p9) ∧
  bounded_interval64_square (BoundedInterval64 n2 n2) =
    SOME (BoundedInterval64 p4 p4) ∧
  bounded_interval64_square genuine_crossing =
    SOME
      (BoundedInterval64 (BoundedSigned64 F 0w)
        (BoundedSigned64 F 126169373757w))
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
