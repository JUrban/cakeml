(*****************************************************************************
 * Checked decimal fixed-scale arctangent data instruction.
 *
 * This is the scale-10^12 counterpart of compute_boundedAtan.  Its interval
 * polynomial and reciprocal certificates use the same decimal arithmetic as
 * the authenticated object-checker route.  General real-analytic refinement
 * of the arctangent kernel remains a shared release obligation.
 *****************************************************************************)
Theory compute_boundedAtanDecimal
Ancestors
  compute_boundedCertificateDecimal compute_boundedIntervalDecimal
  compute_boundedIntervalAdd
Libs
  bossLib preamble

Definition bounded_atan_scale_decimal_def:
  bounded_atan_scale_decimal = (1000000000000w:word64)
End

Definition bounded_atan_one_decimal_def:
  bounded_atan_one_decimal =
    BoundedInterval64
      (BoundedSigned64 F 1000000000000w)
      (BoundedSigned64 F 1000000000000w)
End

Definition bounded_atan_pi_half_decimal_def:
  bounded_atan_pi_half_decimal =
    BoundedInterval64
      (BoundedSigned64 F 1570796326794w)
      (BoundedSigned64 F 1570796326795w)
End

Definition bounded_atan_pos_third_decimal_def:
  bounded_atan_pos_third_decimal =
    BoundedInterval64
      (BoundedSigned64 F 333333333333w)
      (BoundedSigned64 F 333333333334w)
End

Definition bounded_atan_neg_third_decimal_def:
  bounded_atan_neg_third_decimal =
    bounded_interval64_neg bounded_atan_pos_third_decimal
End

Definition bounded_atan_pos_fifth_decimal_def:
  bounded_atan_pos_fifth_decimal =
    BoundedInterval64
      (BoundedSigned64 F 200000000000w)
      (BoundedSigned64 F 200000000000w)
End

Definition bounded_atan_neg_seventh_decimal_def:
  bounded_atan_neg_seventh_decimal =
    BoundedInterval64
      (BoundedSigned64 T 142857142858w)
      (BoundedSigned64 T 142857142857w)
End

Definition bounded_atan_pos_ninth_decimal_def:
  bounded_atan_pos_ninth_decimal =
    BoundedInterval64
      (BoundedSigned64 F 111111111111w)
      (BoundedSigned64 F 111111111112w)
End

Definition bounded_atan_neg_eleventh_decimal_def:
  bounded_atan_neg_eleventh_decimal =
    BoundedInterval64
      (BoundedSigned64 T 90909090910w)
      (BoundedSigned64 T 90909090909w)
End

Definition bounded_atan_pos_thirteenth_decimal_def:
  bounded_atan_pos_thirteenth_decimal =
    BoundedInterval64
      (BoundedSigned64 F 76923076923w)
      (BoundedSigned64 F 76923076924w)
End

Definition bounded_interval64_mul_add_decimal_def:
  bounded_interval64_mul_add_decimal scalar accumulator addend =
    case bounded_interval64_mul_decimal scalar accumulator of
    | NONE => NONE
    | SOME product => bounded_interval64_add addend product
End

Definition bounded_interval64_atan_pos_lower_decimal_def:
  bounded_interval64_atan_pos_lower_decimal magnitude =
    let point = BoundedInterval64
      (BoundedSigned64 F magnitude) (BoundedSigned64 F magnitude) in
    case bounded_interval64_mul_decimal point point of
    | NONE => NONE
    | SOME square =>
      case bounded_interval64_mul_add_decimal square
        bounded_atan_neg_eleventh_decimal bounded_atan_pos_ninth_decimal of
      | NONE => NONE
      | SOME step9 =>
        case bounded_interval64_mul_add_decimal square step9
          bounded_atan_neg_seventh_decimal of
        | NONE => NONE
        | SOME step7 =>
          case bounded_interval64_mul_add_decimal square step7
            bounded_atan_pos_fifth_decimal of
          | NONE => NONE
          | SOME step5 =>
            case bounded_interval64_mul_add_decimal square step5
              bounded_atan_neg_third_decimal of
            | NONE => NONE
            | SOME step3 =>
              case bounded_interval64_mul_add_decimal square step3
                bounded_atan_one_decimal of
              | NONE => NONE
              | SOME body => bounded_interval64_mul_decimal point body
End

Definition bounded_interval64_atan_pos_upper_decimal_def:
  bounded_interval64_atan_pos_upper_decimal magnitude =
    let point = BoundedInterval64
      (BoundedSigned64 F magnitude) (BoundedSigned64 F magnitude) in
    case bounded_interval64_mul_decimal point point of
    | NONE => NONE
    | SOME square =>
      case bounded_interval64_mul_add_decimal square
        bounded_atan_pos_thirteenth_decimal
        bounded_atan_neg_eleventh_decimal of
      | NONE => NONE
      | SOME step11 =>
        case bounded_interval64_mul_add_decimal square step11
          bounded_atan_pos_ninth_decimal of
        | NONE => NONE
        | SOME step9 =>
          case bounded_interval64_mul_add_decimal square step9
            bounded_atan_neg_seventh_decimal of
          | NONE => NONE
          | SOME step7 =>
            case bounded_interval64_mul_add_decimal square step7
              bounded_atan_pos_fifth_decimal of
            | NONE => NONE
            | SOME step5 =>
              case bounded_interval64_mul_add_decimal square step5
                bounded_atan_neg_third_decimal of
              | NONE => NONE
              | SOME step3 =>
                case bounded_interval64_mul_add_decimal square step3
                  bounded_atan_one_decimal of
                | NONE => NONE
                | SOME body => bounded_interval64_mul_decimal point body
End

Definition bounded_interval64_atan_unit_lower_decimal_def:
  bounded_interval64_atan_unit_lower_decimal endpoint =
    let magnitude = bounded_signed64_magnitude endpoint in
    if ¬word_lo magnitude bounded_atan_scale_decimal then NONE
    else if bounded_signed64_effective_negative endpoint then
      case bounded_interval64_atan_pos_upper_decimal magnitude of
      | NONE => NONE
      | SOME enclosure =>
          SOME (bounded_signed64_neg (bounded_interval64_upper enclosure))
    else
      case bounded_interval64_atan_pos_lower_decimal magnitude of
      | NONE => NONE
      | SOME enclosure => SOME (bounded_interval64_lower enclosure)
End

Definition bounded_interval64_atan_unit_upper_decimal_def:
  bounded_interval64_atan_unit_upper_decimal endpoint =
    let magnitude = bounded_signed64_magnitude endpoint in
    if ¬word_lo magnitude bounded_atan_scale_decimal then NONE
    else if bounded_signed64_effective_negative endpoint then
      case bounded_interval64_atan_pos_lower_decimal magnitude of
      | NONE => NONE
      | SOME enclosure =>
          SOME (bounded_signed64_neg (bounded_interval64_lower enclosure))
    else
      case bounded_interval64_atan_pos_upper_decimal magnitude of
      | NONE => NONE
      | SOME enclosure => SOME (bounded_interval64_upper enclosure)
End

Definition bounded_interval64_atan_unit_decimal_def:
  bounded_interval64_atan_unit_decimal input =
    if ¬bounded_interval64_valid input then NONE
    else
      case bounded_interval64_atan_unit_lower_decimal
        (bounded_interval64_lower input) of
      | NONE => NONE
      | SOME lower =>
        case bounded_interval64_atan_unit_upper_decimal
          (bounded_interval64_upper input) of
        | NONE => NONE
        | SOME upper =>
            let result = BoundedInterval64 lower upper in
            if bounded_interval64_valid result then SOME result else NONE
End

Definition bounded_interval64_atan_range_point_decimal_def:
  bounded_interval64_atan_range_point_decimal endpoint reciprocal =
    let magnitude = bounded_signed64_magnitude endpoint in
    if word_lo magnitude bounded_atan_scale_decimal then
      if reciprocal = NONE then
        bounded_interval64_atan_unit_decimal
          (BoundedInterval64 endpoint endpoint)
      else NONE
    else if magnitude = bounded_atan_scale_decimal then NONE
    else
      case reciprocal of
      | NONE => NONE
      | SOME reciprocal_interval =>
          if ¬bounded_interval64_inv_certificate_decimal
            (BoundedInterval64 endpoint endpoint) reciprocal_interval
          then NONE
          else
            let reduced =
              if bounded_signed64_effective_negative endpoint then
                bounded_interval64_neg reciprocal_interval
              else reciprocal_interval in
            case bounded_interval64_atan_unit_decimal reduced of
            | NONE => NONE
            | SOME reduced_atan =>
                if bounded_signed64_effective_negative endpoint then
                  bounded_interval64_add reduced_atan
                    (bounded_interval64_neg bounded_atan_pi_half_decimal)
                else
                  bounded_interval64_add bounded_atan_pi_half_decimal
                    (bounded_interval64_neg reduced_atan)
End

Definition bounded_interval64_atan_range_decimal_def:
  bounded_interval64_atan_range_decimal input lower_reciprocal
      upper_reciprocal =
    if ¬bounded_interval64_valid input then NONE
    else
      case bounded_interval64_atan_range_point_decimal
        (bounded_interval64_lower input) lower_reciprocal of
      | NONE => NONE
      | SOME lower_enclosure =>
        case bounded_interval64_atan_range_point_decimal
          (bounded_interval64_upper input) upper_reciprocal of
        | NONE => NONE
        | SOME upper_enclosure =>
            let result = BoundedInterval64
              (bounded_interval64_lower lower_enclosure)
              (bounded_interval64_upper upper_enclosure) in
            if bounded_interval64_valid result then SOME result else NONE
End

Theorem bounded_interval64_atan_range_decimal_some:
  bounded_interval64_atan_range_decimal input lower_reciprocal
      upper_reciprocal = SOME result ==>
  bounded_interval64_valid result
Proof
  rw [bounded_interval64_atan_range_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_interval64_atan_range_decimal_rejects_invalid:
  ¬bounded_interval64_valid input ==>
  bounded_interval64_atan_range_decimal input lower_reciprocal
    upper_reciprocal = NONE
Proof
  rw [bounded_interval64_atan_range_decimal_def]
QED

Theorem bounded_interval64_atan_decimal_closed_tests:
  bounded_interval64_atan_range_decimal
    (BoundedInterval64
      (BoundedSigned64 F 0w) (BoundedSigned64 F 0w))
    NONE NONE =
      SOME (BoundedInterval64
        (BoundedSigned64 F 0w) (BoundedSigned64 F 0w)) /\
  bounded_interval64_atan_range_point_decimal
    (BoundedSigned64 F 1000000000000w) NONE = NONE /\
  bounded_interval64_atan_range_point_decimal
    (BoundedSigned64 F 2000000000000w) NONE = NONE /\
  (case bounded_interval64_atan_range_point_decimal
      (BoundedSigned64 F 2000000000000w)
      (SOME (BoundedInterval64
        (BoundedSigned64 F 500000000000w)
        (BoundedSigned64 F 500000000000w))) of
   | NONE => F
   | SOME result => bounded_interval64_valid result) /\
  bounded_interval64_atan_range_decimal
    (BoundedInterval64
      (BoundedSigned64 F 3w) (BoundedSigned64 T 3w))
    NONE NONE = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
