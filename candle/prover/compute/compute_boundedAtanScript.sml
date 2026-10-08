(*****************************************************************************
 * Checked fixed-scale arctangent data instruction.
 *
 * The alternating polynomial is evaluated with the existing outward interval
 * operations on (-1,1).  Endpoints outside that range use the standard
 * reciprocal identities, but only after an externally supplied reciprocal
 * enclosure passes the exact certificate checker.  Exact +/-1 remains
 * fail-closed until a separate pi/4 boundary is added.
 *
 * This theory establishes the executable and fail-closed data boundary.
 * Its general real-analytic enclosure refinement is an explicit release
 * obligation, shared by every source expression rather than proved per case.
 *****************************************************************************)
Theory compute_boundedAtan
Ancestors
  compute_boundedReciprocalCertificate compute_boundedIntervalAdd
Libs
  bossLib preamble

Definition bounded_atan_word64_def:
  bounded_atan_word64 (high:word64) low = (high << 32) + low
End

Definition bounded_atan_scale_def:
  bounded_atan_scale = bounded_atan_word64 256w 0w
End

Definition bounded_atan_one_def:
  bounded_atan_one =
    BoundedInterval64
      (BoundedSigned64 F (bounded_atan_word64 256w 0w))
      (BoundedSigned64 F (bounded_atan_word64 256w 0w))
End

Definition bounded_atan_pi_half_def:
  bounded_atan_pi_half =
    BoundedInterval64
      (BoundedSigned64 F (bounded_atan_word64 402w 531973120w))
      (BoundedSigned64 F (bounded_atan_word64 402w 531973376w))
End

Definition bounded_atan_pos_third_def:
  bounded_atan_pos_third =
    BoundedInterval64
      (BoundedSigned64 F (bounded_atan_word64 85w 1431655765w))
      (BoundedSigned64 F (bounded_atan_word64 85w 1431655766w))
End

Definition bounded_atan_neg_third_def:
  bounded_atan_neg_third = bounded_interval64_neg bounded_atan_pos_third
End

Definition bounded_atan_pos_fifth_def:
  bounded_atan_pos_fifth =
    BoundedInterval64
      (BoundedSigned64 F (bounded_atan_word64 51w 858993459w))
      (BoundedSigned64 F (bounded_atan_word64 51w 858993460w))
End

Definition bounded_atan_neg_seventh_def:
  bounded_atan_neg_seventh =
    BoundedInterval64
      (BoundedSigned64 T (bounded_atan_word64 36w 2454267027w))
      (BoundedSigned64 T (bounded_atan_word64 36w 2454267026w))
End

Definition bounded_atan_pos_ninth_def:
  bounded_atan_pos_ninth =
    BoundedInterval64
      (BoundedSigned64 F (bounded_atan_word64 28w 1908874353w))
      (BoundedSigned64 F (bounded_atan_word64 28w 1908874354w))
End

Definition bounded_atan_neg_eleventh_def:
  bounded_atan_neg_eleventh =
    BoundedInterval64
      (BoundedSigned64 T (bounded_atan_word64 23w 1171354718w))
      (BoundedSigned64 T (bounded_atan_word64 23w 1171354717w))
End

Definition bounded_atan_pos_thirteenth_def:
  bounded_atan_pos_thirteenth =
    BoundedInterval64
      (BoundedSigned64 F (bounded_atan_word64 19w 2973438897w))
      (BoundedSigned64 F (bounded_atan_word64 19w 2973438898w))
End

Definition bounded_interval64_mul_add_def:
  bounded_interval64_mul_add scalar accumulator addend =
    case bounded_interval64_mul scalar accumulator of
    | NONE => NONE
    | SOME product => bounded_interval64_add addend product
End

Definition bounded_interval64_atan_pos_lower_def:
  bounded_interval64_atan_pos_lower magnitude =
    let point = BoundedInterval64
      (BoundedSigned64 F magnitude) (BoundedSigned64 F magnitude) in
    case bounded_interval64_mul point point of
    | NONE => NONE
    | SOME square =>
      case bounded_interval64_mul_add square
        bounded_atan_neg_eleventh bounded_atan_pos_ninth of
      | NONE => NONE
      | SOME step9 =>
        case bounded_interval64_mul_add square step9
          bounded_atan_neg_seventh of
        | NONE => NONE
        | SOME step7 =>
          case bounded_interval64_mul_add square step7
            bounded_atan_pos_fifth of
          | NONE => NONE
          | SOME step5 =>
            case bounded_interval64_mul_add square step5
              bounded_atan_neg_third of
            | NONE => NONE
            | SOME step3 =>
              case bounded_interval64_mul_add square step3
                bounded_atan_one of
              | NONE => NONE
              | SOME body => bounded_interval64_mul point body
End

Definition bounded_interval64_atan_pos_upper_def:
  bounded_interval64_atan_pos_upper magnitude =
    let point = BoundedInterval64
      (BoundedSigned64 F magnitude) (BoundedSigned64 F magnitude) in
    case bounded_interval64_mul point point of
    | NONE => NONE
    | SOME square =>
      case bounded_interval64_mul_add square
        bounded_atan_pos_thirteenth bounded_atan_neg_eleventh of
      | NONE => NONE
      | SOME step11 =>
        case bounded_interval64_mul_add square step11
          bounded_atan_pos_ninth of
        | NONE => NONE
        | SOME step9 =>
          case bounded_interval64_mul_add square step9
            bounded_atan_neg_seventh of
          | NONE => NONE
          | SOME step7 =>
            case bounded_interval64_mul_add square step7
              bounded_atan_pos_fifth of
            | NONE => NONE
            | SOME step5 =>
              case bounded_interval64_mul_add square step5
                bounded_atan_neg_third of
              | NONE => NONE
              | SOME step3 =>
                case bounded_interval64_mul_add square step3
                  bounded_atan_one of
                | NONE => NONE
                | SOME body => bounded_interval64_mul point body
End

Definition bounded_interval64_atan_unit_lower_def:
  bounded_interval64_atan_unit_lower endpoint =
    let magnitude = bounded_signed64_magnitude endpoint in
    if ¬word_lo magnitude bounded_atan_scale then NONE
    else if bounded_signed64_effective_negative endpoint then
      case bounded_interval64_atan_pos_upper magnitude of
      | NONE => NONE
      | SOME enclosure =>
          SOME (bounded_signed64_neg (bounded_interval64_upper enclosure))
    else
      case bounded_interval64_atan_pos_lower magnitude of
      | NONE => NONE
      | SOME enclosure => SOME (bounded_interval64_lower enclosure)
End

Definition bounded_interval64_atan_unit_upper_def:
  bounded_interval64_atan_unit_upper endpoint =
    let magnitude = bounded_signed64_magnitude endpoint in
    if ¬word_lo magnitude bounded_atan_scale then NONE
    else if bounded_signed64_effective_negative endpoint then
      case bounded_interval64_atan_pos_lower magnitude of
      | NONE => NONE
      | SOME enclosure =>
          SOME (bounded_signed64_neg (bounded_interval64_lower enclosure))
    else
      case bounded_interval64_atan_pos_upper magnitude of
      | NONE => NONE
      | SOME enclosure => SOME (bounded_interval64_upper enclosure)
End

Definition bounded_interval64_atan_unit_def:
  bounded_interval64_atan_unit input =
    if ¬bounded_interval64_valid input then NONE
    else
      case bounded_interval64_atan_unit_lower
        (bounded_interval64_lower input) of
      | NONE => NONE
      | SOME lower =>
        case bounded_interval64_atan_unit_upper
          (bounded_interval64_upper input) of
        | NONE => NONE
        | SOME upper =>
            let result = BoundedInterval64 lower upper in
            if bounded_interval64_valid result then SOME result else NONE
End

Definition bounded_interval64_atan_range_point_def:
  bounded_interval64_atan_range_point endpoint reciprocal =
    let magnitude = bounded_signed64_magnitude endpoint in
    if word_lo magnitude bounded_atan_scale then
      if reciprocal = NONE then
        bounded_interval64_atan_unit
          (BoundedInterval64 endpoint endpoint)
      else NONE
    else if magnitude = bounded_atan_scale then NONE
    else
      case reciprocal of
      | NONE => NONE
      | SOME reciprocal_interval =>
          if ¬bounded_interval64_inv_certificate
            (BoundedInterval64 endpoint endpoint) reciprocal_interval
          then NONE
          else
            let reduced =
              if bounded_signed64_effective_negative endpoint then
                bounded_interval64_neg reciprocal_interval
              else reciprocal_interval in
            case bounded_interval64_atan_unit reduced of
            | NONE => NONE
            | SOME reduced_atan =>
                if bounded_signed64_effective_negative endpoint then
                  bounded_interval64_add reduced_atan
                    (bounded_interval64_neg bounded_atan_pi_half)
                else
                  bounded_interval64_add bounded_atan_pi_half
                    (bounded_interval64_neg reduced_atan)
End

Definition bounded_interval64_atan_range_def:
  bounded_interval64_atan_range input lower_reciprocal upper_reciprocal =
    if ¬bounded_interval64_valid input then NONE
    else
      case bounded_interval64_atan_range_point
        (bounded_interval64_lower input) lower_reciprocal of
      | NONE => NONE
      | SOME lower_enclosure =>
        case bounded_interval64_atan_range_point
          (bounded_interval64_upper input) upper_reciprocal of
        | NONE => NONE
        | SOME upper_enclosure =>
            let result = BoundedInterval64
              (bounded_interval64_lower lower_enclosure)
              (bounded_interval64_upper upper_enclosure) in
            if bounded_interval64_valid result then SOME result else NONE
End

Theorem bounded_interval64_atan_range_some:
  bounded_interval64_atan_range input lower_reciprocal upper_reciprocal =
    SOME result ⇒
  bounded_interval64_valid result
Proof
  rw [bounded_interval64_atan_range_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_interval64_atan_range_rejects_invalid:
  ¬bounded_interval64_valid input ⇒
  bounded_interval64_atan_range input lower_reciprocal upper_reciprocal =
    NONE
Proof
  rw [bounded_interval64_atan_range_def]
QED

Theorem bounded_interval64_atan_closed_tests:
  bounded_interval64_atan_range
    (BoundedInterval64
      (BoundedSigned64 F 0w) (BoundedSigned64 F 0w))
    NONE NONE =
      SOME (BoundedInterval64
        (BoundedSigned64 F 0w) (BoundedSigned64 F 0w)) ∧
  bounded_interval64_atan_range_point
    (BoundedSigned64 F 1099511627776w) NONE = NONE ∧
  bounded_interval64_atan_range_point
    (BoundedSigned64 F 2199023255552w) NONE = NONE ∧
  (case bounded_interval64_atan_range_point
      (BoundedSigned64 F 2199023255552w)
      (SOME (BoundedInterval64
        (BoundedSigned64 F 549755813888w)
        (BoundedSigned64 F 549755813888w))) of
   | NONE => F
   | SOME result => bounded_interval64_valid result) ∧
  bounded_interval64_atan_range
    (BoundedInterval64
      (BoundedSigned64 F 3w) (BoundedSigned64 T 3w))
    NONE NONE = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
