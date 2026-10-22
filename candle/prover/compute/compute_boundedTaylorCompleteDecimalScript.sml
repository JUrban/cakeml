(*****************************************************************************
 * Decimal fixed-scale completion of compact Taylor states.
 *
 * This is the scale-10^12 counterpart of the optimized dyadic completion.
 * It retains raw radius/gradient and radius/radius/Hessian products and
 * performs the same single outward rounding used by the authenticated object
 * checker.  Every narrowing remains option-valued and fail-closed.
 *****************************************************************************)
Theory compute_boundedTaylorCompleteDecimal
Ancestors
  compute_boundedTaylorProductDecimal compute_boundedTaylorGradient
Libs
  bossLib preamble

Definition bounded128_floor64_decimal_def:
  bounded128_floor64_decimal magnitude =
    let quotient = bounded128_to_num magnitude DIV 1000000000000 in
    if quotient < bounded_word_base then
      SOME ((n2w quotient):word64)
    else NONE
End

Definition bounded128_ceil64_decimal_def:
  bounded128_ceil64_decimal magnitude =
    let quotient =
      (bounded128_to_num magnitude + 999999999999) DIV 1000000000000 in
    if quotient < bounded_word_base then
      SOME ((n2w quotient):word64)
    else NONE
End

Definition bounded_signed128_floor64_decimal_def:
  bounded_signed128_floor64_decimal
      (BoundedSigned128 negative magnitude) =
    case (if negative then bounded128_ceil64_decimal magnitude
          else bounded128_floor64_decimal magnitude) of
    | NONE => NONE
    | SOME quotient => SOME (bounded_signed64_make negative quotient)
End

Definition bounded_signed128_ceil64_decimal_def:
  bounded_signed128_ceil64_decimal
      (BoundedSigned128 negative magnitude) =
    case (if negative then bounded128_floor64_decimal magnitude
          else bounded128_ceil64_decimal magnitude) of
    | NONE => NONE
    | SOME quotient => SOME (bounded_signed64_make negative quotient)
End

Definition bounded_signed64_scale_decimal128_def:
  bounded_signed64_scale_decimal128 value =
    bounded_signed64_raw_product value
      (BoundedSigned64 F 1000000000000w)
End

Definition bounded_taylor_gradient_row_complete_decimal_def:
  bounded_taylor_gradient_row_complete_decimal
      radii center_entry hessian_row =
    case bounded_dot_abs_upper radii hessian_row of
    | NONE => NONE
    | SOME variation =>
      case center_entry of
      | BoundedInterval64 center_lower center_upper =>
        case bounded_signed128_add
          (bounded_signed64_scale_decimal128 center_lower)
          (bounded_signed128_make T variation) of
        | NONE => NONE
        | SOME raw_lower =>
          case bounded_signed128_add
            (bounded_signed64_scale_decimal128 center_upper)
            (bounded_signed128_make F variation) of
          | NONE => NONE
          | SOME raw_upper =>
            case bounded_signed128_floor64_decimal raw_lower of
            | NONE => NONE
            | SOME lower =>
              case bounded_signed128_ceil64_decimal raw_upper of
              | NONE => NONE
              | SOME upper => SOME (BoundedInterval64 lower upper)
End

Definition bounded_taylor_gradient_rows_complete_decimal_def:
  bounded_taylor_gradient_rows_complete_decimal radii [] [] = SOME [] /\
  bounded_taylor_gradient_rows_complete_decimal radii [] (_::_) = NONE /\
  bounded_taylor_gradient_rows_complete_decimal radii (_::_) [] = NONE /\
  bounded_taylor_gradient_rows_complete_decimal radii
      (center_entry::center_rest) (hessian_row::hessian_rest) =
    case bounded_taylor_gradient_row_complete_decimal
      radii center_entry hessian_row of
    | NONE => NONE
    | SOME gradient_bound =>
      case bounded_taylor_gradient_rows_complete_decimal
        radii center_rest hessian_rest of
      | NONE => NONE
      | SOME gradient_rest => SOME (gradient_bound::gradient_rest)
End

Definition bounded_taylor_gradient_complete_decimal_def:
  bounded_taylor_gradient_complete_decimal radii center_gradient hessian =
    case bounded_hessian64_rows hessian of
    | NONE => NONE
    | SOME rows =>
      bounded_taylor_gradient_rows_complete_decimal
        radii center_gradient rows
End

Definition bounded_taylor_error_decimal_def:
  bounded_taylor_error_decimal radii center_gradient hessian =
    case bounded_dot_abs_upper radii center_gradient of
    | NONE => NONE
    | SOME linear =>
      case bounded_quadratic_abs_upper radii hessian of
      | NONE => NONE
      | SOME quadratic =>
        case bounded128_mul_word64_to_192_words linear 2000000000000w of
        | NONE => NONE
        | SOME scaled_linear =>
          bounded192_add_words scaled_linear quadratic
End

Definition bounded_signed64_scale_two_decimal_squared192_def:
  bounded_signed64_scale_two_decimal_squared192
      (BoundedSigned64 negative magnitude) =
    case bounded128_mul_word64_to_192_words
      bounded_decimal_scale_squared128 magnitude of
    | NONE => NONE
    | SOME product =>
      case bounded192_add_words product product of
      | NONE => NONE
      | SOME doubled => SOME (bounded_signed192_make negative doubled)
End

Definition bounded192_floor64_two_decimal_squared_def:
  bounded192_floor64_two_decimal_squared magnitude =
    let quotient =
      bounded192_to_num magnitude DIV 2000000000000000000000000 in
    if quotient < bounded_word_base then
      SOME ((n2w quotient):word64)
    else NONE
End

Definition bounded192_ceil64_two_decimal_squared_def:
  bounded192_ceil64_two_decimal_squared magnitude =
    let quotient =
      (bounded192_to_num magnitude + 1999999999999999999999999) DIV
        2000000000000000000000000 in
    if quotient < bounded_word_base then
      SOME ((n2w quotient):word64)
    else NONE
End

Definition bounded_signed192_floor64_two_decimal_squared_def:
  bounded_signed192_floor64_two_decimal_squared
      (BoundedSigned192 negative magnitude) =
    case
      (if negative then bounded192_ceil64_two_decimal_squared magnitude
       else bounded192_floor64_two_decimal_squared magnitude) of
    | NONE => NONE
    | SOME quotient => SOME (bounded_signed64_make negative quotient)
End

Definition bounded_signed192_ceil64_two_decimal_squared_def:
  bounded_signed192_ceil64_two_decimal_squared
      (BoundedSigned192 negative magnitude) =
    case
      (if negative then bounded192_floor64_two_decimal_squared magnitude
       else bounded192_ceil64_two_decimal_squared magnitude) of
    | NONE => NONE
    | SOME quotient => SOME (bounded_signed64_make negative quotient)
End

Definition bounded_taylor_value_complete_decimal_def:
  bounded_taylor_value_complete_decimal
      radii center_value center_gradient hessian =
    case bounded_taylor_error_decimal radii center_gradient hessian of
    | NONE => NONE
    | SOME error =>
      case center_value of
      | BoundedInterval64 center_lower center_upper =>
        case bounded_signed64_scale_two_decimal_squared192 center_lower of
        | NONE => NONE
        | SOME scaled_lower =>
          case bounded_signed64_scale_two_decimal_squared192 center_upper of
          | NONE => NONE
          | SOME scaled_upper =>
            case bounded_signed192_add scaled_lower
              (bounded_signed192_make T error) of
            | NONE => NONE
            | SOME raw_lower =>
              case bounded_signed192_add scaled_upper
                (bounded_signed192_make F error) of
              | NONE => NONE
              | SOME raw_upper =>
                case bounded_signed192_floor64_two_decimal_squared
                  raw_lower of
                | NONE => NONE
                | SOME lower =>
                  case bounded_signed192_ceil64_two_decimal_squared
                    raw_upper of
                  | NONE => NONE
                  | SOME upper => SOME (BoundedInterval64 lower upper)
End

Definition bounded_taylor64_complete_decimal_def:
  bounded_taylor64_complete_decimal
      radii domain center_value center_gradient hessian =
    case bounded_taylor_value_complete_decimal
      radii center_value center_gradient hessian of
    | NONE => NONE
    | SOME value_bound =>
      case bounded_taylor_gradient_complete_decimal
        radii center_gradient hessian of
      | NONE => NONE
      | SOME gradient_bounds =>
        bounded_taylor64_make domain center_value center_gradient
          value_bound gradient_bounds hessian
End

Theorem bounded_taylor64_complete_decimal_some:
  bounded_taylor64_complete_decimal radii result_domain center_value
    center_gradient hessian = SOME result ==>
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_complete_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorStateTheory.bounded_taylor64_make_some
QED

Theorem bounded_taylor_complete_decimal_closed_tests:
  let zero = bounded_interval64_zero in
  let zeros6 = REPLICATE 6 zero in
  let zeros21 = REPLICATE 21 zero in
  let radii = REPLICATE 6 0w in
  let one = BoundedInterval64
    (BoundedSigned64 F 1000000000000w)
    (BoundedSigned64 F 1000000000000w) in
  bounded_signed64_scale_decimal128 (BoundedSigned64 F 1w) =
    BoundedSigned128 F (Bounded128 0w 1000000000000w) /\
  bounded_taylor_value_complete_decimal radii one zeros6 zeros21 =
    SOME one /\
  bounded_taylor_gradient_complete_decimal radii zeros6 zeros21 =
    SOME zeros6 /\
  bounded_taylor64_complete_decimal radii T one zeros6 zeros21 =
    SOME (BoundedTaylor64 T one zeros6 one zeros6 zeros21)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
