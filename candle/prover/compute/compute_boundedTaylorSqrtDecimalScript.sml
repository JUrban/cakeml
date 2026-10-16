(*****************************************************************************
 * Checked reciprocal and square-root lifts at decimal fixed scale.
 *****************************************************************************)
Theory compute_boundedTaylorSqrtDecimal
Ancestors
  compute_boundedTaylorUnaryDecimal compute_boundedCertificateDecimal
Libs
  bossLib preamble

Definition bounded_taylor64_inverse_decimal_def:
  bounded_taylor64_inverse_decimal
      radii center_reciprocal box_reciprocal source =
    case source of
    | BoundedTaylor64 source_domain center_value center_gradient
        value_bound gradient_bounds hessian =>
      if ¬bounded_interval64_inv_certificate_decimal
          center_value center_reciprocal ∨
         ¬bounded_interval64_inv_certificate_decimal
          value_bound box_reciprocal
      then NONE
      else
        case bounded_interval64_mul_decimal
          center_reciprocal center_reciprocal of
        | NONE => NONE
        | SOME center_square =>
          case bounded_interval64_mul_decimal
            box_reciprocal box_reciprocal of
          | NONE => NONE
          | SOME box_square =>
            case bounded_interval64_mul_decimal box_square box_reciprocal of
            | NONE => NONE
            | SOME box_cube =>
              case bounded_interval64_add box_cube box_cube of
              | NONE => NONE
              | SOME box_second =>
                bounded_taylor64_unary_complete_decimal radii T
                  center_reciprocal
                  (bounded_interval64_neg center_square)
                  (bounded_interval64_neg box_square)
                  box_second source
End

Definition bounded_taylor64_sqrt_decimal_def:
  bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal source =
    case source of
    | BoundedTaylor64 source_domain center_value center_gradient
        value_bound gradient_bounds hessian =>
      if ¬bounded_interval64_sqrt_certificate_decimal
            center_value center_sqrt ∨
         ¬bounded_interval64_sqrt_certificate_decimal value_bound box_sqrt
      then NONE
      else
        case bounded_interval64_add center_sqrt center_sqrt of
        | NONE => NONE
        | SOME center_twice =>
          case bounded_interval64_add box_sqrt box_sqrt of
          | NONE => NONE
          | SOME box_twice =>
            case bounded_interval64_add value_bound value_bound of
            | NONE => NONE
            | SOME input_twice =>
              case bounded_interval64_mul_decimal box_twice input_twice of
              | NONE => NONE
              | SOME box_second_denominator =>
                if ¬bounded_interval64_inv_certificate_decimal
                      center_twice center_derivative ∨
                   ¬bounded_interval64_inv_certificate_decimal
                      box_twice box_derivative ∨
                   ¬bounded_interval64_inv_certificate_decimal
                      box_second_denominator box_second_reciprocal
                then NONE
                else
                  bounded_taylor64_unary_complete_decimal radii T center_sqrt
                    center_derivative box_derivative
                    (bounded_interval64_neg box_second_reciprocal) source
End

Theorem bounded_taylor64_inverse_decimal_some:
  bounded_taylor64_inverse_decimal radii center_reciprocal box_reciprocal
      source = SOME result ==>
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_inverse_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorUnaryDecimalTheory.bounded_taylor64_unary_complete_decimal_some
QED

Theorem bounded_taylor64_sqrt_decimal_some:
  bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal source =
    SOME result ==>
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_sqrt_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorUnaryDecimalTheory.bounded_taylor64_unary_complete_decimal_some
QED

Theorem bounded_taylor_sqrt_decimal_closed_tests:
  let zero = bounded_interval64_zero in
  let zeros6 = REPLICATE 6 zero in
  let zeros21 = REPLICATE 21 zero in
  let radii = REPLICATE 6 0w in
  let one = BoundedInterval64
    (BoundedSigned64 F 1000000000000w)
    (BoundedSigned64 F 1000000000000w) in
  let two = BoundedInterval64
    (BoundedSigned64 F 2000000000000w)
    (BoundedSigned64 F 2000000000000w) in
  let four = BoundedInterval64
    (BoundedSigned64 F 4000000000000w)
    (BoundedSigned64 F 4000000000000w) in
  let quarter = BoundedInterval64
    (BoundedSigned64 F 250000000000w)
    (BoundedSigned64 F 250000000000w) in
  let thirty_second = BoundedInterval64
    (BoundedSigned64 F 31250000000w)
    (BoundedSigned64 F 31250000000w) in
  let one_state = BoundedTaylor64 T one zeros6 one zeros6 zeros21 in
  let four_state = BoundedTaylor64 T four zeros6 four zeros6 zeros21 in
  let two_state = BoundedTaylor64 T two zeros6 two zeros6 zeros21 in
  bounded_taylor64_inverse_decimal radii one one one_state =
    SOME one_state /\
  bounded_taylor64_inverse_decimal radii two one one_state = NONE /\
  bounded_taylor64_sqrt_decimal radii two two quarter quarter
      thirty_second four_state = SOME two_state /\
  bounded_taylor64_sqrt_decimal radii four two quarter quarter
      thirty_second four_state = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
