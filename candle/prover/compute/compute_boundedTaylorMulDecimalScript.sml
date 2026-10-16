(*****************************************************************************
 * Complete decimal fixed-scale compact-Taylor product.
 *
 * This follows the authenticated object's raw product-rule normalization:
 * center-gradient and Hessian sums are fused, rounded once at scale 10^12,
 * and then passed to decimal Taylor completion.
 *****************************************************************************)
Theory compute_boundedTaylorMulDecimal
Ancestors
  compute_boundedTaylorCompleteDecimal
Libs
  bossLib preamble

Definition bounded_taylor64_mul_decimal_def:
  bounded_taylor64_mul_decimal radii left right =
    if ¬bounded_taylor64_well_formed left ∨
       ¬bounded_taylor64_well_formed right
    then NONE
    else
      case left of
      | BoundedTaylor64 left_domain left_center left_center_gradient
          left_value left_gradient_bounds left_hessian =>
        case right of
        | BoundedTaylor64 right_domain right_center right_center_gradient
            right_value right_gradient_bounds right_hessian =>
          case bounded_interval64_mul_decimal left_center right_center of
          | NONE => NONE
          | SOME center_value =>
            case bounded_interval64_fused_scale_add_decimal
              right_center left_center_gradient
              left_center right_center_gradient of
            | NONE => NONE
            | SOME center_gradient =>
              case bounded_interval64_symmetric_product_pairs
                left_gradient_bounds right_gradient_bounds of
              | NONE => NONE
              | SOME outer_pairs =>
                case bounded_interval64_fused_hessian_decimal
                  left_value right_value left_hessian right_hessian
                  outer_pairs of
                | NONE => NONE
                | SOME hessian =>
                  bounded_taylor64_complete_decimal radii
                    (left_domain ∧ right_domain) center_value
                    center_gradient hessian
End

Theorem bounded_taylor64_mul_decimal_some:
  bounded_taylor64_mul_decimal radii left right = SOME result ==>
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_mul_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_some
QED

Theorem bounded_taylor64_mul_decimal_closed_tests:
  let zero = bounded_interval64_zero in
  let zeros6 = REPLICATE 6 zero in
  let zeros21 = REPLICATE 21 zero in
  let radii = REPLICATE 6 0w in
  let one = BoundedInterval64
    (BoundedSigned64 F 1000000000000w)
    (BoundedSigned64 F 1000000000000w) in
  let state = BoundedTaylor64 T one zeros6 one zeros6 zeros21 in
  let malformed = BoundedTaylor64 T one [] one zeros6 zeros21 in
  bounded_taylor64_mul_decimal radii state state = SOME state /\
  bounded_taylor64_mul_decimal radii malformed state = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
