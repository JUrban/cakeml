(*****************************************************************************
 * Checked multiplication for compact Taylor states.
 *
 * The product rule is evaluated entirely as data.  Center gradients use
 * g*df + f*dg; the compact upper-triangular Hessian uses
 * g*Hf + df*dg^T + dg*df^T + f*Hg.  The existing complete Taylor
 * constructor then derives whole-box value and gradient bounds.
 *
 * Each interval product is rounded by the existing total fixed-scale
 * primitive.  Complete-batch integration must compare this normalization
 * cadence with the tighter native wide-accumulator path before release.
 *****************************************************************************)
Theory compute_boundedTaylorMul
Ancestors
  compute_boundedTaylorAtan
Libs
  bossLib preamble

Definition bounded_interval64_symmetric_outer_def:
  bounded_interval64_symmetric_outer [] [] = SOME [] ∧
  bounded_interval64_symmetric_outer [] (_::_) = NONE ∧
  bounded_interval64_symmetric_outer (_::_) [] = NONE ∧
  bounded_interval64_symmetric_outer
      (left::left_rest) (right::right_rest) =
    case bounded_interval64_list_scale left (right::right_rest) of
    | NONE => NONE
    | SOME left_row =>
      case bounded_interval64_list_scale right (left::left_rest) of
      | NONE => NONE
      | SOME right_row =>
        case bounded_interval64_list_add left_row right_row of
        | NONE => NONE
        | SOME row =>
          case bounded_interval64_symmetric_outer left_rest right_rest of
          | NONE => NONE
          | SOME rows => SOME (row ++ rows)
End

Definition bounded_taylor64_mul_def:
  bounded_taylor64_mul radii left right =
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
          case bounded_interval64_mul left_center right_center of
          | NONE => NONE
          | SOME center_value =>
            case bounded_interval64_list_scale
              right_center left_center_gradient of
            | NONE => NONE
            | SOME left_center_term =>
              case bounded_interval64_list_scale
                left_center right_center_gradient of
              | NONE => NONE
              | SOME right_center_term =>
                case bounded_interval64_list_add
                  left_center_term right_center_term of
                | NONE => NONE
                | SOME center_gradient =>
                  case bounded_interval64_list_scale
                    right_value left_hessian of
                  | NONE => NONE
                  | SOME left_hessian_term =>
                    case bounded_interval64_symmetric_outer
                      left_gradient_bounds right_gradient_bounds of
                    | NONE => NONE
                    | SOME outer_terms =>
                      case bounded_interval64_list_scale
                        left_value right_hessian of
                      | NONE => NONE
                      | SOME right_hessian_term =>
                        case bounded_interval64_list_add
                          left_hessian_term outer_terms of
                        | NONE => NONE
                        | SOME partial_hessian =>
                          case bounded_interval64_list_add
                            partial_hessian right_hessian_term of
                          | NONE => NONE
                          | SOME hessian =>
                            bounded_taylor64_complete radii
                              (left_domain ∧ right_domain) center_value
                              center_gradient hessian
End

Theorem bounded_taylor64_mul_some:
  bounded_taylor64_mul radii left right = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_mul_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorUnaryTheory.bounded_taylor64_complete_some
QED

Theorem bounded_taylor64_mul_closed_tests:
  let zeros6 = REPLICATE 6 bounded_interval64_zero in
  let zeros21 = REPLICATE 21 bounded_interval64_zero in
  let radii = REPLICATE 6 0w in
  let one = BoundedInterval64
    (BoundedSigned64 F 1099511627776w)
    (BoundedSigned64 F 1099511627776w) in
  let state = BoundedTaylor64 T one zeros6 one zeros6 zeros21 in
  let malformed = BoundedTaylor64 T one [] one zeros6 zeros21 in
  bounded_interval64_symmetric_outer zeros6 zeros6 = SOME zeros21 ∧
  bounded_taylor64_mul radii state state = SOME state ∧
  bounded_taylor64_mul radii malformed state = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
