(*****************************************************************************
 * Decimal fixed-scale unary chain-rule lift for compact Taylor states.
 *****************************************************************************)
Theory compute_boundedTaylorUnaryDecimal
Ancestors
  compute_boundedTaylorMulDecimal
Libs
  bossLib preamble

Definition bounded_interval64_self_outer_decimal_def:
  bounded_interval64_self_outer_decimal [] = SOME [] /\
  bounded_interval64_self_outer_decimal (entry::rest) =
    case bounded_interval64_list_scale_decimal entry (entry::rest) of
    | NONE => NONE
    | SOME row =>
      case bounded_interval64_self_outer_decimal rest of
      | NONE => NONE
      | SOME rows => SOME (row ++ rows)
End

Definition bounded_taylor64_unary_complete_decimal_def:
  bounded_taylor64_unary_complete_decimal radii result_domain center_result
      center_derivative box_derivative box_second source =
    if ¬bounded_taylor64_well_formed source ∨
       ¬bounded_interval64_valid center_result ∨
       ¬bounded_interval64_valid center_derivative ∨
       ¬bounded_interval64_valid box_derivative ∨
       ¬bounded_interval64_valid box_second
    then NONE
    else
      case source of
      | BoundedTaylor64 source_domain source_center source_center_gradient
          source_value source_gradient_bounds source_hessian =>
        case bounded_interval64_list_scale_decimal
          center_derivative source_center_gradient of
        | NONE => NONE
        | SOME center_gradient =>
          case bounded_interval64_self_outer_decimal
            source_gradient_bounds of
          | NONE => NONE
          | SOME gradient_outer =>
            case bounded_interval64_list_scale_decimal
              box_second gradient_outer of
            | NONE => NONE
            | SOME outer_hessian =>
              case bounded_interval64_list_scale_decimal
                box_derivative source_hessian of
              | NONE => NONE
              | SOME source_hessian_scaled =>
                case bounded_interval64_list_add
                  outer_hessian source_hessian_scaled of
                | NONE => NONE
                | SOME hessian =>
                  bounded_taylor64_complete_decimal radii
                    (source_domain ∧ result_domain) center_result
                    center_gradient hessian
End

Theorem bounded_taylor64_unary_complete_decimal_some:
  bounded_taylor64_unary_complete_decimal radii result_domain center_result
    center_derivative box_derivative box_second source = SOME result ==>
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_unary_complete_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_some
QED

Theorem bounded_taylor_unary_decimal_closed_test:
  let zero = bounded_interval64_zero in
  let zeros6 = REPLICATE 6 zero in
  let zeros21 = REPLICATE 21 zero in
  let radii = REPLICATE 6 0w in
  let one = BoundedInterval64
    (BoundedSigned64 F 1000000000000w)
    (BoundedSigned64 F 1000000000000w) in
  let source = BoundedTaylor64 T zero zeros6 zero zeros6 zeros21 in
  bounded_interval64_self_outer_decimal zeros6 = SOME zeros21 /\
  bounded_taylor64_unary_complete_decimal radii T zero one one zero source =
    SOME source
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
