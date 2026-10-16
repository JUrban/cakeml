(*****************************************************************************
 * Decimal product-rule building blocks for compact Taylor states.
 *
 * Raw product sums are normalized once by the proved decimal fused boundary.
 * Ordinary scalar/list products use the directed decimal interval operation.
 *****************************************************************************)
Theory compute_boundedTaylorProductDecimal
Ancestors
  compute_boundedTaylorFusedDecimal compute_boundedIntervalDecimal
Libs
  bossLib preamble

Definition bounded_interval64_list_scale_decimal_def:
  bounded_interval64_list_scale_decimal scalar [] = SOME [] /\
  bounded_interval64_list_scale_decimal scalar (value::rest) =
    case bounded_interval64_mul_decimal scalar value of
    | NONE => NONE
    | SOME product =>
      case bounded_interval64_list_scale_decimal scalar rest of
      | NONE => NONE
      | SOME products => SOME (product::products)
End

Definition bounded_interval64_fused_scale_add_decimal_def:
  bounded_interval64_fused_scale_add_decimal
      left_scale [] right_scale [] = SOME [] /\
  bounded_interval64_fused_scale_add_decimal left_scale (left::left_rest)
      right_scale (right::right_rest) =
    (case bounded_interval64_fused_products_decimal
      [(left_scale,left);(right_scale,right)] of
    | NONE => NONE
    | SOME entry =>
      case bounded_interval64_fused_scale_add_decimal left_scale left_rest
        right_scale right_rest of
      | NONE => NONE
      | SOME entries => SOME (entry::entries)) /\
  bounded_interval64_fused_scale_add_decimal left_scale _ right_scale _ =
    NONE
End

Definition bounded_interval64_fused_hessian_decimal_def:
  bounded_interval64_fused_hessian_decimal
      left_value right_value [] [] [] = SOME [] /\
  bounded_interval64_fused_hessian_decimal left_value right_value
      (left_hessian::left_rest) (right_hessian::right_rest)
      (outer::outer_rest) =
    (case bounded_interval64_fused_products_decimal
      [(right_value,left_hessian);FST outer;SND outer;
       (left_value,right_hessian)] of
    | NONE => NONE
    | SOME entry =>
      case bounded_interval64_fused_hessian_decimal left_value right_value
        left_rest right_rest outer_rest of
      | NONE => NONE
      | SOME entries => SOME (entry::entries)) /\
  bounded_interval64_fused_hessian_decimal left_value right_value _ _ _ =
    NONE
End

Definition bounded_interval64_symmetric_outer_decimal_def:
  bounded_interval64_symmetric_outer_decimal [] [] = SOME [] /\
  bounded_interval64_symmetric_outer_decimal [] (_::_) = NONE /\
  bounded_interval64_symmetric_outer_decimal (_::_) [] = NONE /\
  bounded_interval64_symmetric_outer_decimal
      (left::left_rest) (right::right_rest) =
    case bounded_interval64_list_scale_decimal left (right::right_rest) of
    | NONE => NONE
    | SOME left_row =>
      case bounded_interval64_list_scale_decimal right (left::left_rest) of
      | NONE => NONE
      | SOME right_row =>
        case bounded_interval64_list_add left_row right_row of
        | NONE => NONE
        | SOME row =>
          case bounded_interval64_symmetric_outer_decimal
            left_rest right_rest of
          | NONE => NONE
          | SOME rows => SOME (row ++ rows)
End

Theorem bounded_interval64_list_scale_decimal_length:
  !values result.
    bounded_interval64_list_scale_decimal scalar values = SOME result ==>
    LENGTH result = LENGTH values
Proof
  Induct
  >> rw [bounded_interval64_list_scale_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_interval64_fused_scale_add_decimal_length:
  !left right result.
    bounded_interval64_fused_scale_add_decimal
      left_scale left right_scale right = SOME result ==>
    LENGTH left = LENGTH right /\ LENGTH result = LENGTH left
Proof
  Induct
  >> Cases_on `right`
  >> rw [bounded_interval64_fused_scale_add_decimal_def]
  >> every_case_tac
  >> res_tac
  >> gvs []
QED

Theorem bounded_interval64_fused_hessian_decimal_length:
  !left right outer result.
    bounded_interval64_fused_hessian_decimal
      left_value right_value left right outer = SOME result ==>
    LENGTH left = LENGTH right /\
    LENGTH right = LENGTH outer /\
    LENGTH result = LENGTH left
Proof
  Induct
  >> Cases_on `right`
  >> Cases_on `outer`
  >> rw [bounded_interval64_fused_hessian_decimal_def]
  >> every_case_tac
  >> res_tac
  >> gvs []
QED

Theorem bounded_taylor_product_decimal_closed_tests:
  let zero = bounded_interval64_zero in
  let one = BoundedInterval64
    (BoundedSigned64 F 1000000000000w)
    (BoundedSigned64 F 1000000000000w) in
  bounded_interval64_list_scale_decimal one [one;zero] =
    SOME [one;zero] /\
  bounded_interval64_fused_scale_add_decimal one [one;zero]
      one [zero;one] = SOME [one;one] /\
  bounded_interval64_fused_hessian_decimal one one [zero] [zero]
      [((one,one),(zero,one))] = SOME [one] /\
  bounded_interval64_symmetric_outer_decimal [one;zero] [zero;one] =
    SOME [zero;one;zero]
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
