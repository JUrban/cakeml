(*****************************************************************************
 * General checked unary chain-rule lift for compact Taylor states.
 *
 * A scalar kernel supplies its center value, center first derivative, whole-
 * box first derivative, and whole-box second derivative.  This reusable lift
 * performs the six-gradient and compact symmetric-Hessian chain rule, then
 * invokes the existing complete Taylor constructor.  Scalar kernels remain
 * responsible for their own domain and certificate checks.
 *****************************************************************************)
Theory compute_boundedTaylorUnary
Ancestors
  compute_boundedAtan compute_boundedTaylorGradient
Libs
  bossLib preamble

Definition bounded_interval64_self_outer_def:
  bounded_interval64_self_outer [] = SOME [] ∧
  bounded_interval64_self_outer (entry::rest) =
    case bounded_interval64_list_scale entry (entry::rest) of
    | NONE => NONE
    | SOME row =>
      case bounded_interval64_self_outer rest of
      | NONE => NONE
      | SOME rows => SOME (row ++ rows)
End

Definition bounded_triangular_length_def:
  bounded_triangular_length 0 = 0 ∧
  bounded_triangular_length (SUC n) =
    SUC n + bounded_triangular_length n
End

Definition bounded_taylor64_unary_complete_def:
  bounded_taylor64_unary_complete radii result_domain center_result
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
        case bounded_interval64_list_scale
          center_derivative source_center_gradient of
        | NONE => NONE
        | SOME center_gradient =>
          case bounded_interval64_self_outer source_gradient_bounds of
          | NONE => NONE
          | SOME gradient_outer =>
            case bounded_interval64_list_scale
              box_second gradient_outer of
            | NONE => NONE
            | SOME outer_hessian =>
              case bounded_interval64_list_scale
                box_derivative source_hessian of
              | NONE => NONE
              | SOME source_hessian_scaled =>
                case bounded_interval64_list_add
                  outer_hessian source_hessian_scaled of
                | NONE => NONE
                | SOME hessian =>
                    bounded_taylor64_complete radii
                      (source_domain ∧ result_domain) center_result
                      center_gradient hessian
End

Theorem bounded_interval64_self_outer_length:
  ∀gradient result.
    bounded_interval64_self_outer gradient = SOME result ⇒
    LENGTH result = bounded_triangular_length (LENGTH gradient)
Proof
  Induct
  >> rw [bounded_interval64_self_outer_def,
         bounded_triangular_length_def]
  >> Cases_on `bounded_interval64_list_scale h (h::gradient)`
  >> Cases_on `bounded_interval64_self_outer gradient`
  >> gvs []
  >> imp_res_tac
       compute_boundedIntervalListTheory.bounded_interval64_list_scale_length
  >> res_tac
  >> fs []
QED

Theorem bounded_interval64_self_outer_six_shape:
  LENGTH gradient = 6 ∧
  bounded_interval64_self_outer gradient = SOME result ⇒
  LENGTH result = 21
Proof
  strip_tac
  >> imp_res_tac bounded_interval64_self_outer_length
  >> `bounded_triangular_length 6 = 21` by EVAL_TAC
  >> fs []
QED

Theorem bounded_taylor64_complete_some:
  bounded_taylor64_complete radii domain center_value center_gradient
      hessian = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_complete_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorStateTheory.bounded_taylor64_make_some
QED

Theorem bounded_taylor64_unary_complete_some:
  bounded_taylor64_unary_complete radii result_domain center_result
      center_derivative box_derivative box_second source = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_unary_complete_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_taylor64_complete_some
QED

Theorem bounded_taylor64_unary_closed_test:
  let zeros6 = REPLICATE 6 bounded_interval64_zero in
  let zeros21 = REPLICATE 21 bounded_interval64_zero in
  let radii = REPLICATE 6 0w in
  let one = BoundedInterval64
    (BoundedSigned64 F 1099511627776w)
    (BoundedSigned64 F 1099511627776w) in
  let source = BoundedTaylor64 T bounded_interval64_zero zeros6
    bounded_interval64_zero zeros6 zeros21 in
  bounded_interval64_self_outer zeros6 = SOME zeros21 ∧
  bounded_taylor64_unary_complete radii T bounded_interval64_zero
    one one bounded_interval64_zero source = SOME source
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
