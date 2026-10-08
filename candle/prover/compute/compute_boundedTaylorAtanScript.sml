(*****************************************************************************
 * Checked arctangent lift for compact Taylor states.
 *
 * The fixed range-reduced value kernel computes the center enclosure.
 * Supplied first-derivative intervals are authenticated as reciprocals of
 * 1+x^2 at the center and over the whole box.  The second derivative
 * -2*x/(1+x^2)^2 is then constructed with checked interval arithmetic before
 * the general unary chain-rule lift is used.
 *
 * This is an executable data/certificate boundary.  The real-analytic
 * refinement of the fixed arctangent value kernel remains a single shared
 * release theorem, not a per-expression proof.
 *****************************************************************************)
Theory compute_boundedTaylorAtan
Ancestors
  compute_boundedTaylorSqrt
Libs
  bossLib preamble

Definition bounded_taylor64_atan_def:
  bounded_taylor64_atan radii center_lower_reciprocal
      center_upper_reciprocal center_derivative box_derivative source =
    case source of
    | BoundedTaylor64 source_domain center_value center_gradient
        value_bound gradient_bounds hessian =>
      case bounded_interval64_atan_range center_value
        center_lower_reciprocal center_upper_reciprocal of
      | NONE => NONE
      | SOME center_result =>
        case bounded_interval64_mul center_value center_value of
        | NONE => NONE
        | SOME center_square =>
          case bounded_interval64_add bounded_atan_one center_square of
          | NONE => NONE
          | SOME center_denominator =>
            case bounded_interval64_mul value_bound value_bound of
            | NONE => NONE
            | SOME box_square =>
              case bounded_interval64_add bounded_atan_one box_square of
              | NONE => NONE
              | SOME box_denominator =>
                if ¬bounded_interval64_inv_certificate
                    center_denominator center_derivative ∨
                   ¬bounded_interval64_inv_certificate
                    box_denominator box_derivative
                then NONE
                else
                  case bounded_interval64_mul
                    box_derivative box_derivative of
                  | NONE => NONE
                  | SOME box_derivative_square =>
                    case bounded_interval64_add value_bound value_bound of
                    | NONE => NONE
                    | SOME box_twice =>
                      case bounded_interval64_mul
                        box_twice box_derivative_square of
                      | NONE => NONE
                      | SOME box_second_magnitude =>
                        bounded_taylor64_unary_complete radii T
                          center_result center_derivative box_derivative
                          (bounded_interval64_neg box_second_magnitude)
                          source
End

Theorem bounded_taylor64_atan_some:
  bounded_taylor64_atan radii center_lower_reciprocal
      center_upper_reciprocal center_derivative box_derivative source =
    SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_atan_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorUnaryTheory.bounded_taylor64_unary_complete_some
QED

Theorem bounded_taylor64_atan_closed_tests:
  let zeros6 = REPLICATE 6 bounded_interval64_zero in
  let zeros21 = REPLICATE 21 bounded_interval64_zero in
  let radii = REPLICATE 6 0w in
  let one = BoundedInterval64
    (BoundedSigned64 F 1099511627776w)
    (BoundedSigned64 F 1099511627776w) in
  let two = BoundedInterval64
    (BoundedSigned64 F 2199023255552w)
    (BoundedSigned64 F 2199023255552w) in
  let source = BoundedTaylor64 T bounded_interval64_zero zeros6
    bounded_interval64_zero zeros6 zeros21 in
  bounded_taylor64_atan radii NONE NONE one one source = SOME source ∧
  bounded_taylor64_atan radii NONE NONE two one source = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
