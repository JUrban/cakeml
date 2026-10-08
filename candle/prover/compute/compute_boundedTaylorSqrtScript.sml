(*****************************************************************************
 * Checked square-root lift for compact Taylor states.
 *
 * Square-root and reciprocal intervals are supplied by untrusted
 * preparation.  Exact certificates authenticate the value, first-derivative
 * and second-derivative inputs before the general unary chain rule is used.
 *****************************************************************************)
Theory compute_boundedTaylorSqrt
Ancestors
  compute_boundedTaylorInverse compute_boundedSqrtCertificate
Libs
  bossLib preamble

Definition bounded_taylor64_sqrt_def:
  bounded_taylor64_sqrt radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal source =
    case source of
    | BoundedTaylor64 source_domain center_value center_gradient
        value_bound gradient_bounds hessian =>
      if ¬bounded_interval64_sqrt_certificate center_value center_sqrt ∨
         ¬bounded_interval64_sqrt_certificate value_bound box_sqrt
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
              case bounded_interval64_mul box_twice input_twice of
              | NONE => NONE
              | SOME box_second_denominator =>
                if ¬bounded_interval64_inv_certificate
                    center_twice center_derivative ∨
                   ¬bounded_interval64_inv_certificate
                    box_twice box_derivative ∨
                   ¬bounded_interval64_inv_certificate
                    box_second_denominator box_second_reciprocal
                then NONE
                else
                  bounded_taylor64_unary_complete radii T center_sqrt
                    center_derivative box_derivative
                    (bounded_interval64_neg box_second_reciprocal) source
End

Theorem bounded_taylor64_sqrt_some:
  bounded_taylor64_sqrt radii center_sqrt box_sqrt center_derivative
      box_derivative box_second_reciprocal source = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_sqrt_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorUnaryTheory.bounded_taylor64_unary_complete_some
QED

Theorem bounded_taylor64_sqrt_closed_tests:
  let zeros6 = REPLICATE 6 bounded_interval64_zero in
  let zeros21 = REPLICATE 21 bounded_interval64_zero in
  let radii = REPLICATE 6 0w in
  let four = BoundedInterval64
    (BoundedSigned64 F 4398046511104w)
    (BoundedSigned64 F 4398046511104w) in
  let two = BoundedInterval64
    (BoundedSigned64 F 2199023255552w)
    (BoundedSigned64 F 2199023255552w) in
  let quarter = BoundedInterval64
    (BoundedSigned64 F 274877906944w)
    (BoundedSigned64 F 274877906944w) in
  let thirty_second = BoundedInterval64
    (BoundedSigned64 F 34359738368w)
    (BoundedSigned64 F 34359738368w) in
  let source = BoundedTaylor64 T four zeros6 four zeros6 zeros21 in
  let expected = BoundedTaylor64 T two zeros6 two zeros6 zeros21 in
  bounded_taylor64_sqrt radii two two quarter quarter thirty_second
      source = SOME expected ∧
  bounded_taylor64_sqrt radii four two quarter quarter thirty_second
      source = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
