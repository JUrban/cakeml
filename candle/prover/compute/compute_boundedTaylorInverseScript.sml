(*****************************************************************************
 * Checked reciprocal lift for compact Taylor states.
 *
 * Untrusted preparation supplies center and whole-box reciprocal intervals.
 * Exact endpoint-product certificates authenticate both.  The general unary
 * chain-rule lift then applies f'(x) = -r^2 and f''(x) = 2r^3.
 *****************************************************************************)
Theory compute_boundedTaylorInverse
Ancestors
  compute_boundedTaylorUnary compute_boundedReciprocalCertificate
Libs
  bossLib preamble

Definition bounded_taylor64_inverse_def:
  bounded_taylor64_inverse radii center_reciprocal box_reciprocal source =
    case source of
    | BoundedTaylor64 source_domain center_value center_gradient
        value_bound gradient_bounds hessian =>
      if ¬bounded_interval64_inv_certificate
          center_value center_reciprocal ∨
         ¬bounded_interval64_inv_certificate
          value_bound box_reciprocal
      then NONE
      else
        case bounded_interval64_mul
          center_reciprocal center_reciprocal of
        | NONE => NONE
        | SOME center_square =>
          case bounded_interval64_mul box_reciprocal box_reciprocal of
          | NONE => NONE
          | SOME box_square =>
            case bounded_interval64_mul box_square box_reciprocal of
            | NONE => NONE
            | SOME box_cube =>
              case bounded_interval64_add box_cube box_cube of
              | NONE => NONE
              | SOME box_second =>
                  bounded_taylor64_unary_complete radii T
                    center_reciprocal
                    (bounded_interval64_neg center_square)
                    (bounded_interval64_neg box_square)
                    box_second source
End

Theorem bounded_taylor64_inverse_some:
  bounded_taylor64_inverse radii center_reciprocal box_reciprocal
      source = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_inverse_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_taylor64_unary_complete_some
QED

Theorem bounded_taylor64_inverse_closed_tests:
  let zeros6 = REPLICATE 6 bounded_interval64_zero in
  let zeros21 = REPLICATE 21 bounded_interval64_zero in
  let radii = REPLICATE 6 0w in
  let one = BoundedInterval64
    (BoundedSigned64 F 1099511627776w)
    (BoundedSigned64 F 1099511627776w) in
  let two = BoundedInterval64
    (BoundedSigned64 F 2199023255552w)
    (BoundedSigned64 F 2199023255552w) in
  let state = BoundedTaylor64 T one zeros6 one zeros6 zeros21 in
  bounded_taylor64_inverse radii one one state = SOME state ∧
  bounded_taylor64_inverse radii two one state = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
