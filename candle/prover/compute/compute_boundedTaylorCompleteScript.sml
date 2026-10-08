(*****************************************************************************
 * Compact six-dimensional Taylor value completion over checked words.
 *
 * The checker consumes only six radii, six center-gradient intervals, the
 * twenty-one independent entries of a symmetric Hessian, and a center-value
 * interval.  It returns one outward-rounded value interval or NONE.  Thus no
 * per-operation theorem objects or dense intermediate matrices cross the
 * executable boundary.
 *
 * This remains DEVELOPMENT code until the wide-operation refinements and the
 * complete analytic/source soundness bridge are discharged.
 *****************************************************************************)
Theory compute_boundedTaylorComplete
Ancestors
  compute_boundedTaylorState compute_boundedWideSigned
Libs
  bossLib preamble

Definition bounded_interval64_abs_upper_def:
  bounded_interval64_abs_upper (BoundedInterval64 lower upper) =
    let lower_magnitude = bounded_signed64_magnitude lower in
    let upper_magnitude = bounded_signed64_magnitude upper in
    if word_lo lower_magnitude upper_magnitude then
      upper_magnitude
    else lower_magnitude
End

Definition bounded_word64_product128_def:
  bounded_word64_product128 (left:word64) (right:word64) =
    let product = bounded_word64_mul_full_chunks22 left right in
    Bounded128 (FST product) (SND product)
End

Definition bounded_dot_abs_upper_acc_def:
  bounded_dot_abs_upper_acc [] [] accumulator = SOME accumulator ∧
  bounded_dot_abs_upper_acc [] (_::_) accumulator = NONE ∧
  bounded_dot_abs_upper_acc (_::_) [] accumulator = NONE ∧
  bounded_dot_abs_upper_acc (radius::radii) (entry::entries) accumulator =
    let product = bounded_word64_product128 radius
      (bounded_interval64_abs_upper entry) in
    case bounded128_add_words accumulator product of
    | NONE => NONE
    | SOME next => bounded_dot_abs_upper_acc radii entries next
End

Definition bounded_dot_abs_upper_def:
  bounded_dot_abs_upper radii entries =
    bounded_dot_abs_upper_acc radii entries (Bounded128 0w 0w)
End

Definition bounded_taylor_radius_pairs_def:
  bounded_taylor_radius_pairs radii =
    case radii of
    | r0::r1::r2::r3::r4::r5::[] =>
        SOME
          [(r0,r0,F);
           (r0,r1,T); (r0,r2,T); (r0,r3,T); (r0,r4,T); (r0,r5,T);
           (r1,r1,F);
           (r1,r2,T); (r1,r3,T); (r1,r4,T); (r1,r5,T);
           (r2,r2,F);
           (r2,r3,T); (r2,r4,T); (r2,r5,T);
           (r3,r3,F);
           (r3,r4,T); (r3,r5,T);
           (r4,r4,F);
           (r4,r5,T);
           (r5,r5,F)]
    | _ => NONE
End

Definition bounded_quadratic_abs_upper_acc_def:
  bounded_quadratic_abs_upper_acc [] [] accumulator = SOME accumulator ∧
  bounded_quadratic_abs_upper_acc [] (_::_) accumulator = NONE ∧
  bounded_quadratic_abs_upper_acc (_::_) [] accumulator = NONE ∧
  bounded_quadratic_abs_upper_acc
      ((left_radius,right_radius,double)::weights)
      (entry::entries) accumulator =
    let radius_product =
      bounded_word64_product128 left_radius right_radius in
    case bounded128_mul_word64_to_192_words radius_product
      (bounded_interval64_abs_upper entry) of
    | NONE => NONE
    | SOME raw_contribution =>
      case
        (if double then
           bounded192_add_words raw_contribution raw_contribution
         else SOME raw_contribution) of
      | NONE => NONE
      | SOME contribution =>
        case bounded192_add_words accumulator contribution of
        | NONE => NONE
        | SOME next =>
            bounded_quadratic_abs_upper_acc weights entries next
End

Definition bounded_quadratic_abs_upper_def:
  bounded_quadratic_abs_upper radii hessian =
    case bounded_taylor_radius_pairs radii of
    | NONE => NONE
    | SOME weights =>
        bounded_quadratic_abs_upper_acc
          weights hessian bounded192_zero
End

Definition bounded_taylor_error_def:
  bounded_taylor_error radii center_gradient hessian =
    case bounded_dot_abs_upper radii center_gradient of
    | NONE => NONE
    | SOME linear =>
      case bounded_quadratic_abs_upper radii hessian of
      | NONE => NONE
      | SOME quadratic =>
          bounded192_add_words (bounded128_scale41 linear) quadratic
End

Definition bounded_taylor_value_complete_def:
  bounded_taylor_value_complete radii center_value center_gradient hessian =
    case bounded_taylor_error radii center_gradient hessian of
    | NONE => NONE
    | SOME error =>
      case center_value of
      | BoundedInterval64 center_lower center_upper =>
        case bounded_signed192_add
          (bounded_signed64_scale81 center_lower)
          (bounded_signed192_make T error) of
        | NONE => NONE
        | SOME raw_lower =>
          case bounded_signed192_add
            (bounded_signed64_scale81 center_upper)
            (bounded_signed192_make F error) of
          | NONE => NONE
          | SOME raw_upper =>
            case bounded_signed192_shift_floor81_64 raw_lower of
            | NONE => NONE
            | SOME lower =>
              case bounded_signed192_shift_ceil81_64 raw_upper of
              | NONE => NONE
              | SOME upper => SOME (BoundedInterval64 lower upper)
End

Theorem bounded_taylor_radius_pairs_shape_tests:
  bounded_taylor_radius_pairs [1w;2w;3w;4w;5w] = NONE ∧
  case bounded_taylor_radius_pairs [1w;2w;3w;4w;5w;6w] of
  | NONE => F
  | SOME weights => LENGTH weights = 21
Proof
  EVAL_TAC
QED

Theorem bounded_taylor_value_closed_tests:
  let zeros6 = REPLICATE 6 bounded_interval64_zero in
  let zeros21 = REPLICATE 21 bounded_interval64_zero in
  let radii = [2w;0w;0w;0w;0w;0w] in
  let point3 = BoundedInterval64
    (BoundedSigned64 F 3w) (BoundedSigned64 F 3w) in
  let gradient = point3::TL zeros6 in
  bounded_dot_abs_upper radii gradient = SOME (Bounded128 0w 6w) ∧
  bounded_quadratic_abs_upper radii zeros21 =
    SOME (Bounded192 0w 0w 0w) ∧
  bounded_taylor_value_complete radii bounded_interval64_zero
      gradient zeros21 =
    SOME
      (BoundedInterval64
        (BoundedSigned64 T 1w) (BoundedSigned64 F 1w)) ∧
  bounded_taylor_value_complete radii
      (BoundedInterval64
        (BoundedSigned64 T 3w) (BoundedSigned64 T 2w))
      zeros6 zeros21 =
    SOME
      (BoundedInterval64
        (BoundedSigned64 T 3w) (BoundedSigned64 T 2w))
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
