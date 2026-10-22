(*
  First complete actual-data delta-family instruction.

  This evaluates the interval enclosure for component zero of grad(delta):

    -2*x0*x3 + x1*x3 + x1*x4 - x1*x5 + x2*x3
    - x2*x4 + x2*x5 - x3*x3 + x3*x4 + x3*x5.

  All six source box coordinates are positive in the authenticated case16594
  fixture, so each pair-product enclosure uses lower*lower and upper*upper.
  Directed products and every signed accumulation step are the checked word
  operations from the preceding theories.
*)
Theory compute_boundedDeltaGradient0
Ancestors
  compute_boundedSignedAdd compute_boundedSigned
  compute_boundedCase16594InputData
Libs
  bossLib

Definition bounded_signed128_zero_def:
  bounded_signed128_zero =
    BoundedSigned128 F (Bounded128 0w 0w)
End

Definition bounded_signed128_neg_def:
  bounded_signed128_neg (BoundedSigned128 negative magnitude) =
    bounded_signed128_make (¬negative) magnitude
End

Definition bounded_signed128_sum_aux_def:
  bounded_signed128_sum_aux [] accumulator = SOME accumulator ∧
  bounded_signed128_sum_aux (value::rest) accumulator =
    case bounded_signed128_add accumulator value of
    | NONE => NONE
    | SOME next => bounded_signed128_sum_aux rest next
End

Definition bounded_signed128_sum_def:
  bounded_signed128_sum values =
    bounded_signed128_sum_aux values bounded_signed128_zero
End

Definition bounded_positive_interval_mul_def:
  bounded_positive_interval_mul
      ((left_lower:word64),left_upper)
      ((right_lower:word64),right_upper) =
    case bounded_signed_word64_mul_floor40
           (BoundedSigned64 F left_lower)
           (BoundedSigned64 F right_lower) of
    | NONE => NONE
    | SOME lower =>
        case bounded_signed_word64_mul_ceil40
               (BoundedSigned64 F left_upper)
               (BoundedSigned64 F right_upper) of
        | NONE => NONE
        | SOME upper => SOME (lower,upper)
End

Definition bounded_positive_interval_products_def:
  bounded_positive_interval_products [] = SOME [] ∧
  bounded_positive_interval_products (pair::rest) =
    case bounded_positive_interval_mul (FST pair) (SND pair) of
    | NONE => NONE
    | SOME interval =>
        case bounded_positive_interval_products rest of
        | NONE => NONE
        | SOME intervals => SOME (interval::intervals)
End

Definition bounded_delta_gradient0_from_products_def:
  bounded_delta_gradient0_from_products products =
    case products of
    | [] => NONE
    | p03::products =>
      case products of
      | [] => NONE
      | p13::products =>
        case products of
        | [] => NONE
        | p14::products =>
          case products of
          | [] => NONE
          | p15::products =>
            case products of
            | [] => NONE
            | p23::products =>
              case products of
              | [] => NONE
              | p24::products =>
                case products of
                | [] => NONE
                | p25::products =>
                  case products of
                  | [] => NONE
                  | p33::products =>
                    case products of
                    | [] => NONE
                    | p34::products =>
                      case products of
                      | [] => NONE
                      | p35::products =>
                        case products of
                        | _::_ => NONE
                        | [] =>
                          let p03_lower = FST p03;
                              p03_upper = SND p03;
                              p13_lower = FST p13;
                              p13_upper = SND p13;
                              p14_lower = FST p14;
                              p14_upper = SND p14;
                              p15_lower = FST p15;
                              p15_upper = SND p15;
                              p23_lower = FST p23;
                              p23_upper = SND p23;
                              p24_lower = FST p24;
                              p24_upper = SND p24;
                              p25_lower = FST p25;
                              p25_upper = SND p25;
                              p33_lower = FST p33;
                              p33_upper = SND p33;
                              p34_lower = FST p34;
                              p34_upper = SND p34;
                              p35_lower = FST p35;
                              p35_upper = SND p35
                          in
                            case bounded_signed128_sum
                              [bounded_signed128_neg p03_upper;
                               bounded_signed128_neg p03_upper;
                               p13_lower; p14_lower;
                               bounded_signed128_neg p15_upper;
                               p23_lower;
                               bounded_signed128_neg p24_upper;
                               p25_lower;
                               bounded_signed128_neg p33_upper;
                               p34_lower; p35_lower] of
                            | NONE => NONE
                            | SOME lower =>
                                case bounded_signed128_sum
                                  [bounded_signed128_neg p03_lower;
                                   bounded_signed128_neg p03_lower;
                                   p13_upper; p14_upper;
                                   bounded_signed128_neg p15_lower;
                                   p23_upper;
                                   bounded_signed128_neg p24_lower;
                                   p25_upper;
                                   bounded_signed128_neg p33_lower;
                                   p34_upper; p35_upper] of
                                | NONE => NONE
                                | SOME upper => SOME (lower,upper)
End

Definition bounded_delta_gradient0_box_def:
  bounded_delta_gradient0_box box =
    case box of
    | [] => NONE
    | x0::box =>
      case box of
      | [] => NONE
      | x1::box =>
        case box of
        | [] => NONE
        | x2::box =>
          case box of
          | [] => NONE
          | x3::box =>
            case box of
            | [] => NONE
            | x4::box =>
              case box of
              | [] => NONE
              | x5::box =>
                case box of
                | _::_ => NONE
                | [] =>
                    case bounded_positive_interval_products
                      [(x0,x3); (x1,x3); (x1,x4); (x1,x5); (x2,x3);
                       (x2,x4); (x2,x5); (x3,x3); (x3,x4); (x3,x5)] of
                    | NONE => NONE
                    | SOME products =>
                        bounded_delta_gradient0_from_products products
End

Definition bounded_signed128_digest_def:
  bounded_signed128_digest
      (BoundedSigned128 negative (Bounded128 high low)) digest =
    word_xor digest
      (word_xor (if negative then 18446744073709551615w else 0w)
        (word_xor high low))
End

Definition bounded_delta_gradient0_batch_def:
  bounded_delta_gradient0_batch [] (count:word64) digest =
    SOME (count,digest) ∧
  bounded_delta_gradient0_batch
      (BoundedCase16594Input box box_sqrt center_sqrt::rest)
      (count:word64) digest =
    case bounded_delta_gradient0_box box of
    | NONE => NONE
    | SOME (lower,upper) =>
        bounded_delta_gradient0_batch rest (count + 1w)
          (bounded_signed128_digest upper
            (bounded_signed128_digest lower digest))
End

Definition bounded_delta_gradient0_complete_ok_def:
  bounded_delta_gradient0_complete_ok (u:unit) =
    (bounded_delta_gradient0_batch bounded_case16594_inputs
       (0w:word64) 0w =
       SOME ((875w:word64),111527807236922w))
End

Theorem bounded_signed128_neg_normalized:
  bounded_signed128_normalized (bounded_signed128_neg value)
Proof
  Cases_on `value`
  >> simp [bounded_signed128_neg_def, bounded_signed128_make_normalized]
QED

Theorem bounded_signed128_sum_aux_normalized:
  ∀values accumulator result.
    bounded_signed128_normalized accumulator ∧
    bounded_signed128_sum_aux values accumulator = SOME result ⇒
    bounded_signed128_normalized result
Proof
  Induct
  >> rw [bounded_signed128_sum_aux_def]
  >> Cases_on `bounded_signed128_add accumulator h`
  >> fs []
  >> imp_res_tac bounded_signed128_add_normalized
  >> metis_tac []
QED

Theorem bounded_signed128_sum_normalized:
  bounded_signed128_sum values = SOME result ⇒
  bounded_signed128_normalized result
Proof
  rw [bounded_signed128_sum_def]
  >> mp_tac
       (Q.SPECL [`values`, `bounded_signed128_zero`, `result`]
          bounded_signed128_sum_aux_normalized)
  >> simp [bounded_signed128_zero_def, bounded_signed128_normalized_def]
QED

Theorem bounded_delta_gradient0_unit_test:
  bounded_delta_gradient0_box
    [(1099511627776w,1099511627776w);
     (1099511627776w,1099511627776w);
     (1099511627776w,1099511627776w);
     (1099511627776w,1099511627776w);
     (1099511627776w,1099511627776w);
     (1099511627776w,1099511627776w)] =
  SOME
    (BoundedSigned128 F (Bounded128 0w 1099511627776w),
     BoundedSigned128 F (Bounded128 0w 1099511627776w))
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
