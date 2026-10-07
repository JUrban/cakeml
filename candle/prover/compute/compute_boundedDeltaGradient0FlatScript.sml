(*
  Allocation discriminator for the complete gradient-0 instruction.

  This keeps the proved word arithmetic and exact result unchanged while
  removing the two transient eleven-element signed-sum lists and the
  ten-element product list from the per-box hot path.
*)
Theory compute_boundedDeltaGradient0Flat
Ancestors
  compute_boundedDeltaGradient0
Libs
  bossLib preamble

Definition bounded_signed128_option_add_def:
  bounded_signed128_option_add NONE value = NONE ∧
  bounded_signed128_option_add (SOME accumulator) value =
    bounded_signed128_add accumulator value
End

Definition bounded_signed128_sum11_def:
  bounded_signed128_sum11
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 =
    bounded_signed128_option_add
      (bounded_signed128_option_add
        (bounded_signed128_option_add
          (bounded_signed128_option_add
            (bounded_signed128_option_add
              (bounded_signed128_option_add
                (bounded_signed128_option_add
                  (bounded_signed128_option_add
                    (bounded_signed128_option_add
                      (bounded_signed128_option_add
                        (bounded_signed128_option_add
                          (SOME bounded_signed128_zero) v0) v1) v2) v3) v4)
                    v5) v6) v7) v8) v9) v10
End

Definition bounded_delta_gradient0_flat_coordinates_def:
  bounded_delta_gradient0_flat_coordinates x0 x1 x2 x3 x4 x5 =
    case bounded_positive_interval_mul x0 x3 of
    | NONE => NONE
    | SOME p03 =>
      case bounded_positive_interval_mul x1 x3 of
      | NONE => NONE
      | SOME p13 =>
        case bounded_positive_interval_mul x1 x4 of
        | NONE => NONE
        | SOME p14 =>
          case bounded_positive_interval_mul x1 x5 of
          | NONE => NONE
          | SOME p15 =>
            case bounded_positive_interval_mul x2 x3 of
            | NONE => NONE
            | SOME p23 =>
              case bounded_positive_interval_mul x2 x4 of
              | NONE => NONE
              | SOME p24 =>
                case bounded_positive_interval_mul x2 x5 of
                | NONE => NONE
                | SOME p25 =>
                  case bounded_positive_interval_mul x3 x3 of
                  | NONE => NONE
                  | SOME p33 =>
                    case bounded_positive_interval_mul x3 x4 of
                    | NONE => NONE
                    | SOME p34 =>
                      case bounded_positive_interval_mul x3 x5 of
                      | NONE => NONE
                      | SOME p35 =>
                        case bounded_signed128_sum11
                          (bounded_signed128_neg (SND p03))
                          (bounded_signed128_neg (SND p03))
                          (FST p13) (FST p14)
                          (bounded_signed128_neg (SND p15))
                          (FST p23)
                          (bounded_signed128_neg (SND p24))
                          (FST p25)
                          (bounded_signed128_neg (SND p33))
                          (FST p34) (FST p35) of
                        | NONE => NONE
                        | SOME lower =>
                          case bounded_signed128_sum11
                            (bounded_signed128_neg (FST p03))
                            (bounded_signed128_neg (FST p03))
                            (SND p13) (SND p14)
                            (bounded_signed128_neg (FST p15))
                            (SND p23)
                            (bounded_signed128_neg (FST p24))
                            (SND p25)
                            (bounded_signed128_neg (FST p33))
                            (SND p34) (SND p35) of
                          | NONE => NONE
                          | SOME upper => SOME (lower,upper)
End

Definition bounded_delta_gradient0_flat_box_def:
  bounded_delta_gradient0_flat_box box =
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
                    bounded_delta_gradient0_flat_coordinates
                      x0 x1 x2 x3 x4 x5
End

Definition bounded_delta_gradient0_flat_batch_def:
  bounded_delta_gradient0_flat_batch [] (count:word64) digest =
    SOME (count,digest) ∧
  bounded_delta_gradient0_flat_batch
      (BoundedCase16594Input box box_sqrt center_sqrt::rest)
      (count:word64) digest =
    case bounded_delta_gradient0_flat_box box of
    | NONE => NONE
    | SOME (lower,upper) =>
        bounded_delta_gradient0_flat_batch rest (count + 1w)
          (bounded_signed128_digest upper
            (bounded_signed128_digest lower digest))
End

Definition bounded_delta_gradient0_flat_complete_ok_def:
  bounded_delta_gradient0_flat_complete_ok (u:unit) =
    (bounded_delta_gradient0_flat_batch bounded_case16594_inputs
       (0w:word64) 0w =
       SOME ((875w:word64),111527807236922w))
End

Definition bounded_delta_gradient0_flat_repeat_def:
  bounded_delta_gradient0_flat_repeat 0 = T ∧
  bounded_delta_gradient0_flat_repeat (SUC remaining) =
    (bounded_delta_gradient0_flat_complete_ok () ∧
     bounded_delta_gradient0_flat_repeat remaining)
End

Theorem bounded_signed128_sum11_eq:
  bounded_signed128_sum11
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 =
    bounded_signed128_sum [v0;v1;v2;v3;v4;v5;v6;v7;v8;v9;v10]
Proof
  simp [bounded_signed128_sum11_def, bounded_signed128_option_add_def,
        bounded_signed128_sum_def, bounded_signed128_sum_aux_def]
  >> every_case_tac
  >> simp [bounded_signed128_option_add_def]
QED

Theorem bounded_delta_gradient0_flat_box_eq:
  bounded_delta_gradient0_flat_box box = bounded_delta_gradient0_box box
Proof
  simp [bounded_delta_gradient0_flat_box_def,
        bounded_delta_gradient0_flat_coordinates_def,
        bounded_delta_gradient0_box_def,
        bounded_positive_interval_products_def,
        bounded_delta_gradient0_from_products_def,
        bounded_signed128_sum11_eq]
  >> every_case_tac
  >> simp [bounded_positive_interval_products_def,
           bounded_delta_gradient0_from_products_def,
           bounded_signed128_sum11_eq]
QED

Theorem bounded_delta_gradient0_flat_batch_eq:
  ∀inputs count digest.
    bounded_delta_gradient0_flat_batch inputs count digest =
    bounded_delta_gradient0_batch inputs count digest
Proof
  Induct
  >> simp [bounded_delta_gradient0_flat_batch_def,
           bounded_delta_gradient0_batch_def]
  >> Cases_on `h`
  >> simp [bounded_delta_gradient0_flat_batch_def,
           bounded_delta_gradient0_batch_def,
           bounded_delta_gradient0_flat_box_eq]
QED

Theorem bounded_delta_gradient0_flat_complete_ok_eq:
  bounded_delta_gradient0_flat_complete_ok u =
  bounded_delta_gradient0_complete_ok u
Proof
  simp [bounded_delta_gradient0_flat_complete_ok_def,
        bounded_delta_gradient0_complete_ok_def,
        bounded_delta_gradient0_flat_batch_eq]
QED

Theorem bounded_delta_gradient0_flat_unit_test:
  bounded_delta_gradient0_flat_box
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
  rw [bounded_delta_gradient0_flat_box_eq,
      bounded_delta_gradient0_unit_test]
QED

val _ = export_theory ();
