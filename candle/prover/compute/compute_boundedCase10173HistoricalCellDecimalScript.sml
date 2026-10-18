(*****************************************************************************
 * Complete case-10173 historical cell at decimal scale 10^12.
 *
 * The packet supplies untrusted fixed-point roots and reciprocals.  This
 * checker validates them, recomputes both dihedral jets, and performs the
 * final Taylor completion.  It contains no expected numerical verdict.
 *****************************************************************************)
Theory compute_boundedCase10173HistoricalCellDecimal
Ancestors
  compute_boundedHistoricalDihedralSecondDecimal
  compute_boundedCase10173HistoricalCell
  compute_boundedTaylorSqrtDecimal
Libs
  bossLib preamble

Definition bounded_interval64_unit_vector_decimal_def:
  bounded_interval64_unit_vector_decimal index =
    if index < 6 then
      SOME
        (GENLIST
          (\position.
             if position = index then bounded_atan_one_decimal
             else bounded_interval64_zero)
          6)
    else NONE
End

Definition bounded_taylor64_variable_decimal_def:
  bounded_taylor64_variable_decimal center_environment box_environment index =
    if LENGTH center_environment <> 6 \/ LENGTH box_environment <> 6
    then NONE
    else
      case bounded_interval64_unit_vector_decimal index of
      | NONE => NONE
      | SOME gradient =>
        case bounded_interval64_nth center_environment index of
        | NONE => NONE
        | SOME center_value =>
          case bounded_interval64_nth box_environment index of
          | NONE => NONE
          | SOME box_value =>
              bounded_taylor64_make T center_value gradient
                box_value gradient (bounded_interval64_zeros 21)
End

Definition bounded_case10173_root_coefficients_decimal_def:
  bounded_case10173_root_coefficients_decimal =
    [BoundedInterval64
       (BoundedSigned64 F 273298000000w)
       (BoundedSigned64 F 273298000000w);
     BoundedInterval64
       (BoundedSigned64 T 273853000000w)
       (BoundedSigned64 T 273853000000w);
     BoundedInterval64
       (BoundedSigned64 T 273853000000w)
       (BoundedSigned64 T 273853000000w);
     BoundedInterval64
       (BoundedSigned64 F 708818000000w)
       (BoundedSigned64 F 708818000000w);
     BoundedInterval64
       (BoundedSigned64 T 313988000000w)
       (BoundedSigned64 T 313988000000w);
     BoundedInterval64
       (BoundedSigned64 T 313988000000w)
       (BoundedSigned64 T 313988000000w)]
End

Definition bounded_case10173_source_constant_decimal_def:
  bounded_case10173_source_constant_decimal =
    BoundedInterval64
      (BoundedSigned64 F 1614938360000w)
      (BoundedSigned64 F 1614938360000w)
End

Definition bounded_case10173_angle_coefficient_decimal_def:
  bounded_case10173_angle_coefficient_decimal =
    BoundedInterval64
      (BoundedSigned64 T 1000000000000w)
      (BoundedSigned64 T 1000000000000w)
End

Definition bounded_case10173_deferred_scale_decimal_def:
  bounded_case10173_deferred_scale_decimal coefficient source =
    if ¬bounded_interval64_valid coefficient \/
       ¬bounded_taylor64_well_formed source
    then NONE
    else
      case source of
      | BoundedTaylor64 domain_flag center_value center_gradient
          value_bound gradient_bounds hessian =>
        case bounded_interval64_mul_decimal coefficient center_value of
        | NONE => NONE
        | SOME scaled_value =>
          case bounded_interval64_list_scale_decimal coefficient center_gradient of
          | NONE => NONE
          | SOME scaled_gradient =>
            case bounded_interval64_list_scale_decimal coefficient hessian of
            | NONE => NONE
            | SOME scaled_hessian =>
                bounded_taylor64_make domain_flag scaled_value scaled_gradient
                  bounded_interval64_zero (bounded_interval64_zeros 6)
                  scaled_hessian
End

Definition bounded_case10173_u_guards_decimal_def:
  bounded_case10173_u_guards_decimal environment <=>
    case bounded_historical_u126_decimal environment of
    | NONE => F
    | SOME (u126,u126_gradient) =>
      case bounded_historical_u135_decimal environment of
      | NONE => F
      | SOME (u135,u135_gradient) =>
          bounded_signed64_strict_positive
            (bounded_interval64_lower u126) /\
          bounded_signed64_strict_positive
            (bounded_interval64_lower u135)
End

Definition bounded_case10173_add_coordinate_sqrts_decimal_def:
  bounded_case10173_add_coordinate_sqrts_decimal radii center_environment
      box_environment [] [] index accumulator =
    (if index = 6 then SOME accumulator else NONE) /\
  bounded_case10173_add_coordinate_sqrts_decimal radii center_environment
      box_environment
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
         center_derivative box_derivative box_second_reciprocal::certificates)
      (coefficient::coefficients) index accumulator =
    (if 6 <= index then NONE
     else
       case bounded_taylor64_variable_decimal
         center_environment box_environment index of
       | NONE => NONE
       | SOME variable =>
         case bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
           center_derivative box_derivative box_second_reciprocal variable of
         | NONE => NONE
         | SOME root =>
           case bounded_case10173_defer root of
           | NONE => NONE
           | SOME deferred_root =>
             case bounded_case10173_deferred_scale_decimal
               coefficient deferred_root of
             | NONE => NONE
             | SOME scaled_root =>
               case bounded_case10173_deferred_add accumulator scaled_root of
               | NONE => NONE
               | SOME next =>
                   bounded_case10173_add_coordinate_sqrts_decimal radii
                     center_environment box_environment certificates
                     coefficients (SUC index) next) /\
  bounded_case10173_add_coordinate_sqrts_decimal radii center_environment
      box_environment _ _ index accumulator = NONE
End

Definition bounded_case10173_complete_deferred_decimal_def:
  bounded_case10173_complete_deferred_decimal radii
      (BoundedTaylor64 domain_flag center_value center_gradient
        value_bound gradient_bounds hessian) =
    bounded_taylor64_complete_decimal
      radii domain_flag center_value center_gradient hessian
End

Definition bounded_case10173_checked_cell64_decimal_def:
  bounded_case10173_checked_cell64_decimal radii center_environment
      box_environment coordinate_sqrt_certificates
      center_root_delta center_root_four_x0 center_reciprocals
      box_root_delta box_root_four_x0 box_reciprocals =
    if ¬bounded_case10173_geometry_ok
         box_environment center_environment radii 0 \/
       ¬bounded_case10173_positive_environment center_environment \/
       ¬bounded_case10173_positive_environment box_environment \/
       ¬bounded_case10173_u_guards_decimal center_environment \/
       ¬bounded_case10173_u_guards_decimal box_environment
    then NONE
    else
      case bounded_taylor64_constant
        bounded_case10173_source_constant_decimal of
      | NONE => NONE
      | SOME source_constant =>
        case bounded_case10173_defer source_constant of
        | NONE => NONE
        | SOME initial =>
          case bounded_case10173_add_coordinate_sqrts_decimal radii
            center_environment box_environment coordinate_sqrt_certificates
            bounded_case10173_root_coefficients_decimal 0 initial of
          | NONE => NONE
          | SOME roots_and_constant =>
            case bounded_historical_dihedral_first64_decimal center_environment
              center_root_delta center_root_four_x0 center_reciprocals of
            | NONE => NONE
            | SOME (center_value,center_gradient) =>
              case bounded_historical_dihedral_second64_decimal box_environment
                box_root_delta box_root_four_x0 box_reciprocals of
              | NONE => NONE
              | SOME (box_value,box_gradient,hessian) =>
                case bounded_taylor64_complete_decimal radii T
                  center_value center_gradient hessian of
                | NONE => NONE
                | SOME historical_item =>
                  case bounded_case10173_angle_state
                    (center_value,center_gradient)
                    (box_value,box_gradient,hessian) of
                  | NONE => NONE
                  | SOME angle =>
                    case bounded_case10173_defer angle of
                    | NONE => NONE
                    | SOME deferred_angle =>
                      case bounded_case10173_deferred_scale_decimal
                        bounded_case10173_angle_coefficient_decimal
                        deferred_angle of
                      | NONE => NONE
                      | SOME scaled_angle =>
                        case bounded_case10173_deferred_add
                          roots_and_constant scaled_angle of
                        | NONE => NONE
                        | SOME complete_source =>
                            bounded_case10173_complete_deferred_decimal
                              radii complete_source
End

Definition bounded_case10173_checked_cell_accepts_decimal_def:
  bounded_case10173_checked_cell_accepts_decimal radii center_environment
      box_environment coordinate_sqrt_certificates
      center_root_delta center_root_four_x0 center_reciprocals
      box_root_delta box_root_four_x0 box_reciprocals <=>
    case bounded_case10173_checked_cell64_decimal radii center_environment
      box_environment coordinate_sqrt_certificates
      center_root_delta center_root_four_x0 center_reciprocals
      box_root_delta box_root_four_x0 box_reciprocals of
    | NONE => F
    | SOME
        (BoundedTaylor64 domain_flag center_value center_gradient
          value_bound gradient_bounds hessian) =>
        domain_flag /\ bounded_signed64_strict_negative
          (bounded_interval64_upper value_bound)
End

Theorem bounded_taylor64_variable_decimal_some:
  bounded_taylor64_variable_decimal center_environment box_environment index =
    SOME result ==>
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_variable_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorStateTheory.bounded_taylor64_make_some
QED

Theorem bounded_case10173_deferred_scale_decimal_some:
  bounded_case10173_deferred_scale_decimal coefficient source = SOME result ==>
  bounded_taylor64_well_formed result
Proof
  rw [bounded_case10173_deferred_scale_decimal_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac
       [compute_boundedTaylorStateTheory.bounded_taylor64_make_some]
QED

Theorem bounded_case10173_complete_deferred_decimal_some:
  bounded_case10173_complete_deferred_decimal radii source = SOME result ==>
  bounded_taylor64_well_formed result
Proof
  Cases_on `source`
  >> rw [bounded_case10173_complete_deferred_decimal_def]
  >> metis_tac
       [compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_some]
QED

Theorem bounded_case10173_checked_cell64_decimal_some:
  bounded_case10173_checked_cell64_decimal radii center_environment
      box_environment coordinate_sqrt_certificates
      center_root_delta center_root_four_x0 center_reciprocals
      box_root_delta box_root_four_x0 box_reciprocals = SOME result ==>
  bounded_taylor64_well_formed result
Proof
  rw [bounded_case10173_checked_cell64_decimal_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_case10173_complete_deferred_decimal_some]
QED

Theorem bounded_case10173_checked_cell_accepts_decimal_contract:
  bounded_case10173_checked_cell_accepts_decimal radii center_environment
      box_environment coordinate_sqrt_certificates
      center_root_delta center_root_four_x0 center_reciprocals
      box_root_delta box_root_four_x0 box_reciprocals ==>
  ?center_value center_gradient value_bound gradient_bounds hessian.
    bounded_case10173_checked_cell64_decimal radii center_environment
      box_environment coordinate_sqrt_certificates
      center_root_delta center_root_four_x0 center_reciprocals
      box_root_delta box_root_four_x0 box_reciprocals =
        SOME (BoundedTaylor64 T center_value center_gradient
          value_bound gradient_bounds hessian) /\
    bounded_signed64_strict_negative
      (bounded_interval64_upper value_bound)
Proof
  rw [bounded_case10173_checked_cell_accepts_decimal_def]
  >> every_case_tac
  >> gvs []
QED

val _ = export_theory ();
