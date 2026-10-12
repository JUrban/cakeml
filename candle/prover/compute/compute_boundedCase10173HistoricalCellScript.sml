(*****************************************************************************
 * Complete checked-word historical cell for genuine Flyspeck case 10173.
 *
 * This is the numerical core of the registered fast route.  It evaluates
 * the six source coordinate square roots, the frozen source constant, and
 * the historical dihedral center/box jets, then performs one final Taylor
 * completion.  Supplied roots and reciprocals remain untrusted certificates.
 * Expected intermediate or final jets are deliberately absent.
 *****************************************************************************)
Theory compute_boundedCase10173HistoricalCell
Ancestors
  compute_boundedHistoricalDihedralSecond compute_boundedTaylorSqrt
Libs
  bossLib preamble

Datatype:
  bounded_case10173_sqrt64_certificate =
    BoundedCase10173Sqrt64Certificate
      bounded_interval64 bounded_interval64 bounded_interval64
      bounded_interval64 bounded_interval64
End

(* Outward scale-2^40 encodings of the authenticated source coefficients.
 * Their rational identities are, in order,
 *
 *   136649/500000, -273853/1000000, -273853/1000000,
 *   354409/500000, -78497/250000, -78497/250000.
 *
 * The source-identity theorem connecting these words to the original
 * reflected expression belongs at the enclosing registered-plan boundary. *)
Definition bounded_case10173_root_coefficients_def:
  bounded_case10173_root_coefficients =
    [BoundedInterval64
       (BoundedSigned64 F 300494328847w)
       (BoundedSigned64 F 300494328848w);
     BoundedInterval64
       (BoundedSigned64 T 301104557802w)
       (BoundedSigned64 T 301104557801w);
     BoundedInterval64
       (BoundedSigned64 T 301104557802w)
       (BoundedSigned64 T 301104557801w);
     BoundedInterval64
       (BoundedSigned64 F 779353632976w)
       (BoundedSigned64 F 779353632977w);
     BoundedInterval64
       (BoundedSigned64 T 345233456983w)
       (BoundedSigned64 T 345233456982w);
     BoundedInterval64
       (BoundedSigned64 T 345233456983w)
       (BoundedSigned64 T 345233456982w)]
End

(* The seven source constants sum to 40373459/25000000.  Preserve the
 * production algorithm's separately outward-rounded accumulation here;
 * it is intentionally seven units wider than rounding the rational sum
 * only once. *)
Definition bounded_case10173_source_constant_def:
  bounded_case10173_source_constant =
    BoundedInterval64
      (BoundedSigned64 F 1775643504958w)
      (BoundedSigned64 F 1775643504965w)
End

(* Exact encoding of the source's coefficient -1 on the dihedral term. *)
Definition bounded_case10173_angle_coefficient_def:
  bounded_case10173_angle_coefficient =
    BoundedInterval64
      (BoundedSigned64 T 1099511627776w)
      (BoundedSigned64 T 1099511627776w)
End

(* Keep only the center jet and Hessian.  Native HOL Light postpones Taylor
 * completion across additive terms so cancellation is not lost. *)
Definition bounded_case10173_defer_def:
  bounded_case10173_defer
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) =
    bounded_taylor64_make domain center_value center_gradient
      bounded_interval64_zero (bounded_interval64_zeros 6) hessian
End

Definition bounded_case10173_deferred_scale_def:
  bounded_case10173_deferred_scale coefficient source =
    if ¬bounded_interval64_valid coefficient ∨
       ¬bounded_taylor64_well_formed source
    then NONE
    else
      case source of
      | BoundedTaylor64 domain center_value center_gradient
          value_bound gradient_bounds hessian =>
        case bounded_interval64_mul coefficient center_value of
        | NONE => NONE
        | SOME scaled_value =>
          case bounded_interval64_list_scale coefficient center_gradient of
          | NONE => NONE
          | SOME scaled_gradient =>
            case bounded_interval64_list_scale coefficient hessian of
            | NONE => NONE
            | SOME scaled_hessian =>
                bounded_taylor64_make domain scaled_value scaled_gradient
                  bounded_interval64_zero (bounded_interval64_zeros 6)
                  scaled_hessian
End

Definition bounded_case10173_deferred_add_def:
  bounded_case10173_deferred_add left right =
    bounded_taylor64_add left right
End

(* The supplied center and radius must cover the original box and the center
 * must itself lie in that box.  This admits reusable externally prepared
 * geometry without trusting it. *)
Definition bounded_case10173_radius_covers_def:
  bounded_case10173_radius_covers box center radius =
    if ¬bounded_interval64_valid box ∨
       ¬bounded_interval64_valid center
    then F
    else
      case bounded_signed64_add (bounded_interval64_lower center)
        (BoundedSigned64 T radius) of
      | NONE => F
      | SOME left_extent =>
        case bounded_signed64_add (bounded_interval64_upper center)
          (BoundedSigned64 F radius) of
        | NONE => F
        | SOME right_extent =>
            bounded_signed64_le (bounded_interval64_lower box)
              (bounded_interval64_lower center) ∧
            bounded_signed64_le (bounded_interval64_upper center)
              (bounded_interval64_upper box) ∧
            bounded_signed64_le left_extent
              (bounded_interval64_lower box) ∧
            bounded_signed64_le (bounded_interval64_upper box)
              right_extent
End

Definition bounded_case10173_geometry_ok_def:
  bounded_case10173_geometry_ok [] [] [] count = (count = 6) ∧
  bounded_case10173_geometry_ok (box::boxes) (center::centers)
      (radius::radii) count =
    (bounded_case10173_radius_covers box center radius ∧
     bounded_case10173_geometry_ok boxes centers radii (SUC count)) ∧
  bounded_case10173_geometry_ok _ _ _ count = F
End

Definition bounded_case10173_positive_environment_def:
  bounded_case10173_positive_environment environment ⇔
    LENGTH environment = 6 ∧
    EVERY
      (λvalue.
         bounded_interval64_valid value ∧
         bounded_signed64_strict_positive
           (bounded_interval64_lower value))
      environment
End

Definition bounded_case10173_u_guards_def:
  bounded_case10173_u_guards environment ⇔
    case bounded_historical_u126 environment of
    | NONE => F
    | SOME (u126,u126_gradient) =>
      case bounded_historical_u135 environment of
      | NONE => F
      | SOME (u135,u135_gradient) =>
          bounded_signed64_strict_positive
            (bounded_interval64_lower u126) ∧
          bounded_signed64_strict_positive
            (bounded_interval64_lower u135)
End

Definition bounded_case10173_add_coordinate_sqrts_def:
  bounded_case10173_add_coordinate_sqrts radii center_environment
      box_environment [] [] index accumulator =
    (if index = 6 then SOME accumulator else NONE) ∧
  bounded_case10173_add_coordinate_sqrts radii center_environment
      box_environment
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
         center_derivative box_derivative box_second_reciprocal::certificates)
      (coefficient::coefficients) index accumulator =
    (if 6 ≤ index then NONE
     else
       case bounded_taylor64_variable
         center_environment box_environment index of
       | NONE => NONE
       | SOME variable =>
         case bounded_taylor64_sqrt radii center_sqrt box_sqrt
           center_derivative box_derivative box_second_reciprocal variable of
         | NONE => NONE
         | SOME root =>
           case bounded_case10173_defer root of
           | NONE => NONE
           | SOME deferred_root =>
             case bounded_case10173_deferred_scale
               coefficient deferred_root of
             | NONE => NONE
             | SOME scaled_root =>
               case bounded_case10173_deferred_add accumulator scaled_root of
               | NONE => NONE
               | SOME next =>
                   bounded_case10173_add_coordinate_sqrts radii
                     center_environment box_environment certificates
                     coefficients (SUC index) next) ∧
  bounded_case10173_add_coordinate_sqrts radii center_environment
      box_environment _ _ index accumulator = NONE
End

Definition bounded_case10173_angle_state_def:
  bounded_case10173_angle_state center_result box_result =
    case center_result of
    | (center_value,center_gradient) =>
      case box_result of
      | (box_value,box_gradient,hessian) =>
          bounded_taylor64_make T center_value center_gradient
            box_value box_gradient hessian
End

Definition bounded_case10173_complete_deferred_def:
  bounded_case10173_complete_deferred radii
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) =
    bounded_taylor64_complete radii domain center_value center_gradient hessian
End

Definition bounded_case10173_checked_cell64_def:
  bounded_case10173_checked_cell64 radii center_environment box_environment
      coordinate_sqrt_certificates
      center_root_delta center_root_four_x0 center_reciprocals
      box_root_delta box_root_four_x0 box_reciprocals =
    if ¬bounded_case10173_geometry_ok
         box_environment center_environment radii 0 ∨
       ¬bounded_case10173_positive_environment center_environment ∨
       ¬bounded_case10173_positive_environment box_environment ∨
       ¬bounded_case10173_u_guards center_environment ∨
       ¬bounded_case10173_u_guards box_environment
    then NONE
    else
      case bounded_taylor64_constant bounded_case10173_source_constant of
      | NONE => NONE
      | SOME source_constant =>
        case bounded_case10173_defer source_constant of
        | NONE => NONE
        | SOME initial =>
          case bounded_case10173_add_coordinate_sqrts radii
            center_environment box_environment coordinate_sqrt_certificates
            bounded_case10173_root_coefficients 0 initial of
          | NONE => NONE
          | SOME roots_and_constant =>
            case bounded_historical_dihedral_first64 center_environment
              center_root_delta center_root_four_x0 center_reciprocals of
            | NONE => NONE
            | SOME center_result =>
              case bounded_historical_dihedral_second64 box_environment
                box_root_delta box_root_four_x0 box_reciprocals of
              | NONE => NONE
              | SOME box_result =>
                case bounded_case10173_angle_state
                  center_result box_result of
                | NONE => NONE
                | SOME angle =>
                  case bounded_case10173_defer angle of
                  | NONE => NONE
                  | SOME deferred_angle =>
                    case bounded_case10173_deferred_scale
                      bounded_case10173_angle_coefficient deferred_angle of
                    | NONE => NONE
                    | SOME scaled_angle =>
                      case bounded_case10173_deferred_add
                        roots_and_constant scaled_angle of
                      | NONE => NONE
                      | SOME complete_source =>
                          bounded_case10173_complete_deferred
                            radii complete_source
End

Definition bounded_case10173_checked_cell_accepts_def:
  bounded_case10173_checked_cell_accepts radii center_environment
      box_environment coordinate_sqrt_certificates
      center_root_delta center_root_four_x0 center_reciprocals
      box_root_delta box_root_four_x0 box_reciprocals ⇔
    case bounded_case10173_checked_cell64 radii center_environment
      box_environment coordinate_sqrt_certificates
      center_root_delta center_root_four_x0 center_reciprocals
      box_root_delta box_root_four_x0 box_reciprocals of
    | NONE => F
    | SOME
        (BoundedTaylor64 domain center_value center_gradient
          value_bound gradient_bounds hessian) =>
        domain ∧ bounded_signed64_strict_negative
          (bounded_interval64_upper value_bound)
End

Theorem bounded_case10173_defer_some:
  bounded_case10173_defer source = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  Cases_on `source`
  >> rw [bounded_case10173_defer_def]
  >> metis_tac
       [compute_boundedTaylorStateTheory.bounded_taylor64_make_some]
QED

Theorem bounded_case10173_deferred_scale_some:
  bounded_case10173_deferred_scale coefficient source = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_case10173_deferred_scale_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac
       [compute_boundedTaylorStateTheory.bounded_taylor64_make_some]
QED

Theorem bounded_case10173_complete_deferred_some:
  bounded_case10173_complete_deferred radii source = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  Cases_on `source`
  >> rw [bounded_case10173_complete_deferred_def]
  >> metis_tac
       [compute_boundedTaylorUnaryTheory.bounded_taylor64_complete_some]
QED

Theorem bounded_case10173_checked_cell64_some:
  bounded_case10173_checked_cell64 radii center_environment box_environment
      coordinate_sqrt_certificates
      center_root_delta center_root_four_x0 center_reciprocals
      box_root_delta box_root_four_x0 box_reciprocals = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_case10173_checked_cell64_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_case10173_complete_deferred_some]
QED

val _ = export_theory ();
