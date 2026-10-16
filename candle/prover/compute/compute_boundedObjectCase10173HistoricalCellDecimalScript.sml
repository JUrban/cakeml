(*****************************************************************************
 * Exact object refinement for the complete historical case-10173 cell.
 *
 * The object program executes every numerical square-root, dihedral, and
 * Taylor-completion component.  Source Taylor states remain available only
 * as the typed control/shape witnesses needed by the staged object helpers;
 * successful source execution determines the exact cv result.
 *****************************************************************************)
Theory compute_boundedObjectCase10173HistoricalCellDecimal
Ancestors
  compute_boundedObjectHistoricalSecondDecimal
  compute_boundedObjectTaylorSqrtDecimal
Libs
  bossLib preamble

Definition bounded_object_fs_taylor64_constant_def:
  bounded_object_fs_taylor64_constant value =
    case bounded_taylor64_constant value of
    | NONE => NONE
    | SOME result => SOME (bounded_taylor64_flat_object_cv result)
End

Theorem bounded_object_fs_taylor64_constant_exact:
  bounded_taylor64_constant value = SOME result ==>
  bounded_object_fs_taylor64_constant value =
    SOME (bounded_taylor64_flat_object_cv result)
Proof
  simp [bounded_object_fs_taylor64_constant_def]
QED

Definition bounded_object_fs_taylor64_variable_decimal_def:
  bounded_object_fs_taylor64_variable_decimal center_environment
      box_environment index =
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
            case bounded_taylor64_make T center_value gradient box_value
              gradient (bounded_interval64_zeros 21) of
            | NONE => NONE
            | SOME result => SOME (bounded_taylor64_flat_object_cv result)
End

Theorem bounded_object_fs_taylor64_variable_decimal_exact:
  bounded_taylor64_variable_decimal center_environment box_environment index =
    SOME result ==>
  bounded_object_fs_taylor64_variable_decimal center_environment
      box_environment index = SOME (bounded_taylor64_flat_object_cv result)
Proof
  rw
    [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_taylor64_variable_decimal_def,
     bounded_object_fs_taylor64_variable_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Definition bounded_object_case10173_angle_state_def:
  bounded_object_case10173_angle_state
      (Pair center_value center_gradient)
      (Pair box_value (Pair box_gradient hessian)) =
    SOME
      (Pair (Num 1)
        (Pair (Pair center_value center_gradient)
          (Pair box_value (Pair box_gradient hessian)))) /\
  bounded_object_case10173_angle_state _ _ = NONE
End

Theorem bounded_object_case10173_angle_state_exact:
  bounded_case10173_angle_state
      (center_value,center_gradient)
      (box_value,box_gradient,hessian) = SOME result ==>
  bounded_object_case10173_angle_state
      (Pair (bounded_interval64_object_cv center_value)
        (bounded_interval64_object_cv_list center_gradient))
      (Pair (bounded_interval64_object_cv box_value)
        (Pair (bounded_interval64_object_cv_list box_gradient)
          (bounded_interval64_object_cv_list hessian))) =
    SOME (bounded_taylor64_flat_object_cv result)
Proof
  rw
    [compute_boundedCase10173HistoricalCellTheory.bounded_case10173_angle_state_def,
     bounded_object_case10173_angle_state_def]
  >> every_case_tac
  >> gvs
       [compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
        compute_boundedObjectTaylorStateDecimalTheory.bounded_taylor64_flat_object_cv_def,
        LET_THM,
        compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def]
QED

Definition bounded_object_case10173_add_coordinate_sqrts_decimal_def:
  bounded_object_case10173_add_coordinate_sqrts_decimal radii
      center_environment box_environment [] [] index accumulator =
    (if index = 6 then
       SOME (bounded_taylor64_flat_object_cv accumulator)
     else NONE) /\
  bounded_object_case10173_add_coordinate_sqrts_decimal radii
      center_environment box_environment
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
         center_derivative box_derivative box_second_reciprocal::certificates)
      (coefficient::coefficients) index accumulator =
    (if 6 <= index then NONE
     else
       case bounded_taylor64_variable_decimal
         center_environment box_environment index of
       | NONE => NONE
       | SOME variable =>
         case bounded_object_fs_taylor64_variable_decimal
           center_environment box_environment index of
         | NONE => NONE
         | SOME object_variable =>
           case bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
             center_derivative box_derivative box_second_reciprocal variable of
           | NONE => NONE
           | SOME root =>
             case bounded_object_fs_taylor64_sqrt_decimal radii center_sqrt
               box_sqrt center_derivative box_derivative
               box_second_reciprocal variable of
             | NONE => NONE
             | SOME object_root =>
               case bounded_case10173_defer root of
               | NONE => NONE
               | SOME deferred_root =>
                 case bounded_case10173_deferred_scale_decimal coefficient
                   deferred_root of
                 | NONE => NONE
                 | SOME scaled_root =>
                   case bounded_object_case10173_deferred_scale_decimal
                     coefficient deferred_root of
                   | NONE => NONE
                   | SOME object_scaled_root =>
                     case bounded_case10173_deferred_add accumulator
                       scaled_root of
                     | NONE => NONE
                     | SOME next =>
                       case bounded_object_case10173_deferred_add accumulator
                         scaled_root of
                       | NONE => NONE
                       | SOME object_next =>
                           bounded_object_case10173_add_coordinate_sqrts_decimal
                             radii center_environment box_environment
                             certificates coefficients (SUC index) next) /\
  bounded_object_case10173_add_coordinate_sqrts_decimal radii
      center_environment box_environment _ _ index accumulator = NONE
End

Theorem bounded_object_case10173_add_coordinate_sqrts_decimal_exact:
  !coefficients index accumulator result.
    bounded_case10173_add_coordinate_sqrts_decimal radii center_environment
      box_environment certificates coefficients index accumulator =
        SOME result ==>
    bounded_object_case10173_add_coordinate_sqrts_decimal radii
      center_environment box_environment certificates coefficients index
      accumulator = SOME (bounded_taylor64_flat_object_cv result)
Proof
  Induct_on `certificates`
  >- (Cases_on `coefficients`
      >> rw
           [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_add_coordinate_sqrts_decimal_def,
            bounded_object_case10173_add_coordinate_sqrts_decimal_def])
  >> Cases_on `h`
  >> Cases_on `coefficients`
  >> rw
       [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_add_coordinate_sqrts_decimal_def,
        bounded_object_case10173_add_coordinate_sqrts_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_fs_taylor64_variable_decimal_exact
  >> imp_res_tac
       compute_boundedObjectTaylorSqrtDecimalTheory.bounded_object_fs_taylor64_sqrt_decimal_exact
  >> imp_res_tac
       compute_boundedObjectTaylorStateDecimalTheory.bounded_object_case10173_deferred_scale_decimal_exact
  >> imp_res_tac
       compute_boundedObjectTaylorStateDecimalTheory.bounded_object_case10173_deferred_add_exact
  >> res_tac
  >> gvs []
QED

val _ = export_theory ();
