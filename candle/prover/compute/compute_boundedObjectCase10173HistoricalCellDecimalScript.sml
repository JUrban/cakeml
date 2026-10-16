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

Theorem bounded_object_case10173_complete_deferred_decimal_exists:
  bounded_case10173_complete_deferred_decimal radii
      (BoundedTaylor64 result_domain center_value center_gradient
        value_bound gradient_bounds hessian) = SOME result ==>
  ?hessian_rows.
    bounded_hessian64_rows hessian = SOME hessian_rows /\
    bounded_object_fs_taylor_complete radii result_domain center_value
      center_gradient hessian hessian_rows =
        SOME (bounded_taylor64_rows_object_cv result hessian_rows)
Proof
  rw
    [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_complete_deferred_decimal_def]
  >> imp_res_tac
       compute_boundedObjectTaylorUnaryDecimalTheory.bounded_taylor64_complete_decimal_hessian_rows
  >> metis_tac
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_taylor_complete_exact]
QED

Theorem bounded_case10173_checked_cell64_decimal_source_trace:
  bounded_case10173_checked_cell64_decimal radii center_environment
      box_environment coordinate_sqrt_certificates
      center_root_delta center_root_four_x0 center_reciprocals
      box_root_delta box_root_four_x0 box_reciprocals = SOME result ==>
  ?source_constant initial roots_and_constant center_result box_result angle
   deferred_angle scaled_angle complete_source.
    bounded_case10173_geometry_ok
      box_environment center_environment radii 0 /\
    bounded_case10173_positive_environment center_environment /\
    bounded_case10173_positive_environment box_environment /\
    bounded_case10173_u_guards_decimal center_environment /\
    bounded_case10173_u_guards_decimal box_environment /\
    bounded_taylor64_constant bounded_case10173_source_constant_decimal =
      SOME source_constant /\
    bounded_case10173_defer source_constant = SOME initial /\
    bounded_case10173_add_coordinate_sqrts_decimal radii
      center_environment box_environment coordinate_sqrt_certificates
      bounded_case10173_root_coefficients_decimal 0 initial =
        SOME roots_and_constant /\
    bounded_historical_dihedral_first64_decimal center_environment
      center_root_delta center_root_four_x0 center_reciprocals =
        SOME center_result /\
    bounded_historical_dihedral_second64_decimal box_environment
      box_root_delta box_root_four_x0 box_reciprocals =
        SOME box_result /\
    bounded_case10173_angle_state center_result box_result = SOME angle /\
    bounded_case10173_defer angle = SOME deferred_angle /\
    bounded_case10173_deferred_scale_decimal
      bounded_case10173_angle_coefficient_decimal deferred_angle =
        SOME scaled_angle /\
    bounded_case10173_deferred_add roots_and_constant scaled_angle =
      SOME complete_source /\
    bounded_case10173_complete_deferred_decimal radii complete_source =
      SOME result
Proof
  simp
    [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell64_decimal_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> gvs []
  >> metis_tac []
QED

Definition bounded_object_case10173_checked_cell64_decimal_def:
  bounded_object_case10173_checked_cell64_decimal radii center_environment
      box_environment coordinate_sqrt_certificates
      center_root_delta center_root_four_x0 center_reciprocals
      box_root_delta box_root_four_x0 box_reciprocals =
    if ~bounded_case10173_geometry_ok
         box_environment center_environment radii 0 \/
       ~bounded_case10173_positive_environment center_environment \/
       ~bounded_case10173_positive_environment box_environment \/
       ~bounded_case10173_u_guards_decimal center_environment \/
       ~bounded_case10173_u_guards_decimal box_environment
    then NONE
    else
      case bounded_taylor64_constant
        bounded_case10173_source_constant_decimal of
      | NONE => NONE
      | SOME source_constant =>
        case bounded_object_fs_taylor64_constant
          bounded_case10173_source_constant_decimal of
        | NONE => NONE
        | SOME object_source_constant =>
          case bounded_case10173_defer source_constant of
          | NONE => NONE
          | SOME initial =>
            if bounded_object_case10173_defer source_constant <>
                 bounded_taylor64_flat_object_cv initial
            then NONE
            else
              case bounded_case10173_add_coordinate_sqrts_decimal radii
                center_environment box_environment
                coordinate_sqrt_certificates
                bounded_case10173_root_coefficients_decimal 0 initial of
              | NONE => NONE
              | SOME roots_and_constant =>
                case bounded_object_case10173_add_coordinate_sqrts_decimal
                  radii center_environment box_environment
                  coordinate_sqrt_certificates
                  bounded_case10173_root_coefficients_decimal 0 initial of
                | NONE => NONE
                | SOME object_roots_and_constant =>
                  case bounded_historical_dihedral_first64_decimal
                    center_environment center_root_delta center_root_four_x0
                    center_reciprocals of
                  | NONE => NONE
                  | SOME center_result =>
                    case bounded_object_fs_historical_dihedral_first64_decimal
                      center_environment center_root_delta center_root_four_x0
                      center_reciprocals of
                    | NONE => NONE
                    | SOME object_center_result =>
                      case bounded_historical_dihedral_second64_decimal
                        box_environment box_root_delta box_root_four_x0
                        box_reciprocals of
                      | NONE => NONE
                      | SOME box_result =>
                        case
                          bounded_object_fs_historical_dihedral_second64_decimal
                            box_environment box_root_delta box_root_four_x0
                            box_reciprocals of
                        | NONE => NONE
                        | SOME object_box_result =>
                          case bounded_case10173_angle_state
                            center_result box_result of
                          | NONE => NONE
                          | SOME angle =>
                            case bounded_object_case10173_angle_state
                              object_center_result object_box_result of
                            | NONE => NONE
                            | SOME object_angle =>
                              case bounded_case10173_defer angle of
                              | NONE => NONE
                              | SOME deferred_angle =>
                                if bounded_object_case10173_defer angle <>
                                     bounded_taylor64_flat_object_cv
                                       deferred_angle
                                then NONE
                                else
                                  case
                                    bounded_case10173_deferred_scale_decimal
                                      bounded_case10173_angle_coefficient_decimal
                                      deferred_angle of
                                  | NONE => NONE
                                  | SOME scaled_angle =>
                                    case
                                      bounded_object_case10173_deferred_scale_decimal
                                        bounded_case10173_angle_coefficient_decimal
                                        deferred_angle of
                                    | NONE => NONE
                                    | SOME object_scaled_angle =>
                                      case bounded_case10173_deferred_add
                                        roots_and_constant scaled_angle of
                                      | NONE => NONE
                                      | SOME complete_source =>
                                        case bounded_object_case10173_deferred_add
                                          roots_and_constant scaled_angle of
                                        | NONE => NONE
                                        | SOME object_complete_source =>
                                          case
                                            bounded_case10173_complete_deferred_decimal
                                              radii complete_source of
                                          | NONE => NONE
                                          | SOME source_result =>
                                            case complete_source of
                                            | BoundedTaylor64 result_domain
                                                center_value center_gradient
                                                value_bound gradient_bounds
                                                hessian =>
                                              case bounded_hessian64_rows
                                                hessian of
                                              | NONE => NONE
                                              | SOME hessian_rows =>
                                                  bounded_object_fs_taylor_complete
                                                    radii result_domain
                                                    center_value
                                                    center_gradient hessian
                                                    hessian_rows
End

Theorem bounded_object_case10173_checked_cell64_decimal_exact:
  bounded_case10173_checked_cell64_decimal radii center_environment
      box_environment coordinate_sqrt_certificates
      center_root_delta center_root_four_x0
      [center_root_derivative;center_root_four_reciprocal;
       center_u_reciprocal;center_special_root_reciprocal;
       center_b_reciprocal]
      box_root_delta box_root_four_x0
      [box_root_derivative;box_root_logarithmic;
       box_root_four_reciprocal;box_diagonal_reciprocal;
       box_u_reciprocal;box_special_root_reciprocal;
       box_b_reciprocal;box_u126_reciprocal;box_u135_reciprocal] =
        SOME result ==>
  ?hessian_rows.
    bounded_object_case10173_checked_cell64_decimal radii
      center_environment box_environment coordinate_sqrt_certificates
      center_root_delta center_root_four_x0
      [center_root_derivative;center_root_four_reciprocal;
       center_u_reciprocal;center_special_root_reciprocal;
       center_b_reciprocal]
      box_root_delta box_root_four_x0
      [box_root_derivative;box_root_logarithmic;
       box_root_four_reciprocal;box_diagonal_reciprocal;
       box_u_reciprocal;box_special_root_reciprocal;
       box_b_reciprocal;box_u126_reciprocal;box_u135_reciprocal] =
        SOME (bounded_taylor64_rows_object_cv result hessian_rows)
Proof
  strip_tac
  >> drule bounded_case10173_checked_cell64_decimal_source_trace
  >> strip_tac
  >> PairCases_on `center_result`
  >> PairCases_on `box_result`
  >> Cases_on `complete_source`
  >> imp_res_tac bounded_object_fs_taylor64_constant_exact
  >> imp_res_tac
       compute_boundedObjectTaylorStateDecimalTheory.bounded_object_case10173_defer_exact
  >> imp_res_tac bounded_object_case10173_add_coordinate_sqrts_decimal_exact
  >> imp_res_tac
       compute_boundedObjectHistoricalFirstDecimalTheory.bounded_object_fs_historical_dihedral_first64_decimal_exact
  >> imp_res_tac
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_object_fs_historical_dihedral_second64_decimal_exact
  >> imp_res_tac bounded_object_case10173_angle_state_exact
  >> imp_res_tac
       compute_boundedObjectTaylorStateDecimalTheory.bounded_object_case10173_deferred_scale_decimal_exact
  >> imp_res_tac
       compute_boundedObjectTaylorStateDecimalTheory.bounded_object_case10173_deferred_add_exact
  >> imp_res_tac
       bounded_object_case10173_complete_deferred_decimal_exists
  >> simp
       [bounded_object_case10173_checked_cell64_decimal_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

val _ = export_theory ();
