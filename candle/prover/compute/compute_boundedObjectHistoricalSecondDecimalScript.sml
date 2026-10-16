(*****************************************************************************
 * Exact object traces for the historical decimal box calculation.
 *
 * The source trace is intentionally extracted before the object refinements:
 * it lets each second-order component consume one authenticated successful
 * path without repeatedly unfolding the deeply nested top-level checker.
 *****************************************************************************)
Theory compute_boundedObjectHistoricalSecondDecimal
Ancestors
  compute_boundedObjectHistoricalFirstDecimal
  compute_boundedHistoricalDihedralSecondDecimal
Libs
  bossLib preamble

Theorem bounded_historical_dihedral_second64_decimal_source_trace:
  bounded_historical_dihedral_second64_decimal environment root_delta
      root_four_x0
      [root_derivative;root_logarithmic;root_four_reciprocal;
       diagonal_reciprocal;u_reciprocal;special_root_reciprocal;
       b_reciprocal;u126_reciprocal;u135_reciprocal] =
    SOME (value,gradient,hessian) ==>
  ?delta_interval delta_gradient delta_hessian root_value root_gradient
   root_hessian delta_x4 delta_x4_gradient delta_x4_hessian
   u126 u126_gradient u135 u135_gradient x0 four_x0 twice_x0 b
   two two_over_root_four b_gradient_base b_correction b_gradient
   b_hessian_base b_hessian c u_product gradient_base twice_root_delta
   special_gradient logarithmic_126 logarithmic_135
   logarithmic_u_gradient quotient angle.
    bounded_historical_delta_second_decimal environment =
      SOME (delta_interval,delta_gradient,delta_hessian) /\
    bounded_historical_sqrt_second_decimal
      delta_interval delta_gradient delta_hessian root_delta
      root_derivative root_logarithmic =
      SOME (root_value,root_gradient,root_hessian) /\
    bounded_historical_delta_x4_second_decimal environment =
      SOME (delta_x4,delta_x4_gradient,delta_x4_hessian) /\
    bounded_historical_u126_decimal environment =
      SOME (u126,u126_gradient) /\
    bounded_historical_u135_decimal environment =
      SOME (u135,u135_gradient) /\
    bounded_interval64_nth environment 0 = SOME x0 /\
    bounded_interval64_scale4 x0 = SOME four_x0 /\
    bounded_interval64_positive_sqrt_certificate_decimal
      four_x0 root_four_x0 /\
    bounded_interval64_positive_inv_certificate_decimal
      root_four_x0 root_four_reciprocal /\
    bounded_historical_scale2 x0 = SOME twice_x0 /\
    bounded_interval64_positive_inv_certificate_decimal
      twice_x0 diagonal_reciprocal /\
    bounded_interval64_mul_decimal root_delta root_four_x0 = SOME b /\
    bounded_interval64_positive_inv_certificate_decimal b b_reciprocal /\
    bounded_historical_scale2 bounded_atan_one_decimal = SOME two /\
    bounded_interval64_mul_decimal two root_four_reciprocal =
      SOME two_over_root_four /\
    bounded_interval64_list_scale_decimal root_four_x0 root_gradient =
      SOME b_gradient_base /\
    bounded_interval64_mul_decimal root_delta two_over_root_four =
      SOME b_correction /\
    bounded_interval64_list_add_at b_correction 0 b_gradient_base =
      SOME b_gradient /\
    bounded_interval64_list_scale_decimal root_four_x0 root_hessian =
      SOME b_hessian_base /\
    bounded_historical_b_hessian_decimal root_delta two_over_root_four
      diagonal_reciprocal root_gradient b_hessian_base = SOME b_hessian /\
    bounded_historical_c_vector_decimal delta_x4 b delta_x4_gradient
      b_gradient = SOME c /\
    bounded_interval64_mul_decimal u126 u135 = SOME u_product /\
    bounded_interval64_positive_inv_certificate_decimal
      u_product u_reciprocal /\
    bounded_interval64_positive_inv_certificate_decimal
      u126 u126_reciprocal /\
    bounded_interval64_positive_inv_certificate_decimal
      u135 u135_reciprocal /\
    bounded_interval64_list_scale_decimal u_reciprocal c =
      SOME gradient_base /\
    bounded_historical_scale2 root_delta = SOME twice_root_delta /\
    bounded_interval64_positive_inv_certificate_decimal
      twice_root_delta special_root_reciprocal /\
    bounded_interval64_mul_decimal root_four_x0 special_root_reciprocal =
      SOME special_gradient /\
    bounded_historical_replace_three gradient_base special_gradient =
      SOME gradient /\
    bounded_interval64_list_scale_decimal u126_reciprocal u126_gradient =
      SOME logarithmic_126 /\
    bounded_interval64_list_scale_decimal u135_reciprocal u135_gradient =
      SOME logarithmic_135 /\
    bounded_interval64_list_add logarithmic_126 logarithmic_135 =
      SOME logarithmic_u_gradient /\
    bounded_historical_second_hessian_decimal delta_x4 b u_reciprocal
      delta_x4_gradient b_gradient gradient logarithmic_u_gradient
      bounded_delta64_hessian_indices delta_x4_hessian b_hessian =
      SOME hessian /\
    bounded_interval64_mul_decimal
      (bounded_interval64_neg delta_x4) b_reciprocal = SOME quotient /\
    bounded_interval64_atan_range_decimal quotient NONE NONE = SOME angle /\
    bounded_interval64_add bounded_atan_pi_half_decimal angle = SOME value
Proof
  simp
    [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_dihedral_second64_decimal_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> strip_tac
  >> gvs []
QED

Theorem bounded_historical_dihedral_second64_decimal_x0_object_trace:
  bounded_historical_dihedral_second64_decimal environment root_delta
      root_four_x0
      [root_derivative;root_logarithmic;root_four_reciprocal;
       diagonal_reciprocal;u_reciprocal;special_root_reciprocal;
       b_reciprocal;u126_reciprocal;u135_reciprocal] =
    SOME (value,gradient,hessian) ==>
  ?x0 four_x0 twice_x0.
    bounded_object_fs_interval_scale4
      (bounded_interval64_object_cv x0) =
      SOME (bounded_interval64_object_cv four_x0) /\
    bounded_object_fs_hist_positive_root_certificate
      (bounded_interval64_object_cv four_x0)
      (bounded_interval64_object_cv root_four_x0) = Num 1 /\
    bounded_object_fs_hist_positive_inv
      (bounded_interval64_object_cv root_four_x0) =
      SOME (bounded_interval64_object_cv root_four_reciprocal) /\
    bounded_object_fs_interval_scale2
      (bounded_interval64_object_cv x0) =
      SOME (bounded_interval64_object_cv twice_x0) /\
    bounded_object_fs_hist_positive_inv
      (bounded_interval64_object_cv twice_x0) =
      SOME (bounded_interval64_object_cv diagonal_reciprocal)
Proof
  strip_tac
  >> drule bounded_historical_dihedral_second64_decimal_source_trace
  >> strip_tac
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_scale4_exact
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_scale2_exact
  >> imp_res_tac
       compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_sqrt_certificate_decimal_object_exact
  >> imp_res_tac
       compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_inv_certificate_decimal_object_exact
  >> qexists_tac `x0`
  >> qexists_tac `four_x0`
  >> qexists_tac `twice_x0`
  >> simp []
QED

Theorem bounded_historical_dihedral_second64_decimal_product_object_trace:
  bounded_historical_dihedral_second64_decimal environment root_delta
      root_four_x0
      [root_derivative;root_logarithmic;root_four_reciprocal;
       diagonal_reciprocal;u_reciprocal;special_root_reciprocal;
       b_reciprocal;u126_reciprocal;u135_reciprocal] =
    SOME (value,gradient,hessian) ==>
  ?u126 u135 b u_product two two_over_root_four twice_root_delta.
    bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv root_delta)
      (bounded_interval64_object_cv root_four_x0) =
      SOME (bounded_interval64_object_cv b) /\
    bounded_object_fs_hist_positive_inv
      (bounded_interval64_object_cv b) =
      SOME (bounded_interval64_object_cv b_reciprocal) /\
    bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv u126)
      (bounded_interval64_object_cv u135) =
      SOME (bounded_interval64_object_cv u_product) /\
    bounded_object_fs_hist_positive_inv
      (bounded_interval64_object_cv u_product) =
      SOME (bounded_interval64_object_cv u_reciprocal) /\
    bounded_object_fs_hist_positive_inv
      (bounded_interval64_object_cv u126) =
      SOME (bounded_interval64_object_cv u126_reciprocal) /\
    bounded_object_fs_hist_positive_inv
      (bounded_interval64_object_cv u135) =
      SOME (bounded_interval64_object_cv u135_reciprocal) /\
    bounded_object_fs_interval_scale2
      (bounded_interval64_object_cv bounded_atan_one_decimal) =
      SOME (bounded_interval64_object_cv two) /\
    bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv two)
      (bounded_interval64_object_cv root_four_reciprocal) =
      SOME (bounded_interval64_object_cv two_over_root_four) /\
    bounded_object_fs_interval_scale2
      (bounded_interval64_object_cv root_delta) =
      SOME (bounded_interval64_object_cv twice_root_delta) /\
    bounded_object_fs_hist_positive_inv
      (bounded_interval64_object_cv twice_root_delta) =
      SOME (bounded_interval64_object_cv special_root_reciprocal)
Proof
  strip_tac
  >> drule bounded_historical_dihedral_second64_decimal_source_trace
  >> strip_tac
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_scale2_exact
  >> imp_res_tac
       compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_inv_certificate_decimal_object_exact
  >> qexists_tac `u126`
  >> qexists_tac `u135`
  >> qexists_tac `b`
  >> qexists_tac `u_product`
  >> qexists_tac `two`
  >> qexists_tac `two_over_root_four`
  >> qexists_tac `twice_root_delta`
  >> simp []
QED

Theorem bounded_historical_dihedral_second64_decimal_gradient_object_trace:
  bounded_historical_dihedral_second64_decimal environment root_delta
      root_four_x0
      [root_derivative;root_logarithmic;root_four_reciprocal;
       diagonal_reciprocal;u_reciprocal;special_root_reciprocal;
       b_reciprocal;u126_reciprocal;u135_reciprocal] =
    SOME (value,gradient,hessian) ==>
  ?root_gradient root_hessian delta_x4 delta_x4_gradient b
   two_over_root_four b_gradient_base b_correction b_gradient
   b_hessian_base c gradient_base special_gradient.
    bounded_object_fs_interval_list_scale_decimal
      root_four_x0 root_gradient =
      SOME (bounded_interval64_object_cv_list b_gradient_base) /\
    bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv root_delta)
      (bounded_interval64_object_cv two_over_root_four) =
      SOME (bounded_interval64_object_cv b_correction) /\
    bounded_object_fs_interval_list_add_at
      (bounded_interval64_object_cv b_correction) 0
      (bounded_interval64_object_cv_list b_gradient_base) =
      SOME (bounded_interval64_object_cv_list b_gradient) /\
    bounded_object_fs_interval_list_scale_decimal
      root_four_x0 root_hessian =
      SOME (bounded_interval64_object_cv_list b_hessian_base) /\
    bounded_object_fs_historical_c_vector_decimal
      (bounded_interval64_object_cv delta_x4)
      (bounded_interval64_object_cv b)
      (bounded_interval64_object_cv_list delta_x4_gradient)
      (bounded_interval64_object_cv_list b_gradient) =
      SOME (bounded_interval64_object_cv_list c) /\
    bounded_object_fs_interval_list_scale_decimal u_reciprocal c =
      SOME (bounded_interval64_object_cv_list gradient_base) /\
    bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv root_four_x0)
      (bounded_interval64_object_cv special_root_reciprocal) =
      SOME (bounded_interval64_object_cv special_gradient) /\
    bounded_object_fs_historical_replace_three
      (bounded_interval64_object_cv_list gradient_base)
      (bounded_interval64_object_cv special_gradient) =
      SOME (bounded_interval64_object_cv_list gradient)
Proof
  strip_tac
  >> drule bounded_historical_dihedral_second64_decimal_source_trace
  >> strip_tac
  >> imp_res_tac
       compute_boundedObjectTaylorProductDecimalTheory.bounded_object_fs_interval_list_scale_decimal_exact
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_list_add_at_exact
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_historical_c_vector_decimal_exact
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_historical_replace_three_exact
  >> qexists_tac `root_gradient`
  >> qexists_tac `root_hessian`
  >> qexists_tac `delta_x4`
  >> qexists_tac `delta_x4_gradient`
  >> qexists_tac `b`
  >> qexists_tac `two_over_root_four`
  >> qexists_tac `b_gradient_base`
  >> qexists_tac `b_correction`
  >> qexists_tac `b_gradient`
  >> qexists_tac `b_hessian_base`
  >> qexists_tac `c`
  >> qexists_tac `gradient_base`
  >> qexists_tac `special_gradient`
  >> simp []
QED

Theorem bounded_historical_dihedral_second64_decimal_logarithmic_object_trace:
  bounded_historical_dihedral_second64_decimal environment root_delta
      root_four_x0
      [root_derivative;root_logarithmic;root_four_reciprocal;
       diagonal_reciprocal;u_reciprocal;special_root_reciprocal;
       b_reciprocal;u126_reciprocal;u135_reciprocal] =
    SOME (value,gradient,hessian) ==>
  ?u126_gradient u135_gradient logarithmic_126 logarithmic_135
   logarithmic_u_gradient.
    bounded_object_fs_interval_list_scale_decimal
      u126_reciprocal u126_gradient =
      SOME (bounded_interval64_object_cv_list logarithmic_126) /\
    bounded_object_fs_interval_list_scale_decimal
      u135_reciprocal u135_gradient =
      SOME (bounded_interval64_object_cv_list logarithmic_135) /\
    bounded_object_fs_interval_list_add logarithmic_126 logarithmic_135 =
      SOME (bounded_interval64_object_cv_list logarithmic_u_gradient)
Proof
  strip_tac
  >> drule bounded_historical_dihedral_second64_decimal_source_trace
  >> strip_tac
  >> imp_res_tac
       compute_boundedObjectTaylorProductDecimalTheory.bounded_object_fs_interval_list_scale_decimal_exact
  >> imp_res_tac
       compute_boundedObjectTaylorStateDecimalTheory.bounded_object_fs_interval_list_add_exact
  >> qexists_tac `u126_gradient`
  >> qexists_tac `u135_gradient`
  >> qexists_tac `logarithmic_126`
  >> qexists_tac `logarithmic_135`
  >> qexists_tac `logarithmic_u_gradient`
  >> simp []
QED

Theorem bounded_historical_dihedral_second64_decimal_final_object_trace:
  bounded_historical_dihedral_second64_decimal environment root_delta
      root_four_x0
      [root_derivative;root_logarithmic;root_four_reciprocal;
       diagonal_reciprocal;u_reciprocal;special_root_reciprocal;
       b_reciprocal;u126_reciprocal;u135_reciprocal] =
    SOME (value,gradient,hessian) ==>
  ?delta_x4 quotient angle.
    bounded_object_fs_interval_neg
      (bounded_interval64_object_cv delta_x4) =
      SOME
        (bounded_interval64_object_cv
          (bounded_interval64_neg delta_x4)) /\
    bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv (bounded_interval64_neg delta_x4))
      (bounded_interval64_object_cv b_reciprocal) =
      SOME (bounded_interval64_object_cv quotient) /\
    bounded_object_fs_interval64_atan_range_none_decimal quotient =
      SOME (bounded_interval64_object_cv angle) /\
    bounded_object_fs_interval_add
      (bounded_interval64_object_cv bounded_atan_pi_half_decimal)
      (bounded_interval64_object_cv angle) =
      SOME (bounded_interval64_object_cv value)
Proof
  strip_tac
  >> drule bounded_historical_dihedral_second64_decimal_source_trace
  >> strip_tac
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> imp_res_tac bounded_object_fs_interval64_atan_range_none_decimal_exact
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
  >> qexists_tac `delta_x4`
  >> qexists_tac `quotient`
  >> qexists_tac `angle`
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
QED

Definition bounded_object_cv_list_nth_def:
  bounded_object_cv_list_nth 0 (Pair entry rest) = SOME entry /\
  bounded_object_cv_list_nth (SUC index) (Pair entry rest) =
    bounded_object_cv_list_nth index rest /\
  bounded_object_cv_list_nth index (Num malformed) = NONE
End

Theorem bounded_object_cv_list_nth_exact:
  !index result.
    bounded_interval64_nth values index = SOME result ==>
    bounded_object_cv_list_nth index
      (bounded_interval64_object_cv_list values) =
    SOME (bounded_interval64_object_cv result)
Proof
  Induct_on `values`
  >> Cases_on `index`
  >> simp
       [compute_boundedTaylorBaseTheory.bounded_interval64_nth_def,
        bounded_object_cv_list_nth_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_historical_sqrt_hessian_decimal_def:
  bounded_object_fs_historical_sqrt_hessian_decimal derivative
      logarithmic_derivative gradient [] (Num 0) = SOME (Num 0 : cv) /\
  bounded_object_fs_historical_sqrt_hessian_decimal derivative
      logarithmic_derivative gradient [] (Num (SUC malformed)) = NONE /\
  bounded_object_fs_historical_sqrt_hessian_decimal derivative
      logarithmic_derivative gradient [] (Pair entry rest) = NONE /\
  bounded_object_fs_historical_sqrt_hessian_decimal derivative
      logarithmic_derivative gradient (_::_) (Num malformed) = NONE /\
  bounded_object_fs_historical_sqrt_hessian_decimal derivative
      logarithmic_derivative gradient ((row,column)::indices)
      (Pair hessian_entry hessian_entries) =
    case bounded_object_cv_list_nth row gradient of
    | NONE => NONE
    | SOME row_gradient =>
      case bounded_object_cv_list_nth column gradient of
      | NONE => NONE
      | SOME column_gradient =>
        case bounded_object_fs_interval_mul_decimal
          logarithmic_derivative row_gradient of
        | NONE => NONE
        | SOME scaled_row =>
          case bounded_object_fs_interval_mul_decimal
            column_gradient scaled_row of
          | NONE => NONE
          | SOME outer =>
            case bounded_object_fs_interval_add outer hessian_entry of
            | NONE => NONE
            | SOME inside =>
              case bounded_object_fs_interval_mul_decimal derivative inside of
              | NONE => NONE
              | SOME value =>
                case bounded_object_fs_historical_sqrt_hessian_decimal
                  derivative logarithmic_derivative gradient indices
                  hessian_entries of
                | NONE => NONE
                | SOME rest => SOME (Pair value rest)
End

Theorem bounded_object_fs_historical_sqrt_hessian_decimal_exact:
  !hessian result.
    bounded_historical_sqrt_hessian_decimal derivative
      logarithmic_derivative gradient indices hessian = SOME result ==>
    bounded_object_fs_historical_sqrt_hessian_decimal
      (bounded_interval64_object_cv derivative)
      (bounded_interval64_object_cv logarithmic_derivative)
      (bounded_interval64_object_cv_list gradient) indices
      (bounded_interval64_object_cv_list hessian) =
    SOME (bounded_interval64_object_cv_list result)
Proof
  Induct_on `indices`
  >- (Cases_on `hessian`
      >> simp
           [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_sqrt_hessian_decimal_def,
            bounded_object_fs_historical_sqrt_hessian_decimal_def,
            compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def])
  >> Cases_on `h`
  >> Cases_on `hessian`
  >> rw
       [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_sqrt_hessian_decimal_def,
        bounded_object_fs_historical_sqrt_hessian_decimal_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_cv_list_nth_exact
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
  >> res_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Theorem bounded_historical_sqrt_second_decimal_source_trace:
  bounded_historical_sqrt_second_decimal value gradient hessian root
      derivative_reciprocal logarithmic_reciprocal =
    SOME (result_root,result_gradient,result_hessian) ==>
  ?twice_root twice_value.
    result_root = root /\
    bounded_interval64_positive_sqrt_certificate_decimal value root /\
    bounded_historical_scale2 root = SOME twice_root /\
    bounded_interval64_positive_inv_certificate_decimal
      twice_root derivative_reciprocal /\
    bounded_historical_scale2 value = SOME twice_value /\
    bounded_interval64_positive_inv_certificate_decimal
      twice_value logarithmic_reciprocal /\
    bounded_interval64_list_scale_decimal derivative_reciprocal gradient =
      SOME result_gradient /\
    bounded_historical_sqrt_hessian_decimal derivative_reciprocal
      (bounded_interval64_neg logarithmic_reciprocal) gradient
      bounded_delta64_hessian_indices hessian = SOME result_hessian
Proof
  simp
    [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_sqrt_second_decimal_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> strip_tac
  >> gvs []
QED

Theorem bounded_historical_sqrt_second_decimal_object_trace:
  bounded_historical_sqrt_second_decimal value gradient hessian root
      derivative_reciprocal logarithmic_reciprocal =
    SOME (result_root,result_gradient,result_hessian) ==>
  ?twice_root twice_value.
    result_root = root /\
    bounded_object_fs_hist_positive_root_certificate
      (bounded_interval64_object_cv value)
      (bounded_interval64_object_cv root) = Num 1 /\
    bounded_object_fs_interval_scale2
      (bounded_interval64_object_cv root) =
      SOME (bounded_interval64_object_cv twice_root) /\
    bounded_object_fs_hist_positive_inv
      (bounded_interval64_object_cv twice_root) =
      SOME (bounded_interval64_object_cv derivative_reciprocal) /\
    bounded_object_fs_interval_scale2
      (bounded_interval64_object_cv value) =
      SOME (bounded_interval64_object_cv twice_value) /\
    bounded_object_fs_hist_positive_inv
      (bounded_interval64_object_cv twice_value) =
      SOME (bounded_interval64_object_cv logarithmic_reciprocal) /\
    bounded_object_fs_interval_list_scale_decimal
      derivative_reciprocal gradient =
      SOME (bounded_interval64_object_cv_list result_gradient) /\
    bounded_object_fs_interval_neg
      (bounded_interval64_object_cv logarithmic_reciprocal) =
      SOME
        (bounded_interval64_object_cv
          (bounded_interval64_neg logarithmic_reciprocal)) /\
    bounded_object_fs_historical_sqrt_hessian_decimal
      (bounded_interval64_object_cv derivative_reciprocal)
      (bounded_interval64_object_cv
        (bounded_interval64_neg logarithmic_reciprocal))
      (bounded_interval64_object_cv_list gradient)
      bounded_delta64_hessian_indices
      (bounded_interval64_object_cv_list hessian) =
      SOME (bounded_interval64_object_cv_list result_hessian)
Proof
  strip_tac
  >> drule bounded_historical_sqrt_second_decimal_source_trace
  >> strip_tac
  >> imp_res_tac
       compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_sqrt_certificate_decimal_object_exact
  >> imp_res_tac
       compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_inv_certificate_decimal_object_exact
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_scale2_exact
  >> imp_res_tac
       compute_boundedObjectTaylorProductDecimalTheory.bounded_object_fs_interval_list_scale_decimal_exact
  >> imp_res_tac bounded_object_fs_historical_sqrt_hessian_decimal_exact
  >> qexists_tac `twice_root`
  >> qexists_tac `twice_value`
  >> gvs
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
QED

val _ = export_theory ();
