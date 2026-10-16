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

Definition bounded_object_fs_historical_second_hessian_entry_decimal_def:
  bounded_object_fs_historical_second_hessian_entry_decimal delta_x4 b
      reciprocal_u delta_x4_gradient b_gradient result_gradient
      logarithmic_u_gradient (row:num) (column:num) delta_x4_hessian
      b_hessian =
    case bounded_object_cv_list_nth row delta_x4_gradient of
    | NONE => NONE
    | SOME delta_x4_row =>
      case bounded_object_cv_list_nth column delta_x4_gradient of
      | NONE => NONE
      | SOME delta_x4_column =>
        case bounded_object_cv_list_nth row b_gradient of
        | NONE => NONE
        | SOME b_row =>
          case bounded_object_cv_list_nth column b_gradient of
          | NONE => NONE
          | SOME b_column =>
            case bounded_object_cv_list_nth row result_gradient of
            | NONE => NONE
            | SOME result_row =>
              case bounded_object_cv_list_nth column logarithmic_u_gradient of
              | NONE => NONE
              | SOME logarithmic_column =>
                case bounded_object_fs_interval_mul_decimal
                  b delta_x4_hessian of
                | NONE => NONE
                | SOME first_term =>
                  case bounded_object_fs_interval_mul_decimal
                    delta_x4 b_hessian of
                  | NONE => NONE
                  | SOME final_term =>
                    case
                      (if row = column then
                         case bounded_object_fs_interval_neg first_term of
                         | NONE => NONE
                         | SOME negative_first =>
                             bounded_object_fs_interval_add
                               negative_first final_term
                       else
                         case bounded_object_fs_interval_mul_decimal
                           delta_x4_row b_column of
                         | NONE => NONE
                         | SOME second_term =>
                           case bounded_object_fs_interval_mul_decimal
                             delta_x4_column b_row of
                           | NONE => NONE
                           | SOME third_term =>
                             case bounded_object_fs_interval_neg first_term of
                             | NONE => NONE
                             | SOME negative_first =>
                               case bounded_object_fs_interval_neg second_term of
                               | NONE => NONE
                               | SOME negative_second =>
                                   bounded_object_fs_interval_sum
                                     (Pair negative_first
                                       (Pair negative_second
                                         (Pair third_term
                                           (Pair final_term (Num 0)))))) of
                    | NONE => NONE
                    | SOME identity =>
                      case bounded_object_fs_interval_mul_decimal
                        reciprocal_u identity of
                      | NONE => NONE
                      | SOME scaled_identity =>
                        case bounded_object_fs_interval_mul_decimal
                          result_row logarithmic_column of
                        | NONE => NONE
                        | SOME logarithmic_term =>
                          case bounded_object_fs_interval_neg logarithmic_term of
                          | NONE => NONE
                          | SOME negative_logarithmic =>
                              bounded_object_fs_interval_add scaled_identity
                                negative_logarithmic
End

Theorem bounded_object_fs_historical_second_hessian_entry_decimal_exact:
  bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      row column delta_x4_hessian b_hessian = SOME result ==>
  bounded_object_fs_historical_second_hessian_entry_decimal
      (bounded_interval64_object_cv delta_x4)
      (bounded_interval64_object_cv b)
      (bounded_interval64_object_cv reciprocal_u)
      (bounded_interval64_object_cv_list delta_x4_gradient)
      (bounded_interval64_object_cv_list b_gradient)
      (bounded_interval64_object_cv_list result_gradient)
      (bounded_interval64_object_cv_list logarithmic_u_gradient)
      row column
      (bounded_interval64_object_cv delta_x4_hessian)
      (bounded_interval64_object_cv b_hessian) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_second_hessian_entry_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_cv_list_nth_exact
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_sum_exact
  >> gvs
       [bounded_object_fs_historical_second_hessian_entry_decimal_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_historical_second_hessian_decimal_def:
  bounded_object_fs_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      [] (Num 0) (Num 0) = SOME (Num 0 : cv) /\
  bounded_object_fs_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      [] (Num 0) (Num (SUC malformed)) = NONE /\
  bounded_object_fs_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      [] (Num 0) (Pair entry rest) = NONE /\
  bounded_object_fs_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      [] (Num (SUC malformed)) right = NONE /\
  bounded_object_fs_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      [] (Pair entry rest) right = NONE /\
  bounded_object_fs_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      (_::_) (Num malformed) right = NONE /\
  bounded_object_fs_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      (_::_) left (Num malformed) = NONE /\
  bounded_object_fs_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      ((row,column)::indices) (Pair delta_entry delta_entries)
      (Pair b_entry b_entries) =
    case bounded_object_fs_historical_second_hessian_entry_decimal
      delta_x4 b reciprocal_u delta_x4_gradient b_gradient
      result_gradient logarithmic_u_gradient row column delta_entry b_entry of
    | NONE => NONE
    | SOME value =>
      case bounded_object_fs_historical_second_hessian_decimal
        delta_x4 b reciprocal_u delta_x4_gradient b_gradient
        result_gradient logarithmic_u_gradient indices delta_entries b_entries of
      | NONE => NONE
      | SOME rest => SOME (Pair value rest)
End

Theorem bounded_object_fs_historical_second_hessian_decimal_exact:
  !delta_hessian b_hessian result.
    bounded_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      indices delta_hessian b_hessian = SOME result ==>
    bounded_object_fs_historical_second_hessian_decimal
      (bounded_interval64_object_cv delta_x4)
      (bounded_interval64_object_cv b)
      (bounded_interval64_object_cv reciprocal_u)
      (bounded_interval64_object_cv_list delta_x4_gradient)
      (bounded_interval64_object_cv_list b_gradient)
      (bounded_interval64_object_cv_list result_gradient)
      (bounded_interval64_object_cv_list logarithmic_u_gradient)
      indices (bounded_interval64_object_cv_list delta_hessian)
      (bounded_interval64_object_cv_list b_hessian) =
    SOME (bounded_interval64_object_cv_list result)
Proof
  Induct_on `indices`
  >- (Cases_on `delta_hessian`
      >> Cases_on `b_hessian`
      >> simp
           [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_second_hessian_decimal_def,
            bounded_object_fs_historical_second_hessian_decimal_def,
            compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def])
  >> Cases_on `h`
  >> Cases_on `delta_hessian`
  >> Cases_on `b_hessian`
  >> rw
       [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_second_hessian_decimal_def,
        bounded_object_fs_historical_second_hessian_decimal_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       bounded_object_fs_historical_second_hessian_entry_decimal_exact
  >> res_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_historical_b_hessian_decimal_def:
  bounded_object_fs_historical_b_hessian_decimal root_delta
      two_over_root_four diagonal_reciprocal root_gradient base_hessian =
    case root_gradient of
    | Pair g0 (Pair g1 (Pair g2 (Pair g3 (Pair g4 (Pair g5 (Num 0)))))) =>
      case base_hessian of
      | Pair base00
          (Pair base01
            (Pair base02
              (Pair base03 (Pair base04 (Pair base05 base_tail))))) =>
                case bounded_object_fs_interval_mul_decimal
                  g0 two_over_root_four of
                | NONE => NONE
                | SOME first_correction =>
                  case bounded_object_fs_interval_scale2
                    first_correction of
                  | NONE => NONE
                  | SOME twice_first_correction =>
                    case bounded_object_fs_interval_mul_decimal
                      root_delta two_over_root_four of
                    | NONE => NONE
                    | SOME diagonal_numerator =>
                      case bounded_object_fs_interval_mul_decimal
                        diagonal_numerator diagonal_reciprocal of
                      | NONE => NONE
                      | SOME diagonal_subtraction =>
                        case bounded_object_fs_interval_neg
                          diagonal_subtraction of
                        | NONE => NONE
                        | SOME negative_diagonal_subtraction =>
                          case bounded_object_fs_interval_add
                            twice_first_correction
                            negative_diagonal_subtraction of
                          | NONE => NONE
                          | SOME diagonal_correction =>
                            case bounded_object_fs_interval_add
                              base00 diagonal_correction of
                            | NONE => NONE
                            | SOME r00 =>
                              case bounded_object_fs_interval_mul_decimal
                                g1 two_over_root_four of
                              | NONE => NONE
                              | SOME c01 =>
                                case bounded_object_fs_interval_add base01 c01 of
                                | NONE => NONE
                                | SOME r01 =>
                                  case bounded_object_fs_interval_mul_decimal
                                    g2 two_over_root_four of
                                  | NONE => NONE
                                  | SOME c02 =>
                                    case bounded_object_fs_interval_add base02 c02 of
                                    | NONE => NONE
                                    | SOME r02 =>
                                      case bounded_object_fs_interval_mul_decimal
                                        g3 two_over_root_four of
                                      | NONE => NONE
                                      | SOME c03 =>
                                        case bounded_object_fs_interval_add base03 c03 of
                                        | NONE => NONE
                                        | SOME r03 =>
                                          case bounded_object_fs_interval_mul_decimal
                                            g4 two_over_root_four of
                                          | NONE => NONE
                                          | SOME c04 =>
                                            case bounded_object_fs_interval_add
                                              base04 c04 of
                                            | NONE => NONE
                                            | SOME r04 =>
                                              case bounded_object_fs_interval_mul_decimal
                                                g5 two_over_root_four of
                                              | NONE => NONE
                                              | SOME c05 =>
                                                case bounded_object_fs_interval_add
                                                  base05 c05 of
                                                | NONE => NONE
                                                | SOME r05 =>
                                                    SOME
                                                      (Pair r00
                                                        (Pair r01
                                                          (Pair r02
                                                            (Pair r03
                                                              (Pair r04
                                                                (Pair r05 base_tail))))))
      | _ => NONE
    | _ => NONE
End

Theorem bounded_historical_b_hessian_decimal_source_trace:
  bounded_historical_b_hessian_decimal root_delta two_over_root_four
      diagonal_reciprocal root_gradient base_hessian = SOME result ==>
  ?g0 g1 g2 g3 g4 g5
   h00 h01 h02 h03 h04 h05 h11 h12 h13 h14 h15 h22 h23 h24 h25
   h33 h34 h35 h44 h45 h55 first_correction twice_first_correction
   diagonal_numerator diagonal_subtraction diagonal_correction
   r00 c01 r01 c02 r02 c03 r03 c04 r04 c05 r05.
    root_gradient = [g0;g1;g2;g3;g4;g5] /\
    base_hessian =
      [h00;h01;h02;h03;h04;h05;h11;h12;h13;h14;h15;
       h22;h23;h24;h25;h33;h34;h35;h44;h45;h55] /\
    bounded_interval64_mul_decimal g0 two_over_root_four =
      SOME first_correction /\
    bounded_historical_scale2 first_correction =
      SOME twice_first_correction /\
    bounded_interval64_mul_decimal root_delta two_over_root_four =
      SOME diagonal_numerator /\
    bounded_interval64_mul_decimal diagonal_numerator diagonal_reciprocal =
      SOME diagonal_subtraction /\
    bounded_interval64_add twice_first_correction
      (bounded_interval64_neg diagonal_subtraction) =
      SOME diagonal_correction /\
    bounded_interval64_add h00 diagonal_correction = SOME r00 /\
    bounded_interval64_mul_decimal g1 two_over_root_four = SOME c01 /\
    bounded_interval64_add h01 c01 = SOME r01 /\
    bounded_interval64_mul_decimal g2 two_over_root_four = SOME c02 /\
    bounded_interval64_add h02 c02 = SOME r02 /\
    bounded_interval64_mul_decimal g3 two_over_root_four = SOME c03 /\
    bounded_interval64_add h03 c03 = SOME r03 /\
    bounded_interval64_mul_decimal g4 two_over_root_four = SOME c04 /\
    bounded_interval64_add h04 c04 = SOME r04 /\
    bounded_interval64_mul_decimal g5 two_over_root_four = SOME c05 /\
    bounded_interval64_add h05 c05 = SOME r05 /\
    result =
      [r00;r01;r02;r03;r04;r05;h11;h12;h13;h14;h15;
       h22;h23;h24;h25;h33;h34;h35;h44;h45;h55]
Proof
  simp
    [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_b_hessian_decimal_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> strip_tac
  >> gvs []
QED

Theorem bounded_object_fs_historical_b_hessian_decimal_exact:
  bounded_historical_b_hessian_decimal root_delta two_over_root_four
      diagonal_reciprocal root_gradient base_hessian = SOME result ==>
  bounded_object_fs_historical_b_hessian_decimal
      (bounded_interval64_object_cv root_delta)
      (bounded_interval64_object_cv two_over_root_four)
      (bounded_interval64_object_cv diagonal_reciprocal)
      (bounded_interval64_object_cv_list root_gradient)
      (bounded_interval64_object_cv_list base_hessian) =
    SOME (bounded_interval64_object_cv_list result)
Proof
  strip_tac
  >> drule bounded_historical_b_hessian_decimal_source_trace
  >> strip_tac
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_scale2_exact
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
  >> gvs
       [bounded_object_fs_historical_b_hessian_decimal_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Theorem bounded_historical_dihedral_second64_decimal_b_hessian_object_trace:
  bounded_historical_dihedral_second64_decimal environment root_delta
      root_four_x0
      [root_derivative;root_logarithmic;root_four_reciprocal;
       diagonal_reciprocal;u_reciprocal;special_root_reciprocal;
       b_reciprocal;u126_reciprocal;u135_reciprocal] =
    SOME (value,gradient,hessian) ==>
  ?root_gradient two_over_root_four b_hessian_base b_hessian.
    bounded_object_fs_historical_b_hessian_decimal
      (bounded_interval64_object_cv root_delta)
      (bounded_interval64_object_cv two_over_root_four)
      (bounded_interval64_object_cv diagonal_reciprocal)
      (bounded_interval64_object_cv_list root_gradient)
      (bounded_interval64_object_cv_list b_hessian_base) =
    SOME (bounded_interval64_object_cv_list b_hessian)
Proof
  strip_tac
  >> drule bounded_historical_dihedral_second64_decimal_source_trace
  >> strip_tac
  >> imp_res_tac bounded_object_fs_historical_b_hessian_decimal_exact
  >> qexists_tac `root_gradient`
  >> qexists_tac `two_over_root_four`
  >> qexists_tac `b_hessian_base`
  >> qexists_tac `b_hessian`
  >> simp []
QED

Theorem bounded_historical_dihedral_second64_decimal_hessian_object_trace:
  bounded_historical_dihedral_second64_decimal environment root_delta
      root_four_x0
      [root_derivative;root_logarithmic;root_four_reciprocal;
       diagonal_reciprocal;u_reciprocal;special_root_reciprocal;
       b_reciprocal;u126_reciprocal;u135_reciprocal] =
    SOME (value,gradient,hessian) ==>
  ?delta_x4 b delta_x4_gradient b_gradient logarithmic_u_gradient
   delta_x4_hessian b_hessian.
    bounded_object_fs_historical_second_hessian_decimal
      (bounded_interval64_object_cv delta_x4)
      (bounded_interval64_object_cv b)
      (bounded_interval64_object_cv u_reciprocal)
      (bounded_interval64_object_cv_list delta_x4_gradient)
      (bounded_interval64_object_cv_list b_gradient)
      (bounded_interval64_object_cv_list gradient)
      (bounded_interval64_object_cv_list logarithmic_u_gradient)
      bounded_delta64_hessian_indices
      (bounded_interval64_object_cv_list delta_x4_hessian)
      (bounded_interval64_object_cv_list b_hessian) =
    SOME (bounded_interval64_object_cv_list hessian)
Proof
  strip_tac
  >> drule bounded_historical_dihedral_second64_decimal_source_trace
  >> strip_tac
  >> imp_res_tac bounded_object_fs_historical_second_hessian_decimal_exact
  >> qexists_tac `delta_x4`
  >> qexists_tac `b`
  >> qexists_tac `delta_x4_gradient`
  >> qexists_tac `b_gradient`
  >> qexists_tac `logarithmic_u_gradient`
  >> qexists_tac `delta_x4_hessian`
  >> qexists_tac `b_hessian`
  >> simp []
QED

Theorem bounded_signed64_zero_le_iff_nonnegative:
  bounded_signed64_le (BoundedSigned64 F 0w) value =
    bounded_signed64_nonnegative value
Proof
  Cases_on `value`
  >> Cases_on `b`
  >> Cases_on `w = 0w`
  >> simp
       [compute_boundedSignedEndpointTheory.bounded_signed64_le_def,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
        wordsTheory.WORD_LO]
QED

Theorem bounded_signed64_le_zero_iff_nonpositive:
  bounded_signed64_le value (BoundedSigned64 F 0w) =
    bounded_signed64_nonpositive value
Proof
  Cases_on `value`
  >> Cases_on `b`
  >> Cases_on `w = 0w`
  >> simp
       [compute_boundedSignedEndpointTheory.bounded_signed64_le_def,
        compute_boundedIntervalTheory.bounded_signed64_nonpositive_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
        wordsTheory.WORD_LO]
QED

Definition bounded_object_fs_historical_monotone_coordinate_def:
  bounded_object_fs_historical_monotone_coordinate value derivative upper =
    case bounded_object_fs_raw_le
      (bounded_signed64_object_cv (BoundedSigned64 F 0w))
      (bounded_signed64_object_cv (bounded_interval64_lower derivative)) of
    | NONE => NONE
    | SOME nonnegative =>
      if nonnegative then
        let endpoint =
          if upper then bounded_interval64_upper value
          else bounded_interval64_lower value in
        SOME
          (Pair (bounded_signed64_object_cv endpoint)
            (bounded_signed64_object_cv endpoint))
      else
        case bounded_object_fs_raw_le
          (bounded_signed64_object_cv (bounded_interval64_upper derivative))
          (bounded_signed64_object_cv (BoundedSigned64 F 0w)) of
        | NONE => NONE
        | SOME nonpositive =>
          if nonpositive then
            let endpoint =
              if upper then bounded_interval64_lower value
              else bounded_interval64_upper value in
            SOME
              (Pair (bounded_signed64_object_cv endpoint)
                (bounded_signed64_object_cv endpoint))
          else SOME (bounded_interval64_object_cv value)
End

Theorem bounded_object_fs_historical_monotone_coordinate_exact:
  bounded_object_fs_historical_monotone_coordinate value derivative upper =
    SOME
      (bounded_interval64_object_cv
        (bounded_historical_monotone_coordinate value derivative upper))
Proof
  Cases_on `value`
  >> Cases_on `derivative`
  >> Cases_on `upper`
  >> Cases_on `bounded_signed64_nonnegative b'`
  >> Cases_on `bounded_signed64_nonpositive b''`
  >> simp
       [bounded_object_fs_historical_monotone_coordinate_def,
        compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_le_object_cv,
        bounded_signed64_zero_le_iff_nonnegative,
        bounded_signed64_le_zero_iff_nonpositive,
        compute_boundedHistoricalDihedralSecondTheory.bounded_historical_monotone_coordinate_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_lower_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_upper_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> every_case_tac
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Definition bounded_object_fs_historical_monotone_environment_def:
  bounded_object_fs_historical_monotone_environment [] [] upper =
      SOME (Num 0 : cv) /\
  bounded_object_fs_historical_monotone_environment (value::values)
      (derivative::derivatives) upper =
    (case bounded_object_fs_historical_monotone_coordinate
      value derivative upper of
    | NONE => NONE
    | SOME coordinate =>
      case bounded_object_fs_historical_monotone_environment
        values derivatives upper of
      | NONE => NONE
      | SOME rest => SOME (Pair coordinate rest)) /\
  bounded_object_fs_historical_monotone_environment _ _ upper = NONE
End

Theorem bounded_object_fs_historical_monotone_environment_exact:
  !derivatives upper result.
    bounded_historical_monotone_environment values derivatives upper =
      SOME result ==>
    bounded_object_fs_historical_monotone_environment
      values derivatives upper =
    SOME (bounded_interval64_object_cv_list result)
Proof
  Induct_on `values`
  >> Cases_on `derivatives`
  >> rw
       [compute_boundedHistoricalDihedralSecondTheory.bounded_historical_monotone_environment_def,
        bounded_object_fs_historical_monotone_environment_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> every_case_tac
  >> gvs [bounded_object_fs_historical_monotone_coordinate_exact]
  >> res_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_historical_extreme_interval_def:
  bounded_object_fs_historical_extreme_interval lower_value upper_value =
    case bounded_object_fs_interval_endpoints
      (bounded_interval64_object_cv lower_value) of
    | NONE => NONE
    | SOME (lower,_) =>
      case bounded_object_fs_interval_endpoints
        (bounded_interval64_object_cv upper_value) of
      | NONE => NONE
      | SOME (_,upper) => SOME (Pair lower upper)
End

Theorem bounded_object_fs_historical_extreme_interval_exact:
  bounded_object_fs_historical_extreme_interval lower_value upper_value =
    SOME
      (bounded_interval64_object_cv
        (bounded_historical_extreme_interval lower_value upper_value))
Proof
  Cases_on `lower_value`
  >> Cases_on `upper_value`
  >> simp
       [bounded_object_fs_historical_extreme_interval_def,
        bounded_object_fs_interval_endpoints_exact,
        compute_boundedHistoricalDihedralSecondTheory.bounded_historical_extreme_interval_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

val _ = export_theory ();
