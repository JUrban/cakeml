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

val _ = export_theory ();
