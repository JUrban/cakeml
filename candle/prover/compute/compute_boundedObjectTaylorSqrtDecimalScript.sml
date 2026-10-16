(*****************************************************************************
 * Exact object trace for the decimal square-root Taylor lift.
 *
 * Successful specialized execution now authenticates the supplied roots and
 * every reciprocal against the deterministic object operations.  This trace
 * exposes those equalities together with exact object addition,
 * multiplication, negation, and the already-proved unary completion layer.
 *****************************************************************************)
Theory compute_boundedObjectTaylorSqrtDecimal
Ancestors
  compute_boundedObjectTaylorUnaryDecimal compute_boundedTaylorSqrtDecimal
Libs
  bossLib preamble

Theorem bounded_taylor64_sqrt_decimal_object_trace:
  bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal source =
    SOME result ==>
  ?center_value value_bound center_twice box_twice input_twice
   box_second_denominator.
    bounded_interval64_add center_sqrt center_sqrt = SOME center_twice /\
    bounded_interval64_add box_sqrt box_sqrt = SOME box_twice /\
    bounded_interval64_add value_bound value_bound = SOME input_twice /\
    bounded_interval64_mul_decimal box_twice input_twice =
      SOME box_second_denominator /\
    bounded_object_fs_hist_positive_root_certificate
      (bounded_interval64_object_cv center_value)
      (bounded_interval64_object_cv center_sqrt) = Num 1 /\
    bounded_object_fs_hist_positive_root_certificate
      (bounded_interval64_object_cv value_bound)
      (bounded_interval64_object_cv box_sqrt) = Num 1 /\
    bounded_object_fs_hist_positive_inv
      (bounded_interval64_object_cv center_twice) =
      SOME (bounded_interval64_object_cv center_derivative) /\
    bounded_object_fs_hist_positive_inv
      (bounded_interval64_object_cv box_twice) =
      SOME (bounded_interval64_object_cv box_derivative) /\
    bounded_object_fs_hist_positive_inv
      (bounded_interval64_object_cv box_second_denominator) =
      SOME (bounded_interval64_object_cv box_second_reciprocal) /\
    bounded_object_fs_interval_add
      (bounded_interval64_object_cv center_sqrt)
      (bounded_interval64_object_cv center_sqrt) =
      SOME (bounded_interval64_object_cv center_twice) /\
    bounded_object_fs_interval_add
      (bounded_interval64_object_cv box_sqrt)
      (bounded_interval64_object_cv box_sqrt) =
      SOME (bounded_interval64_object_cv box_twice) /\
    bounded_object_fs_interval_add
      (bounded_interval64_object_cv value_bound)
      (bounded_interval64_object_cv value_bound) =
      SOME (bounded_interval64_object_cv input_twice) /\
    bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv box_twice)
      (bounded_interval64_object_cv input_twice) =
      SOME (bounded_interval64_object_cv box_second_denominator) /\
    bounded_object_fs_interval_neg
      (bounded_interval64_object_cv box_second_reciprocal) =
      SOME (bounded_interval64_object_cv
        (bounded_interval64_neg box_second_reciprocal)) /\
    bounded_taylor64_unary_complete_decimal radii T center_sqrt
      center_derivative box_derivative
      (bounded_interval64_neg box_second_reciprocal) source = SOME result
Proof
  Cases_on `source`
  >> rw [compute_boundedTaylorSqrtDecimalTheory.bounded_taylor64_sqrt_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_sqrt_certificate_decimal_object_exact
  >> imp_res_tac
       compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_inv_certificate_decimal_object_exact
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
  >> metis_tac []
QED

val _ = export_theory ();
