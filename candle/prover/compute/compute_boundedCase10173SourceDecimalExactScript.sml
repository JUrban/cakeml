(*****************************************************************************
 * Exact decimal identity for authenticated source rational intervals.
 *
 * Canonical outward conversion alone does not say that a rational endpoint
 * was already exactly representable at the fixed 10^12 scale.  The genuine
 * case-10173 square-root records have that stronger property.  These
 * first-order predicates expose it for compiled authentication and connect it
 * to both object conversion and the representation-independent rational
 * relation used by registered evaluator proofs.
 *****************************************************************************)
Theory compute_boundedCase10173SourceDecimalExact
Ancestors
  compute_boundedCase10173DecimalInputBinding
  compute_boundedQNormalizeRelation
Libs
  bossLib preamble wordsLib

Definition bounded_case10173_positive_endpoint64_q_cv_def:
  bounded_case10173_positive_endpoint64_q_cv
      (BoundedSigned64 negative magnitude) =
    Pair (Pair (Num (w2n magnitude)) (Num 0)) (Num 999999999999)
End

Definition bounded_case10173_source_positive_q_endpoint64_exact_def:
  bounded_case10173_source_positive_q_endpoint64_exact
      (encoded : cv) endpoint =
    (bounded_object_positive_q_floor64_decimal encoded = SOME endpoint /\
     bounded_object_positive_q_ceil64_decimal encoded = SOME endpoint /\
     bounded_case10173_q_cv_equiv encoded
       (bounded_case10173_positive_endpoint64_q_cv endpoint))
End

Definition bounded_case10173_source_positive_q_interval64_exact_def:
  bounded_case10173_source_positive_q_interval64_exact
      (Pair lower upper : cv)
      (BoundedInterval64 lower64 upper64) =
    (bounded_case10173_source_positive_q_endpoint64_exact lower lower64 /\
     bounded_case10173_source_positive_q_endpoint64_exact upper upper64 /\
     bounded_interval64_valid (BoundedInterval64 lower64 upper64)) /\
  bounded_case10173_source_positive_q_interval64_exact _ _ = F
End

Definition bounded_case10173_source_sqrt_decimal_prefix_exact_def:
  bounded_case10173_source_sqrt_decimal_prefix_exact
      0 center_roots box_roots certificates = T /\
  bounded_case10173_source_sqrt_decimal_prefix_exact
      (SUC remaining) (Pair center_root center_roots)
      (Pair box_root box_roots)
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
        center_derivative box_derivative box_second_reciprocal::certificates) =
    (bounded_case10173_source_positive_q_interval64_exact
       center_root center_sqrt /\
     bounded_case10173_source_positive_q_interval64_exact
       box_root box_sqrt /\
     bounded_case10173_source_sqrt_decimal_prefix_exact remaining
       center_roots box_roots certificates) /\
  bounded_case10173_source_sqrt_decimal_prefix_exact
      (SUC remaining) _ _ _ = F
End

Definition bounded_case10173_source_coordinate_sqrt_decimals_exact_def:
  bounded_case10173_source_coordinate_sqrt_decimals_exact
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals)
      (Pair box_sqrt_data (Pair center_sqrt_data source_boxes) : cv) =
    bounded_case10173_source_sqrt_decimal_prefix_exact 6
      center_sqrt_data box_sqrt_data coordinate_sqrt_certificates /\
  bounded_case10173_source_coordinate_sqrt_decimals_exact _ _ = F
End

Theorem bounded_case10173_source_positive_q_endpoint64_exact_equiv:
  bounded_case10173_source_positive_q_endpoint64_exact encoded endpoint ==>
  bounded_case10173_q_cv_equiv encoded
    (bounded_case10173_positive_endpoint64_q_cv endpoint)
Proof
  simp [bounded_case10173_source_positive_q_endpoint64_exact_def]
QED

Theorem bounded_case10173_source_positive_q_endpoint64_exact_conversion:
  bounded_case10173_source_positive_q_endpoint64_exact encoded endpoint ==>
  bounded_object_positive_q_floor64_decimal encoded = SOME endpoint /\
  bounded_object_positive_q_ceil64_decimal encoded = SOME endpoint
Proof
  simp [bounded_case10173_source_positive_q_endpoint64_exact_def]
QED

Theorem bounded_case10173_source_positive_q_interval64_exact_conversion:
  bounded_case10173_source_positive_q_interval64_exact encoded interval ==>
  bounded_object_positive_q_interval64_decimal encoded = SOME interval
Proof
  Cases_on `encoded`
  >> Cases_on `interval`
  >> rw [bounded_case10173_source_positive_q_interval64_exact_def]
  >> imp_res_tac
       bounded_case10173_source_positive_q_endpoint64_exact_conversion
  >> simp
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_def]
QED

Theorem bounded_case10173_source_sqrt_decimal_prefix_exact_cons:
  bounded_case10173_source_sqrt_decimal_prefix_exact
      (SUC remaining) (Pair center_root center_roots)
      (Pair box_root box_roots)
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
        center_derivative box_derivative box_second_reciprocal::certificates) ==>
  bounded_case10173_source_positive_q_interval64_exact
    center_root center_sqrt /\
  bounded_case10173_source_positive_q_interval64_exact
    box_root box_sqrt /\
  bounded_case10173_source_sqrt_decimal_prefix_exact remaining
    center_roots box_roots certificates
Proof
  simp [bounded_case10173_source_sqrt_decimal_prefix_exact_def]
QED

val _ = export_theory ();
