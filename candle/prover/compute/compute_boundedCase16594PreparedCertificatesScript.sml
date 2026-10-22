(*****************************************************************************
 * Checked decompression of the case16594 typed scalar certificate fixture.
 *
 * Balanced trees keep the generated constant compact without turning the
 * recurring evaluator into a linear dictionary scan.  Every tree lookup and
 * typed reconstruction is total; absent indices or malformed record shapes
 * fail closed.  The resulting certificates remain untrusted and are checked
 * by the scalar operations when the analytic program runs.
 *****************************************************************************)
Theory compute_boundedCase16594PreparedCertificates
Ancestors
  compute_boundedCase16594AnalyticCertificateData
Libs
  bossLib preamble

Definition bounded_case16594_tree_lookup_def:
  bounded_case16594_tree_lookup index C16594Empty = NONE ∧
  bounded_case16594_tree_lookup index
      (C16594Node key value left right) =
    if index = key then SOME value
    else if index < key then bounded_case16594_tree_lookup index left
    else bounded_case16594_tree_lookup index right
End

Definition bounded_case16594_prepare_raw_interval_def:
  bounded_case16594_prepare_raw_interval
      (C16594RawInterval lower_negative lower_magnitude
        upper_negative upper_magnitude) =
    BoundedInterval64
      (BoundedSigned64 lower_negative lower_magnitude)
      (BoundedSigned64 upper_negative upper_magnitude)
End

Definition bounded_case16594_prepare_interval_def:
  bounded_case16594_prepare_interval index =
    case bounded_case16594_tree_lookup index
      bounded_case16594_interval_tree of
    | NONE => NONE
    | SOME raw => SOME (bounded_case16594_prepare_raw_interval raw)
End

Definition bounded_case16594_prepare_interval_list_def:
  bounded_case16594_prepare_interval_list [] = SOME [] ∧
  bounded_case16594_prepare_interval_list (index::indices) =
    case bounded_case16594_prepare_interval index of
    | NONE => NONE
    | SOME value =>
      case bounded_case16594_prepare_interval_list indices of
      | NONE => NONE
      | SOME rest => SOME (value::rest)
End

Definition bounded_case16594_prepare_interval_option_def:
  bounded_case16594_prepare_interval_option NONE = SOME NONE ∧
  bounded_case16594_prepare_interval_option (SOME index) =
    case bounded_case16594_prepare_interval index of
    | NONE => NONE
    | SOME value => SOME (SOME value)
End

Definition bounded_case16594_prepare_certificate_def:
  bounded_case16594_prepare_certificate index =
    case bounded_case16594_tree_lookup index
      bounded_case16594_certificate_tree of
    | NONE => NONE
    | SOME raw =>
      case raw of
      | C16594RawSqrt center_sqrt box_sqrt center_derivative
          box_derivative box_second_reciprocal =>
          (case bounded_case16594_prepare_interval_list
            [center_sqrt;box_sqrt;center_derivative;box_derivative;
             box_second_reciprocal] of
           | SOME [a;b;c;d;e] =>
               SOME (BoundedAnalytic64SqrtCertificate a b c d e)
           | _ => NONE)
      | C16594RawInverse center_reciprocal box_reciprocal =>
          (case bounded_case16594_prepare_interval_list
            [center_reciprocal;box_reciprocal] of
           | SOME [a;b] =>
               SOME (BoundedAnalytic64InverseCertificate a b)
           | _ => NONE)
      | C16594RawAtan lower_reciprocal upper_reciprocal
          center_derivative box_derivative =>
          (case (bounded_case16594_prepare_interval_option lower_reciprocal,
                 bounded_case16594_prepare_interval_option upper_reciprocal,
                 bounded_case16594_prepare_interval center_derivative,
                 bounded_case16594_prepare_interval box_derivative) of
           | (SOME lower,SOME upper,SOME center,SOME box) =>
               SOME (BoundedAnalytic64AtanCertificate
                 lower upper center box)
           | _ => NONE)
End

Definition bounded_case16594_prepare_certificate_list_def:
  bounded_case16594_prepare_certificate_list [] = SOME [] ∧
  bounded_case16594_prepare_certificate_list (index::indices) =
    case bounded_case16594_prepare_certificate index of
    | NONE => NONE
    | SOME value =>
      case bounded_case16594_prepare_certificate_list indices of
      | NONE => NONE
      | SOME rest => SOME (value::rest)
End

Definition bounded_case16594_prepare_certificate_cells_def:
  bounded_case16594_prepare_certificate_cells [] = SOME [] ∧
  bounded_case16594_prepare_certificate_cells (plan::plans) =
    case bounded_case16594_prepare_certificate_list plan of
    | NONE => NONE
    | SOME certificates =>
      case bounded_case16594_prepare_certificate_cells plans of
      | NONE => NONE
      | SOME rest => SOME (certificates::rest)
End

Definition bounded_case16594_prepared_certificates_def:
  bounded_case16594_prepared_certificates =
    case bounded_case16594_prepare_certificate_cells
      bounded_case16594_certificate_plans of
    | NONE => []
    | SOME cells => cells
End

Definition bounded_case16594_prepared_certificates_ok_def:
  bounded_case16594_prepared_certificates_ok ⇔
    bounded_case16594_prepare_certificate_cells
      bounded_case16594_certificate_plans =
        SOME bounded_case16594_prepared_certificates ∧
    LENGTH bounded_case16594_prepared_certificates = 875 ∧
    EVERY (λcertificates. LENGTH certificates = 31)
      bounded_case16594_prepared_certificates
End

Theorem bounded_case16594_tree_lookup_closed_tests:
  bounded_case16594_tree_lookup 2
    (C16594Node 2 17 C16594Empty C16594Empty) = SOME 17 ∧
  bounded_case16594_tree_lookup 1
    (C16594Node 2 17
      (C16594Node 1 19 C16594Empty C16594Empty) C16594Empty) = SOME 19 ∧
  bounded_case16594_tree_lookup 3
    (C16594Node 2 17 C16594Empty
      (C16594Node 3 23 C16594Empty C16594Empty)) = SOME 23 ∧
  bounded_case16594_tree_lookup 4
    (C16594Node 2 17 C16594Empty C16594Empty) = NONE
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_prepare_certificate_list_length:
  ∀indices certificates.
    bounded_case16594_prepare_certificate_list indices =
      SOME certificates ⇒
    LENGTH certificates = LENGTH indices
Proof
  Induct >> rw [bounded_case16594_prepare_certificate_list_def]
  >> every_case_tac >> gvs []
QED

Theorem bounded_case16594_prepare_certificate_cells_length:
  ∀plans certificates.
    bounded_case16594_prepare_certificate_cells plans =
      SOME certificates ⇒
    LENGTH certificates = LENGTH plans
Proof
  Induct >> rw [bounded_case16594_prepare_certificate_cells_def]
  >> every_case_tac >> gvs []
QED

val _ = export_theory ();
