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

Definition bounded_object_fs_taylor64_sqrt_decimal_def:
  bounded_object_fs_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal source =
    case source of
    | BoundedTaylor64 source_domain center_value center_gradient
        value_bound gradient_bounds hessian =>
      if ~bounded_interval64_positive_sqrt_certificate_decimal
            center_value center_sqrt \/
         ~bounded_interval64_positive_sqrt_certificate_decimal
            value_bound box_sqrt
      then NONE
      else if bounded_object_fs_hist_positive_root_certificate
        (bounded_interval64_object_cv center_value)
        (bounded_interval64_object_cv center_sqrt) <> Num 1
      then NONE
      else if bounded_object_fs_hist_positive_root_certificate
        (bounded_interval64_object_cv value_bound)
        (bounded_interval64_object_cv box_sqrt) <> Num 1
      then NONE
      else
        case bounded_interval64_add center_sqrt center_sqrt of
        | NONE => NONE
        | SOME center_twice =>
          case bounded_object_fs_interval_add
            (bounded_interval64_object_cv center_sqrt)
            (bounded_interval64_object_cv center_sqrt) of
          | NONE => NONE
          | SOME object_center_twice =>
            case bounded_interval64_add box_sqrt box_sqrt of
            | NONE => NONE
            | SOME box_twice =>
              case bounded_object_fs_interval_add
                (bounded_interval64_object_cv box_sqrt)
                (bounded_interval64_object_cv box_sqrt) of
              | NONE => NONE
              | SOME object_box_twice =>
                case bounded_interval64_add value_bound value_bound of
                | NONE => NONE
                | SOME input_twice =>
                  case bounded_object_fs_interval_add
                    (bounded_interval64_object_cv value_bound)
                    (bounded_interval64_object_cv value_bound) of
                  | NONE => NONE
                  | SOME object_input_twice =>
                    case bounded_interval64_mul_decimal
                      box_twice input_twice of
                    | NONE => NONE
                    | SOME box_second_denominator =>
                      case bounded_object_fs_interval_mul_decimal
                        object_box_twice object_input_twice of
                      | NONE => NONE
                      | SOME object_box_second_denominator =>
                        if
                          ~bounded_interval64_positive_inv_certificate_decimal
                            center_twice center_derivative \/
                          ~bounded_interval64_positive_inv_certificate_decimal
                            box_twice box_derivative \/
                          ~bounded_interval64_positive_inv_certificate_decimal
                            box_second_denominator box_second_reciprocal
                        then NONE
                        else
                          case bounded_object_fs_hist_positive_inv
                            object_center_twice of
                          | NONE => NONE
                          | SOME object_center_derivative =>
                            case bounded_object_fs_hist_positive_inv
                              object_box_twice of
                            | NONE => NONE
                            | SOME object_box_derivative =>
                              case bounded_object_fs_hist_positive_inv
                                object_box_second_denominator of
                              | NONE => NONE
                              | SOME object_box_second_reciprocal =>
                                case bounded_object_fs_interval_neg
                                  (bounded_interval64_object_cv
                                    box_second_reciprocal) of
                                | NONE => NONE
                                | SOME object_negative_box_second =>
                                  case
                                    bounded_taylor64_unary_complete_decimal
                                      radii T center_sqrt center_derivative
                                      box_derivative
                                      (bounded_interval64_neg
                                        box_second_reciprocal) source of
                                  | NONE => NONE
                                  | SOME result =>
                                      bounded_object_fs_taylor64_unary_complete_decimal
                                        radii T center_sqrt center_derivative
                                        box_derivative
                                        (bounded_interval64_neg
                                          box_second_reciprocal) source
End

Theorem bounded_taylor64_sqrt_decimal_object_trace:
  bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal source =
    SOME result ==>
  ?source_domain center_value center_gradient value_bound gradient_bounds
   hessian center_twice box_twice input_twice box_second_denominator.
    source =
      BoundedTaylor64 source_domain center_value center_gradient value_bound
        gradient_bounds hessian /\
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

Theorem bounded_object_fs_taylor64_sqrt_decimal_exact:
  bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal source =
    SOME result ==>
  ?hessian_rows.
    bounded_object_fs_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal source =
    SOME (bounded_taylor64_rows_object_cv result hessian_rows)
Proof
  strip_tac
  >> drule bounded_taylor64_sqrt_decimal_object_trace
  >> strip_tac
  >> drule
       compute_boundedObjectTaylorUnaryDecimalTheory.bounded_object_fs_taylor64_unary_complete_decimal_exact
  >> strip_tac
  >> qexists_tac `hessian_rows`
  >> qpat_x_assum
       `source =
          BoundedTaylor64 source_domain center_value center_gradient
            value_bound gradient_bounds hessian`
       (fn source_shape =>
  qpat_x_assum
       `bounded_object_fs_hist_positive_root_certificate
          (bounded_interval64_object_cv center_value)
          (bounded_interval64_object_cv center_sqrt) = Num 1`
       (fn object_center_root =>
  qpat_x_assum
       `bounded_object_fs_hist_positive_root_certificate
          (bounded_interval64_object_cv value_bound)
          (bounded_interval64_object_cv box_sqrt) = Num 1`
       (fn object_box_root =>
  qpat_x_assum
       `bounded_object_fs_interval_add
          (bounded_interval64_object_cv center_sqrt)
          (bounded_interval64_object_cv center_sqrt) = SOME _`
       (fn object_center_twice =>
  qpat_x_assum
       `bounded_object_fs_interval_add
          (bounded_interval64_object_cv box_sqrt)
          (bounded_interval64_object_cv box_sqrt) = SOME _`
       (fn object_box_twice =>
  qpat_x_assum
       `bounded_interval64_add value_bound value_bound = SOME _`
       (fn source_input_twice =>
  qpat_x_assum
       `bounded_object_fs_interval_add
          (bounded_interval64_object_cv value_bound)
          (bounded_interval64_object_cv value_bound) = SOME _`
       (fn object_input_twice =>
  qpat_x_assum
       `bounded_interval64_mul_decimal box_twice input_twice = SOME _`
       (fn source_denominator =>
  qpat_x_assum
       `bounded_object_fs_interval_mul_decimal
          (bounded_interval64_object_cv box_twice)
          (bounded_interval64_object_cv input_twice) = SOME _`
       (fn object_denominator =>
  qpat_x_assum
       `bounded_object_fs_hist_positive_inv
          (bounded_interval64_object_cv center_twice) = SOME _`
       (fn object_center_inv =>
  qpat_x_assum
       `bounded_object_fs_hist_positive_inv
          (bounded_interval64_object_cv box_twice) = SOME _`
       (fn object_box_inv =>
  qpat_x_assum
       `bounded_object_fs_hist_positive_inv
          (bounded_interval64_object_cv box_second_denominator) = SOME _`
       (fn object_denominator_inv =>
  qpat_x_assum
       `bounded_object_fs_interval_neg
          (bounded_interval64_object_cv box_second_reciprocal) = SOME _`
       (fn object_negative =>
  qpat_x_assum
       `bounded_taylor64_unary_complete_decimal radii T center_sqrt
          center_derivative box_derivative
          (bounded_interval64_neg box_second_reciprocal) source = SOME _`
       (fn source_unary =>
  qpat_x_assum
       `bounded_object_fs_taylor64_unary_complete_decimal radii T
          center_sqrt center_derivative box_derivative
          (bounded_interval64_neg box_second_reciprocal) source = SOME _`
       (fn object_unary =>
          map_every assume_tac
               [source_shape, object_center_root, object_box_root,
                object_center_twice,
                object_box_twice, source_input_twice, object_input_twice,
                source_denominator, object_denominator, object_center_inv,
                object_box_inv, object_denominator_inv, object_negative,
                source_unary, object_unary]
          >> gvs
               [bounded_object_fs_taylor64_sqrt_decimal_def,
                compute_boundedTaylorSqrtDecimalTheory.bounded_taylor64_sqrt_decimal_def]
          >> once_rewrite_tac [object_center_root]
          >> simp []
          >> once_rewrite_tac [object_box_root]
          >> simp []
          >> once_rewrite_tac [source_input_twice]
          >> simp []
          >> once_rewrite_tac [object_input_twice]
          >> simp []
          >> once_rewrite_tac [source_denominator]
          >> simp []
          >> once_rewrite_tac [object_denominator]
          >> simp []
          >> once_rewrite_tac [object_denominator_inv]
          >> simp []
          >> once_rewrite_tac [object_negative]
          >> simp []
          >> once_rewrite_tac [source_unary]
          >> simp []
          >> once_rewrite_tac [object_unary]
          >> simp [source_shape])))))))))))))))
QED

val _ = export_theory ();
