(*****************************************************************************
 * Semantic contract for the ordinary five-payload packed-object entry.
 *
 * The entry consumes exact object-q radii, whereas the established packed
 * checker theorem starts from scale-2^40 word radii.  This theory states the
 * exact-q formula once and proves that mapping authenticated word radii to
 * their exact object-q values recovers the existing ordinary acceptance
 * contract.  Registered evaluator equations are deliberately not imported
 * here; their refinement to this contract is a separate boundary.
 *****************************************************************************)
Theory compute_boundedPackedObjectEntryContract
Ancestors
  compute_boundedPackedObjectAcceptRefinement
Libs
  bossLib preamble

Definition bounded_object_q_exact_dot_terms_cv_def:
  bounded_object_q_exact_dot_terms_cv [] [] = [] /\
  bounded_object_q_exact_dot_terms_cv [] (_::_) = [] /\
  bounded_object_q_exact_dot_terms_cv (_::_) [] = [] /\
  bounded_object_q_exact_dot_terms_cv
      (radius::radii) (entry::entries) =
    bounded_object_q_mul_cv radius
      (bounded_object_q_interval_abs_upper_cv entry) ::
    bounded_object_q_exact_dot_terms_cv radii entries
End

Definition bounded_object_q_exact_radius_pairs6_cv_def:
  bounded_object_q_exact_radius_pairs6_cv (radii:cv list) =
    case radii of
    | r0::r1::r2::r3::r4::r5::[] =>
        SOME
          [(r0,r0,F);
           (r0,r1,T); (r0,r2,T); (r0,r3,T); (r0,r4,T); (r0,r5,T);
           (r1,r1,F);
           (r1,r2,T); (r1,r3,T); (r1,r4,T); (r1,r5,T);
           (r2,r2,F);
           (r2,r3,T); (r2,r4,T); (r2,r5,T);
           (r3,r3,F);
           (r3,r4,T); (r3,r5,T);
           (r4,r4,F);
           (r4,r5,T);
           (r5,r5,F)]
    | _ => NONE
End

Definition bounded_object_q_exact_quadratic_contribution_cv_def:
  bounded_object_q_exact_quadratic_contribution_cv
      left_radius right_radius double entry =
    let raw =
      bounded_object_q_mul_cv
        (bounded_object_q_mul_cv left_radius right_radius)
        (bounded_object_q_interval_abs_upper_cv entry)
    in
      if double then bounded_object_q_add_cv raw raw else raw
End

Definition bounded_object_q_exact_quadratic_terms_cv_def:
  bounded_object_q_exact_quadratic_terms_cv [] [] = [] /\
  bounded_object_q_exact_quadratic_terms_cv [] (_::_) = [] /\
  bounded_object_q_exact_quadratic_terms_cv (_::_) [] = [] /\
  bounded_object_q_exact_quadratic_terms_cv
      ((left_radius,right_radius,double)::weights) (entry::entries) =
    bounded_object_q_exact_quadratic_contribution_cv
      left_radius right_radius double entry ::
    bounded_object_q_exact_quadratic_terms_cv weights entries
End

Definition bounded_object_q_exact_packed_error6_cv_def:
  bounded_object_q_exact_packed_error6_cv
      radii center_gradient hessian =
    case bounded_object_q_exact_radius_pairs6_cv radii of
    | NONE => bounded_object_q_zero_cv
    | SOME weights =>
        let linear =
          bounded_object_q_right_sum_cv
            (bounded_object_q_exact_dot_terms_cv radii center_gradient) in
        let quadratic =
          bounded_object_q_right_sum_cv
            (bounded_object_q_exact_quadratic_terms_cv weights hessian) in
          bounded_object_q_add_cv
            (bounded_object_q_add_cv linear linear) quadratic
End

Definition bounded_object_q_exact_packed_value_upper6_cv_def:
  bounded_object_q_exact_packed_value_upper6_cv
      radii center_value center_gradient hessian =
    bounded_object_q_add_cv
      (bounded_object_q_interval_upper_cv center_value)
      (bounded_object_q_ordinary_half_error_cv
        (bounded_object_q_exact_packed_error6_cv
          radii center_gradient hessian))
End

Definition bounded_object_q_exact_packed_accept6_def:
  bounded_object_q_exact_packed_accept6 domain radii center_value
      center_gradient hessian <=>
    domain /\
    LENGTH radii = 6 /\
    LENGTH center_gradient = 6 /\
    LENGTH hessian = 21 /\
    bounded_object_q_strict_negative_cv
      (bounded_object_q_exact_packed_value_upper6_cv
        radii center_value center_gradient hessian)
End

Definition bounded_object_q_cv_list_def:
  bounded_object_q_cv_list [] = Num 0 /\
  bounded_object_q_cv_list (item::items) =
    Pair item (bounded_object_q_cv_list items)
End

Definition bounded_object_q_cv_list_decode_def:
  bounded_object_q_cv_list_decode (Num 0) = SOME [] /\
  bounded_object_q_cv_list_decode (Num (SUC n)) = NONE /\
  bounded_object_q_cv_list_decode (Pair item items) =
    case bounded_object_q_cv_list_decode items of
    | NONE => NONE
    | SOME decoded => SOME (item::decoded)
End

Definition bounded_object_q_exact_packed_payload5_checker_def:
  bounded_object_q_exact_packed_payload5_checker
      domain_payload radii_payload center_value center_gradient_payload
      hessian_payload =
    if domain_payload <> Num 1 then F
    else
      case bounded_object_q_cv_list_decode radii_payload of
      | NONE => F
      | SOME radii =>
        case bounded_object_q_cv_list_decode center_gradient_payload of
        | NONE => F
        | SOME center_gradient =>
          case bounded_object_q_cv_list_decode hessian_payload of
          | NONE => F
          | SOME hessian =>
              bounded_object_q_exact_packed_accept6 T radii center_value
                center_gradient hessian
End

Theorem bounded_object_q_cv_list_decode_encode[simp]:
  bounded_object_q_cv_list_decode (bounded_object_q_cv_list items) =
    SOME items
Proof
  Induct_on `items`
  >> simp
       [bounded_object_q_cv_list_def,
        bounded_object_q_cv_list_decode_def]
QED

Theorem bounded_object_q_exact_packed_payload5_checker_canonical[simp]:
  bounded_object_q_exact_packed_payload5_checker
      (Num 1) (bounded_object_q_cv_list radii) center_value
      (bounded_object_q_cv_list center_gradient)
      (bounded_object_q_cv_list hessian) <=>
    bounded_object_q_exact_packed_accept6 T radii center_value
      center_gradient hessian
Proof
  simp [bounded_object_q_exact_packed_payload5_checker_def]
QED

Theorem bounded_object_q_exact_packed_payload5_checker_rejects_domain:
  domain_payload <> Num 1 ==>
  ~bounded_object_q_exact_packed_payload5_checker domain_payload
      radii_payload center_value center_gradient_payload hessian_payload
Proof
  simp [bounded_object_q_exact_packed_payload5_checker_def]
QED

Theorem bounded_object_q_exact_packed_payload5_checker_rejects_bad_radii:
  bounded_object_q_cv_list_decode radii_payload = NONE ==>
  ~bounded_object_q_exact_packed_payload5_checker (Num 1)
      radii_payload center_value center_gradient_payload hessian_payload
Proof
  simp [bounded_object_q_exact_packed_payload5_checker_def]
QED

Theorem bounded_object_q_exact_dot_terms_word_radii:
  !radii entries.
    bounded_object_q_exact_dot_terms_cv
      (MAP bounded_word64_object_q_cv radii) entries =
    bounded_object_q_dot_terms_cv radii entries
Proof
  Induct_on `radii`
  >> Cases_on `entries`
  >> simp
       [bounded_object_q_exact_dot_terms_cv_def,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_dot_terms_cv_def]
QED

Theorem bounded_object_q_exact_radius_pairs_word_radii:
  bounded_taylor_radius_pairs radii = SOME weights ==>
  bounded_object_q_exact_radius_pairs6_cv
      (MAP bounded_word64_object_q_cv radii) =
    SOME
      (MAP
        (\(left_radius,right_radius,double).
          (bounded_word64_object_q_cv left_radius,
           bounded_word64_object_q_cv right_radius,double))
        weights)
Proof
  rw [compute_boundedTaylorCompleteTheory.bounded_taylor_radius_pairs_def]
  >> every_case_tac
  >> gvs [bounded_object_q_exact_radius_pairs6_cv_def]
QED

Theorem bounded_object_q_exact_quadratic_contribution_word_radii:
  bounded_object_q_exact_quadratic_contribution_cv
      (bounded_word64_object_q_cv left_radius)
      (bounded_word64_object_q_cv right_radius) double entry =
    bounded_object_q_quadratic_contribution_cv
      left_radius right_radius double entry
Proof
  simp
    [bounded_object_q_exact_quadratic_contribution_cv_def,
     compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_quadratic_contribution_cv_def,
     LET_THM]
QED

Theorem bounded_object_q_exact_quadratic_terms_word_radii:
  !weights entries.
    bounded_object_q_exact_quadratic_terms_cv
      (MAP
        (\(left_radius,right_radius,double).
          (bounded_word64_object_q_cv left_radius,
           bounded_word64_object_q_cv right_radius,double))
        weights)
      entries =
    bounded_object_q_quadratic_terms_cv weights entries
Proof
  Induct_on `weights`
  >- (Cases_on `entries`
      >> simp
           [bounded_object_q_exact_quadratic_terms_cv_def,
            compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_quadratic_terms_cv_def])
  >> gen_tac
  >> PairCases_on `h`
  >> Cases_on `entries`
  >> simp
       [bounded_object_q_exact_quadratic_terms_cv_def,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_quadratic_terms_cv_def,
        bounded_object_q_exact_quadratic_contribution_word_radii]
QED

Theorem bounded_object_q_exact_packed_error_word_radii:
  bounded_taylor_radius_pairs radii = SOME weights ==>
  bounded_object_q_exact_packed_error6_cv
      (MAP bounded_word64_object_q_cv radii) center_gradient hessian =
    bounded_object_q_ordinary_error_cv
      radii center_gradient weights hessian
Proof
  strip_tac
  >> imp_res_tac bounded_object_q_exact_radius_pairs_word_radii
  >> rw
       [bounded_object_q_exact_packed_error6_cv_def,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_ordinary_error_cv_def,
        bounded_object_q_exact_dot_terms_word_radii,
        bounded_object_q_exact_quadratic_terms_word_radii,
        LET_THM]
QED

Theorem bounded_object_q_exact_packed_accept_word_radii:
  bounded_taylor_radius_pairs radii = SOME weights ==>
  (bounded_object_q_exact_packed_accept6 object_domain
      (MAP bounded_word64_object_q_cv radii) center_value
      center_gradient hessian <=>
   bounded_object_q_ordinary_accept6 object_domain radii center_value
      center_gradient weights hessian)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths
  >> `bounded_object_q_exact_packed_error6_cv
        (MAP bounded_word64_object_q_cv radii) center_gradient hessian =
      bounded_object_q_ordinary_error_cv
        radii center_gradient weights hessian` by
       metis_tac [bounded_object_q_exact_packed_error_word_radii]
  >> rw
       [bounded_object_q_exact_packed_accept6_def,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_ordinary_accept6_def,
        bounded_object_q_exact_packed_value_upper6_cv_def,
        bounded_object_q_ordinary_value_upper_cv_def,
        LET_THM]
QED

Theorem bounded_object_q_exact_packed_payload5_checker_word_radii:
  bounded_taylor_radius_pairs radii = SOME weights ==>
  (bounded_object_q_exact_packed_payload5_checker
      (Num 1)
      (bounded_object_q_cv_list
        (MAP bounded_word64_object_q_cv radii))
      center_value
      (bounded_object_q_cv_list center_gradient)
      (bounded_object_q_cv_list hessian) <=>
   bounded_object_q_ordinary_accept6 T radii center_value
      center_gradient weights hessian)
Proof
  simp [bounded_object_q_exact_packed_accept_word_radii]
QED

val _ = export_theory ();
