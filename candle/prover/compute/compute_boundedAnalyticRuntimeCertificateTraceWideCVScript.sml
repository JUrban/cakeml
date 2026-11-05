(*****************************************************************************
 * Reusable cv_compute translations for the wide Taylor arithmetic reached
 * by the runtime-certificate trace.  The production checker is unchanged:
 * these equations only expose local pair results as pattern matches, which
 * the CV translator can represent directly.  The packet-only translations
 * live in the preceding theory so edits here do not rebuild that closure.
 *****************************************************************************)
Theory compute_boundedAnalyticRuntimeCertificateTraceWideCV
Ancestors
  compute_boundedAnalyticRuntimeCertificateTraceCV
Libs
  bossLib preamble cv_transLib

Theorem bounded_word64_sub_borrow_in_cv_eq[local]:
  bounded_word64_sub_borrow_in left right borrow_in =
    case bounded_word64_sub_borrow left right of
    | (first_value,first_borrow) =>
        if borrow_in then
          case bounded_word64_sub_borrow first_value 1w of
          | (second_value,second_borrow) =>
              (second_value,first_borrow \/ second_borrow)
        else (first_value,first_borrow)
Proof
  Cases_on `bounded_word64_sub_borrow left right`
  >> Cases_on `bounded_word64_sub_borrow q 1w`
  >> rw [compute_boundedWideTheory.bounded_word64_sub_borrow_in_def]
QED

val _ = cv_auto_trans bounded_word64_sub_borrow_in_cv_eq;

Theorem bounded192_sub_words_cv_eq[local]:
  bounded192_sub_words
      (Bounded192 left_high left_middle left_low)
      (Bounded192 right_high right_middle right_low) =
    if bounded192_le_words
         (Bounded192 right_high right_middle right_low)
         (Bounded192 left_high left_middle left_low)
    then
      case bounded_word64_sub_borrow left_low right_low of
      | (low_value,low_borrow) =>
        case bounded_word64_sub_borrow_in
          left_middle right_middle low_borrow of
        | (middle_value,middle_borrow) =>
          case bounded_word64_sub_borrow_in
            left_high right_high middle_borrow of
          | (high_value,high_borrow) =>
              if high_borrow then NONE
              else SOME (Bounded192 high_value middle_value low_value)
    else NONE
Proof
  Cases_on `bounded_word64_sub_borrow left_low right_low`
  >> Cases_on `bounded_word64_sub_borrow_in left_middle right_middle r`
  >> Cases_on `bounded_word64_sub_borrow_in left_high right_high r'`
  >> rw [compute_boundedWideTheory.bounded192_sub_words_def]
QED

val _ = cv_auto_trans bounded192_sub_words_cv_eq;

Theorem bounded128_mul_word64_to_192_words_cv_eq[local]:
  bounded128_mul_word64_to_192_words
      (Bounded128 left_high left_low) right =
    case bounded_word64_mul_full_chunks22 left_low right of
    | (low_high,low_low) =>
      case bounded_word64_mul_full_chunks22 left_high right of
      | (high_high,high_low) =>
        case bounded_word64_add_carry low_high high_low F of
        | (middle_value,middle_carry) =>
          case bounded_word64_add_carry high_high 0w middle_carry of
          | (high_value,high_carry) =>
              if high_carry then NONE
              else SOME (Bounded192 high_value middle_value low_low)
Proof
  rw [compute_boundedWideTheory.bounded128_mul_word64_to_192_words_def]
  >> every_case_tac
  >> gvs []
QED

val _ = cv_auto_trans bounded128_mul_word64_to_192_words_cv_eq;

(* Use the already-proved extensional implementation rather than exposing
 * the production carry helper's local pair projections to the translator. *)
val _ = cv_auto_trans compute_boundedTheory.bounded192_add_words_refines;

Theorem bounded_signed64_raw_product_cv_eq[local]:
  bounded_signed64_raw_product
      (BoundedSigned64 left_negative left_magnitude)
      (BoundedSigned64 right_negative right_magnitude) =
    case bounded_word64_mul_full_chunks22 left_magnitude right_magnitude of
    | (high,low) =>
        bounded_signed128_make (¬(left_negative = right_negative))
          (Bounded128 high low)
Proof
  Cases_on
    `bounded_word64_mul_full_chunks22 left_magnitude right_magnitude`
  >> Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> rw [compute_boundedTaylorMulTheory.bounded_signed64_raw_product_def]
QED

val _ = cv_auto_trans bounded_signed64_raw_product_cv_eq;

Theorem bounded_interval64_raw_sum_acc_cv_eq[local]:
  bounded_interval64_raw_sum_acc [] lower upper = SOME (lower,upper) /\
  bounded_interval64_raw_sum_acc ((left,right)::products) lower upper =
    if ¬bounded_interval64_valid left \/
       ¬bounded_interval64_valid right
    then NONE
    else
      case bounded_interval64_raw_mul_bounds_unchecked left right of
      | (lower_bound,upper_bound) =>
        case bounded_signed192_add lower
          (bounded_signed128_widen192 lower_bound) of
        | NONE => NONE
        | SOME next_lower =>
          case bounded_signed192_add upper
            (bounded_signed128_widen192 upper_bound) of
          | NONE => NONE
          | SOME next_upper =>
              bounded_interval64_raw_sum_acc
                products next_lower next_upper
Proof
  Cases_on `bounded_interval64_raw_mul_bounds_unchecked left right`
  >> rw [compute_boundedTaylorMulTheory.bounded_interval64_raw_sum_acc_def]
QED

val bounded_interval64_raw_sum_acc_pre_def =
  cv_auto_trans_pre "" (bounded_interval64_raw_sum_acc_cv_eq
    |> measure_args [0]);

Theorem bounded_interval64_raw_sum_acc_pre[cv_pre]:
  !products lower upper.
    bounded_interval64_raw_sum_acc_pre products lower upper
Proof
  Induct_on `products`
  >- rw [Once bounded_interval64_raw_sum_acc_pre_def]
  >> rpt gen_tac
  >> PairCases_on `h`
  >> rw [Once bounded_interval64_raw_sum_acc_pre_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_interval64_fused_hessian_cv_eq[local]:
  bounded_interval64_fused_hessian left_value right_value
      left_hessians right_hessians outer_pairs =
    case left_hessians of
    | [] =>
        (case right_hessians of
         | [] =>
             (case outer_pairs of
              | [] => SOME []
              | _::_ => NONE)
         | _::_ => NONE)
    | left_hessian::left_rest =>
        (case right_hessians of
         | [] => NONE
         | right_hessian::right_rest =>
             case outer_pairs of
             | [] => NONE
             | (outer_left,outer_right)::outer_rest =>
               case bounded_interval64_fused_products
                 [(right_value,left_hessian);outer_left;outer_right;
                  (left_value,right_hessian)] of
               | NONE => NONE
               | SOME entry =>
                 case bounded_interval64_fused_hessian
                   left_value right_value left_rest right_rest outer_rest of
                 | NONE => NONE
                 | SOME entries => SOME (entry::entries))
Proof
  Cases_on `left_hessians`
  >> Cases_on `right_hessians`
  >> Cases_on `outer_pairs`
  >> rw [compute_boundedTaylorMulTheory.bounded_interval64_fused_hessian_def]
  >> every_case_tac
  >> gvs []
QED

val bounded_interval64_fused_hessian_pre_def =
  cv_auto_trans_pre "" (bounded_interval64_fused_hessian_cv_eq
    |> measure_args [2]);

Theorem bounded_interval64_fused_hessian_pre[cv_pre]:
  !left_hessian right_hessian outer.
    bounded_interval64_fused_hessian_pre left_value right_value
      left_hessian right_hessian outer
Proof
  Induct_on `left_hessian`
  >- (rpt gen_tac
      >> Cases_on `right_hessian`
      >> Cases_on `outer`
      >> rw [Once bounded_interval64_fused_hessian_pre_def])
  >> rpt gen_tac
  >> Cases_on `right_hessian`
  >> Cases_on `outer`
  >> rw [Once bounded_interval64_fused_hessian_pre_def]
  >> every_case_tac
  >> gvs []
QED

(* This accumulator is also structurally total.  Its source equation matches
 * a triple at the list head, so record the list-tail totality proof once for
 * every later caller instead of asking each translation to rediscover it. *)
val bounded_quadratic_abs_upper_acc_pre_def =
  cv_auto_trans_pre ""
    (compute_boundedTaylorCompleteTheory.bounded_quadratic_abs_upper_acc_def
      |> measure_args [0]);

Theorem bounded_quadratic_abs_upper_acc_pre[cv_pre]:
  !weights entries accumulator.
    bounded_quadratic_abs_upper_acc_pre weights entries accumulator
Proof
  Induct_on `weights`
  >- (rpt gen_tac
      >> Cases_on `entries`
      >> rw [Once bounded_quadratic_abs_upper_acc_pre_def])
  >> rpt gen_tac
  >> PairCases_on `h`
  >> Cases_on `entries`
  >> rw [Once bounded_quadratic_abs_upper_acc_pre_def]
  >> every_case_tac
  >> gvs []
QED

val bounded_taylor_gradient_rows_complete_pre_def =
  cv_auto_trans_pre ""
    (compute_boundedTaylorGradientTheory.bounded_taylor_gradient_rows_complete_def
      |> measure_args [1]);

Theorem bounded_taylor_gradient_rows_complete_pre[cv_pre]:
  !center_gradient hessian_rows.
    bounded_taylor_gradient_rows_complete_pre radii
      center_gradient hessian_rows
Proof
  Induct_on `center_gradient`
  >- (rpt gen_tac
      >> Cases_on `hessian_rows`
      >> rw [Once bounded_taylor_gradient_rows_complete_pre_def])
  >> rpt gen_tac
  >> Cases_on `hessian_rows`
  >> rw [Once bounded_taylor_gradient_rows_complete_pre_def]
  >> every_case_tac
  >> gvs []
QED

val bounded_interval64_fused_scale_add_pre_def =
  cv_auto_trans_pre ""
    (compute_boundedTaylorMulTheory.bounded_interval64_fused_scale_add_def
      |> measure_args [1]);

Theorem bounded_interval64_fused_scale_add_pre[cv_pre]:
  !left_values right_values.
    bounded_interval64_fused_scale_add_pre left_scale left_values
      right_scale right_values
Proof
  Induct_on `left_values`
  >- (rpt gen_tac
      >> Cases_on `right_values`
      >> rw [Once bounded_interval64_fused_scale_add_pre_def])
  >> rpt gen_tac
  >> Cases_on `right_values`
  >> rw [Once bounded_interval64_fused_scale_add_pre_def]
  >> every_case_tac
  >> gvs []
QED

val bounded_interval64_symmetric_product_pairs_row_pre_def =
  cv_auto_trans_pre ""
    (compute_boundedTaylorMulTheory.bounded_interval64_symmetric_product_pairs_row_def
      |> measure_args [2]);

Theorem bounded_interval64_symmetric_product_pairs_row_pre[cv_pre]:
  !left_values right_values.
    bounded_interval64_symmetric_product_pairs_row_pre
      fixed_left fixed_right left_values right_values
Proof
  Induct_on `left_values`
  >- (rpt gen_tac
      >> Cases_on `right_values`
      >> rw [Once
        bounded_interval64_symmetric_product_pairs_row_pre_def])
  >> rpt gen_tac
  >> Cases_on `right_values`
  >> rw [Once
    bounded_interval64_symmetric_product_pairs_row_pre_def]
  >> every_case_tac
  >> gvs []
QED

val bounded_delta64_product_hessian_pre_def =
  cv_auto_trans_pre ""
    (compute_boundedDeltaTaylorTheory.bounded_delta64_product_hessian_def
      |> measure_args [3]);

Theorem bounded_delta64_product_hessian_pre[cv_pre]:
  !indices entries.
    bounded_delta64_product_hessian_pre coordinate box_coordinate
      delta_gradient indices entries
Proof
  Induct_on `indices`
  >- (rpt gen_tac
      >> Cases_on `entries`
      >> rw [Once bounded_delta64_product_hessian_pre_def])
  >> rpt gen_tac
  >> PairCases_on `h`
  >> Cases_on `entries`
  >> rw [Once bounded_delta64_product_hessian_pre_def]
  >> every_case_tac
  >> gvs []
QED

val bounded_interval64_list_add_pre_def =
  cv_auto_trans_pre ""
    (compute_boundedIntervalListTheory.bounded_interval64_list_add_def
      |> measure_args [0]);

Theorem bounded_interval64_list_add_pre[cv_pre]:
  !left right. bounded_interval64_list_add_pre left right
Proof
  Induct_on `left`
  >- (rpt gen_tac
      >> Cases_on `right`
      >> rw [Once bounded_interval64_list_add_pre_def])
  >> rpt gen_tac
  >> Cases_on `right`
  >> rw [Once bounded_interval64_list_add_pre_def]
  >> every_case_tac
  >> gvs []
QED

val bounded_interval64_list_pairwise_mul_pre_def =
  cv_auto_trans_pre ""
    (compute_boundedIntervalListTheory.bounded_interval64_list_pairwise_mul_def
      |> measure_args [0]);

Theorem bounded_interval64_list_pairwise_mul_pre[cv_pre]:
  !left right. bounded_interval64_list_pairwise_mul_pre left right
Proof
  Induct_on `left`
  >- (rpt gen_tac
      >> Cases_on `right`
      >> rw [Once bounded_interval64_list_pairwise_mul_pre_def])
  >> rpt gen_tac
  >> Cases_on `right`
  >> rw [Once bounded_interval64_list_pairwise_mul_pre_def]
  >> every_case_tac
  >> gvs []
QED

val bounded_interval64_symmetric_product_pairs_pre_def =
  cv_auto_trans_pre ""
    (compute_boundedTaylorMulTheory.bounded_interval64_symmetric_product_pairs_def
      |> measure_args [0]);

Theorem bounded_interval64_symmetric_product_pairs_pre[cv_pre]:
  !left right.
    bounded_interval64_symmetric_product_pairs_pre left right
Proof
  Induct_on `left`
  >- (rpt gen_tac
      >> Cases_on `right`
      >> rw [Once bounded_interval64_symmetric_product_pairs_pre_def])
  >> rpt gen_tac
  >> Cases_on `right`
  >> rw [Once bounded_interval64_symmetric_product_pairs_pre_def]
  >> every_case_tac
  >> gvs []
QED

val _ = cv_auto_trans
  compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_def;

val _ = export_theory ();
