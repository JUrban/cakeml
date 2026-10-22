(* CakeML translation of the authenticated strengthened-decimal stream.
 * This is the runtime component intended for the proved compute_with fast
 * evaluator: packets, source jobs, and historical roots are checked in one
 * lockstep traversal. *)
Theory compute_boundedCase10173PackedDecimalAuthenticatedProg
Ancestors
  compute_boundedCase10173LiteralSourceDecimalProg
  compute_boundedCase10173PackedDecimalAuthenticatedExecutable
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends
  "compute_boundedCase10173LiteralSourceDecimalProg";

(* Source rational decoding and exact source-box coverage. *)
val _ = translate
  compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def;
val _ = translate
  (compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val _ = translate
  (compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_cv_tail_induction[local]:
  !P. (!v:cv. (!x y. v = Pair x y ==> P y) ==> P v) ==> !v. P v
Proof
  gen_tac
  >> strip_tac
  >> qspec_then `P` irule compute_execTheory.cv_induction
  >> rw []
  >> first_x_assum irule
  >> rw []
QED

val _ = translate_no_ind
  (compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_object_q_interval_list_ind_translation[local]:
  bounded_object_q_interval_list_ind
Proof
  once_rewrite_tac
    [fetch "-" "bounded_object_q_interval_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_object_q_interval_list_ind_translation
  |> update_precondition;

(* This mathematical view of a signed endpoint is not needed by the
 * numerical-checker lineage itself, but the authenticated source-coverage
 * predicate executes it. *)
val _ = translate
  compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def;

val _ = translate
  compute_boundedObjectDecimalQTheory.bounded_interval64_covers_object_q_ints_decimal_def;
val _ = translate bounded_interval64_list_covers_q_pairs_decimal_def;
val _ = translate
  bounded_interval64_list_covers_object_q_decimal_executable_def;

(* Exact decoding of the authenticated historical root records. *)
val _ = translate
  (compute_boundedObjectDecimalDecodeTheory.bounded_object_decimal_signed64_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  (compute_boundedObjectDecimalDecodeTheory.bounded_object_decimal_interval64_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val _ = translate_no_ind
  (compute_boundedObjectDecimalDecodeTheory.bounded_object_decimal_interval64_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_object_decimal_interval64_list_ind_translation[local]:
  bounded_object_decimal_interval64_list_ind
Proof
  once_rewrite_tac
    [fetch "-" "bounded_object_decimal_interval64_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_object_decimal_interval64_list_ind_translation
  |> update_precondition;

(* Canonical decimal conversion of source boxes and source sqrt records. *)
val _ = translate
  (compute_boundedObjectDecimalQTheory.bounded_decimal_natural_floor64_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  (compute_boundedObjectDecimalQTheory.bounded_decimal_natural_ceil64_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def;

Theorem bounded_object_positive_q_floor64_decimal_side_total[local]:
  !encoded. bounded_object_positive_q_floor64_decimal_side encoded
Proof
  rw [fetch "-" "bounded_object_positive_q_floor64_decimal_side_def",
      fetch "-" "bounded_decimal_natural_floor64_side_def"]
QED

val _ = bounded_object_positive_q_floor64_decimal_side_total
  |> update_precondition;

val _ = translate
  compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def;

Theorem bounded_object_positive_q_ceil64_decimal_side_total[local]:
  !encoded. bounded_object_positive_q_ceil64_decimal_side encoded
Proof
  rw [fetch "-" "bounded_object_positive_q_ceil64_decimal_side_def",
      fetch "-" "bounded_decimal_natural_ceil64_side_def"]
QED

val _ = bounded_object_positive_q_ceil64_decimal_side_total
  |> update_precondition;

val _ = translate
  (compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val _ = translate_no_ind
  (compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_object_positive_q_interval64_decimal_list_ind_translation[local]:
  bounded_object_positive_q_interval64_decimal_list_ind
Proof
  once_rewrite_tac
    [fetch "-" "bounded_object_positive_q_interval64_decimal_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_object_positive_q_interval64_decimal_list_ind_translation
  |> update_precondition;

(* Packet/source identity relations. *)
val _ = translate
  compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def;
val _ = translate
  compute_boundedCase10173JobBindingTheory.bounded_case10173_object_job_boxes_def;
val _ = translate
  compute_boundedCase10173HistoricalCellDecimalBoundaryTheory.bounded_case10173_decimal_packet_box_binds_object_job_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_sqrt64_center_intervals_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_sqrt64_box_intervals_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_sqrt_roots_def;
val _ = translate
  compute_boundedCase10173RootBindingTheory.bounded_case10173_packet_root_intervals_def;
val _ = translate bounded_interval64_list_prefix_one_extra_def;
val _ = translate
  bounded_case10173_decimal_packet_sqrt_roots_bind_object_job_executable_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_roots_bind_object_record_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_auxiliary_binding_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_box_exact_object_job_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_input_binding_def;
val _ = translate
  compute_registeredCase10173CenterEnvironmentObjectTheory.registered_case10173_q_midpoint_positive_cv_def;
val _ = translate
  compute_registeredCase10173CenterEnvironmentObjectTheory.registered_case10173_q_center_environment_positive_def;
val _ = translate
  compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def;
val _ = translate
  compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_center_exact_object_job_def;
val _ = translate
  compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_root_inputs_exact_def;

(* Exact source-rational square-root certificates.  These checks complement
 * the rounded decimal certificates and are consumed by source refinement. *)
val _ = translate
  compute_boundedCase10173SourceSqrtCertificateTheory.bounded_case10173_source_q_sqrt_certificate_exact_def;
val _ = translate
  compute_boundedCase10173SourceSqrtCertificateTheory.bounded_case10173_source_q_sqrt_prefix_exact_def;
val _ = translate
  compute_boundedCase10173SourceSqrtCertificateTheory.bounded_case10173_source_coordinate_sqrts_exact_def;

(* Exact identity of the authenticated source roots and the typed decimal
 * roots consumed by the specialized derivative checker. *)
val _ = translate
  compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_positive_endpoint64_q_cv_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_positive_q_endpoint64_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_positive_q_interval64_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_sqrt_decimal_prefix_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_coordinate_sqrt_decimals_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_sqrt_dd_floor64_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_sqrt_dd_ceil64_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_sqrt_dd_interval64_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_sqrt_dd_prefix_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_coordinate_sqrt_dd_decimals_exact_def;

(* Exact source-radius reconstruction from the authenticated rational box. *)
val _ = translate
  compute_registeredCase10173RadiusBindingTheory.bounded_case10173_packet_radii_def;
val _ = translate
  compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def;

Theorem bounded_case10173_source_radius64_positive_q_side_total[local]:
  !encoded. bounded_case10173_source_radius64_positive_q_side encoded
Proof
  rw [fetch "-" "bounded_case10173_source_radius64_positive_q_side_def",
      fetch "-" "bounded_decimal_natural_ceil64_side_def"]
QED

val _ = bounded_case10173_source_radius64_positive_q_side_total
  |> update_precondition;

val _ = translate_no_ind
  compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radii64_positive_q_def;

Theorem bounded_case10173_source_radii64_positive_q_ind_translation[local]:
  bounded_case10173_source_radii64_positive_q_ind
Proof
  once_rewrite_tac
    [fetch "-" "bounded_case10173_source_radii64_positive_q_ind_def"]
  >> gen_tac
  >> strip_tac
  >> qspec_then `P` irule compute_execTheory.cv_induction
  >> rw []
  >> first_x_assum irule
  >> rw []
QED

val _ = bounded_case10173_source_radii64_positive_q_ind_translation
  |> update_precondition;

val _ = translate
  compute_registeredCase10173RadiusBindingTheory.bounded_case10173_decimal_packet_source_radii_exact_def;

(* Authenticate the operands used by the literal source program.  The source
 * Taylor-completes each coordinate before sqrt, so this executable contract
 * deliberately recomputes that completed value_bound rather than checking
 * the original source-box coordinate. *)
val _ = translate
  compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_positive_interval64_q_cv_def;
val _ = translate
  compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def;
val _ = translate
  compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_source_actual_sqrt_contract_def;

val _ = translate
  compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_packets_def;
val _ = translate
  compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_full_check_def;

val _ = export_theory ();
