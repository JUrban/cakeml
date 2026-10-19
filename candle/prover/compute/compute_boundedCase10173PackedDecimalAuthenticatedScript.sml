(*****************************************************************************
 * Authenticated streaming boundary for the strengthened decimal batch.
 *
 * Every accepted packet consumes exactly one source job and one historical
 * root record.  In addition to numerical acceptance, the packet box covers
 * the source box, its center is the canonical midpoint environment of that
 * source box, its six coordinate-root intervals are the canonical decimal
 * conversion of the source job's first six roots, and its four historical
 * roots decode exactly to the supplied root record.  Missing, extra,
 * malformed, reordered, or independently substituted inputs fail closed.
 *****************************************************************************)
Theory compute_boundedCase10173PackedDecimalAuthenticated
Ancestors
  compute_boundedCase10173PackedDecimalJobBinding
  compute_registeredCase10173RadiusBinding
  compute_boundedCase10173SourceSqrtCertificate
Libs
  bossLib preamble

Definition bounded_packed_chars_case10173_decimal_authenticated_packets_def:
  bounded_packed_chars_case10173_decimal_authenticated_packets
      0 bytes (Num n) (Num m) count =
    (if bytes = [] /\ n = 0 /\ m = 0 then SOME count else NONE) /\
  bounded_packed_chars_case10173_decimal_authenticated_packets
      0 bytes (Num n) (Pair root_record root_records) count = NONE /\
  bounded_packed_chars_case10173_decimal_authenticated_packets
      0 bytes (Pair object_job object_jobs) root_records count = NONE /\
  bounded_packed_chars_case10173_decimal_authenticated_packets
      (SUC remaining) bytes (Num n) root_records count = NONE /\
  bounded_packed_chars_case10173_decimal_authenticated_packets
      (SUC remaining) bytes (Pair object_job object_jobs) (Num n) count =
    NONE /\
  bounded_packed_chars_case10173_decimal_authenticated_packets
      (SUC remaining) bytes (Pair object_job object_jobs)
      (Pair root_record root_records) count =
    case bounded_packed_chars_case10173_packet bytes of
    | NONE => NONE
    | SOME (packet,rest) =>
        if bounded_packed_chars_case10173_decimal_packet_ok packet /\
           bounded_case10173_decimal_packet_box_binds_object_job
             packet object_job /\
           bounded_case10173_decimal_packet_root_inputs_exact
             packet object_job root_record /\
           bounded_case10173_source_coordinate_sqrts_exact object_job /\
           bounded_case10173_decimal_packet_source_radii_exact
             packet object_job
        then bounded_packed_chars_case10173_decimal_authenticated_packets
          remaining rest object_jobs root_records (SUC count)
        else NONE
End

Definition bounded_packed_chars_case10173_decimal_authenticated_full_check_def:
  bounded_packed_chars_case10173_decimal_authenticated_full_check bytes
      encoded_jobs encoded_roots <=>
    case bounded_packed_chars_case10173_full_header bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_case10173_decimal_authenticated_packets
          4173 rest encoded_jobs encoded_roots 0 = SOME 4173
End

Definition bounded_case10173_object_root_records_length_def:
  bounded_case10173_object_root_records_length (Num 0 : cv) = SOME 0 /\
  bounded_case10173_object_root_records_length (Num (SUC n)) = NONE /\
  bounded_case10173_object_root_records_length
      (Pair root_record root_records) =
    case bounded_case10173_object_root_records_length root_records of
    | NONE => NONE
    | SOME root_count => SOME (SUC root_count)
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Theorem bounded_packed_chars_case10173_decimal_authenticated_numerical_sound:
  !remaining bytes encoded_jobs encoded_roots count result.
    bounded_packed_chars_case10173_decimal_authenticated_packets
      remaining bytes encoded_jobs encoded_roots count = SOME result ==>
    bounded_packed_chars_case10173_decimal_job_packets
      remaining bytes encoded_jobs count = SOME result
Proof
  Induct
  >- (Cases_on `encoded_jobs`
      >> Cases_on `encoded_roots`
      >> rw
           [bounded_packed_chars_case10173_decimal_authenticated_packets_def,
            compute_boundedCase10173PackedDecimalJobBindingTheory.bounded_packed_chars_case10173_decimal_job_packets_def]
      >> gvs [])
  >> Cases_on `encoded_jobs`
  >> Cases_on `encoded_roots`
  >> rw
       [bounded_packed_chars_case10173_decimal_authenticated_packets_def,
        compute_boundedCase10173PackedDecimalJobBindingTheory.bounded_packed_chars_case10173_decimal_job_packets_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> gvs []
QED

Theorem bounded_packed_chars_case10173_decimal_authenticated_lengths:
  !remaining bytes encoded_jobs encoded_roots count result.
    bounded_packed_chars_case10173_decimal_authenticated_packets
      remaining bytes encoded_jobs encoded_roots count = SOME result ==>
    bounded_case10173_object_jobs_length encoded_jobs = SOME remaining /\
    bounded_case10173_object_root_records_length encoded_roots =
      SOME remaining
Proof
  Induct
  >- (Cases_on `encoded_jobs`
      >> Cases_on `encoded_roots`
      >> rw
           [bounded_packed_chars_case10173_decimal_authenticated_packets_def,
            compute_boundedCase10173PackedJobBindingTheory.bounded_case10173_object_jobs_length_def,
            bounded_case10173_object_root_records_length_def]
      >> gvs [])
  >> Cases_on `encoded_jobs`
  >> Cases_on `encoded_roots`
  >> rw
       [bounded_packed_chars_case10173_decimal_authenticated_packets_def,
        compute_boundedCase10173PackedJobBindingTheory.bounded_case10173_object_jobs_length_def,
        bounded_case10173_object_root_records_length_def]
  >> every_case_tac
  >> gvs
       [compute_boundedCase10173HistoricalCellDecimalBoundaryTheory.bounded_case10173_decimal_packet_box_binds_object_job_def]
  >> res_tac
  >> gvs []
QED

Theorem bounded_packed_chars_case10173_decimal_authenticated_step:
  bounded_packed_chars_case10173_decimal_authenticated_packets
      (SUC remaining) bytes (Pair object_job object_jobs)
      (Pair root_record root_records) current_count = SOME result ==>
  ?packet rest.
    bounded_packed_chars_case10173_packet bytes = SOME (packet,rest) /\
    bounded_packed_chars_case10173_decimal_packet_ok packet /\
    bounded_case10173_decimal_packet_box_binds_object_job
      packet object_job /\
    bounded_case10173_decimal_packet_root_inputs_exact
      packet object_job root_record /\
    bounded_case10173_source_coordinate_sqrts_exact object_job /\
    bounded_case10173_decimal_packet_source_radii_exact
      packet object_job /\
    bounded_packed_chars_case10173_decimal_authenticated_packets
      remaining rest object_jobs root_records (SUC current_count) =
        SOME result
Proof
  rw [bounded_packed_chars_case10173_decimal_authenticated_packets_def]
  >> every_case_tac
  >> gvs []
QED

(* This is the complete per-job handoff exposed to the eventual fast
 * evaluator refinement.  It does not merely align list positions: the
 * numerical verdict has an exact object result, the source box is covered,
 * the six coordinate roots are the canonical source conversions, and the
 * four historical roots are byte-for-value identical to the authenticated
 * root record. *)
Theorem bounded_packed_chars_case10173_decimal_authenticated_head_object_contract:
  bounded_packed_chars_case10173_decimal_authenticated_packets
      (SUC remaining) bytes (Pair object_job object_jobs)
      (Pair root_record root_records) current_count = SOME result ==>
  ?packet rest source_boxes center_boxes center_roots box_roots
     center_extra box_extra box_sqrt_data center_sqrt_data.
    bounded_packed_chars_case10173_packet bytes = SOME (packet,rest) /\
    bounded_packed_chars_case10173_decimal_packet_object_ok packet /\
    bounded_case10173_object_job_boxes object_job = SOME source_boxes /\
    bounded_interval64_list_covers_object_q_decimal
      (bounded_case10173_packet_box_environment packet) source_boxes /\
    bounded_object_positive_q_interval64_decimal_list source_boxes =
      SOME (bounded_case10173_packet_box_environment packet) /\
    registered_case10173_q_center_environment_positive source_boxes =
      SOME center_boxes /\
    bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME (bounded_case10173_packet_center_environment packet) /\
    bounded_case10173_source_radii64_positive_q source_boxes =
      SOME (bounded_case10173_packet_radii packet) /\
    object_job = Pair box_sqrt_data (Pair center_sqrt_data source_boxes) /\
    bounded_case10173_source_coordinate_sqrts_exact object_job /\
    bounded_case10173_decimal_packet_sqrt_roots packet =
      (center_roots,box_roots) /\
    bounded_object_positive_q_interval64_decimal_list center_sqrt_data =
      SOME (center_roots ++ [center_extra]) /\
    bounded_object_positive_q_interval64_decimal_list box_sqrt_data =
      SOME (box_roots ++ [box_extra]) /\
    bounded_interval64_object_cv_list
      (bounded_case10173_packet_root_intervals packet) = root_record /\
    bounded_packed_chars_case10173_decimal_authenticated_packets
      remaining rest object_jobs root_records (SUC current_count) =
        SOME result
Proof
  strip_tac
  >> drule bounded_packed_chars_case10173_decimal_authenticated_step
  >> strip_tac
  >> drule
       compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_ok_object_sound
  >> strip_tac
  >> fs
       [compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_root_inputs_exact_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_input_binding_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_auxiliary_binding_def]
  >> drule
       compute_boundedCase10173HistoricalCellDecimalBoundaryTheory.bounded_case10173_decimal_packet_box_binds_object_job_components
  >> strip_tac
  >> drule
       compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_box_exact_components
  >> strip_tac
  >> drule
       compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_sqrt_roots_binding_components
  >> strip_tac
  >> drule
       compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_root_binding_exact_cv
  >> strip_tac
  >> drule
       compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_center_exact_components
  >> strip_tac
  >> drule
       compute_registeredCase10173RadiusBindingTheory.bounded_case10173_decimal_packet_source_radii_exact_components
  >> strip_tac
  >> gvs
       [compute_boundedCase10173JobBindingTheory.bounded_case10173_object_job_boxes_def]
  >> metis_tac []
QED

Theorem bounded_packed_chars_case10173_decimal_authenticated_full_numerical_sound:
  bounded_packed_chars_case10173_decimal_authenticated_full_check
      bytes encoded_jobs encoded_roots ==>
  bounded_packed_chars_case10173_decimal_full_job_check bytes encoded_jobs
Proof
  rw
    [bounded_packed_chars_case10173_decimal_authenticated_full_check_def,
     compute_boundedCase10173PackedDecimalJobBindingTheory.bounded_packed_chars_case10173_decimal_full_job_check_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       bounded_packed_chars_case10173_decimal_authenticated_numerical_sound
QED

Theorem bounded_packed_chars_case10173_decimal_authenticated_full_object_sound:
  bounded_packed_chars_case10173_decimal_authenticated_full_check
      bytes encoded_jobs encoded_roots ==>
  bounded_packed_chars_case10173_decimal_full_object_contract bytes
Proof
  strip_tac
  >> imp_res_tac
       bounded_packed_chars_case10173_decimal_authenticated_full_numerical_sound
  >> metis_tac
       [compute_boundedCase10173PackedDecimalJobBindingTheory.bounded_packed_chars_case10173_decimal_full_job_check_object_sound]
QED

Theorem bounded_packed_chars_case10173_decimal_authenticated_rejects_missing_jobs:
  bounded_packed_chars_case10173_decimal_authenticated_packets
    (SUC remaining) bytes (Num n) encoded_roots current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_decimal_authenticated_packets_def]
QED

Theorem bounded_packed_chars_case10173_decimal_authenticated_rejects_missing_roots:
  bounded_packed_chars_case10173_decimal_authenticated_packets
    (SUC remaining) bytes (Pair object_job object_jobs) (Num n)
    current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_decimal_authenticated_packets_def]
QED

Theorem bounded_packed_chars_case10173_decimal_authenticated_rejects_extra_jobs:
  bounded_packed_chars_case10173_decimal_authenticated_packets 0 []
    (Pair object_job object_jobs) encoded_roots current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_decimal_authenticated_packets_def]
QED

Theorem bounded_packed_chars_case10173_decimal_authenticated_rejects_extra_roots:
  bounded_packed_chars_case10173_decimal_authenticated_packets 0 []
    (Num 0) (Pair root_record root_records) current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_decimal_authenticated_packets_def]
QED

Theorem bounded_packed_chars_case10173_decimal_authenticated_rejects_trailing_bytes:
  bytes <> [] ==>
  bounded_packed_chars_case10173_decimal_authenticated_packets 0 bytes
    (Num 0) (Num 0) current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_decimal_authenticated_packets_def]
QED

Theorem bounded_packed_chars_case10173_decimal_authenticated_rejects_noncanonical_job_nil:
  n <> 0 ==>
  bounded_packed_chars_case10173_decimal_authenticated_packets 0 []
    (Num n) (Num 0) current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_decimal_authenticated_packets_def]
QED

Theorem bounded_packed_chars_case10173_decimal_authenticated_rejects_noncanonical_root_nil:
  n <> 0 ==>
  bounded_packed_chars_case10173_decimal_authenticated_packets 0 []
    (Num 0) (Num n) current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_decimal_authenticated_packets_def]
QED

val _ = export_theory ();
