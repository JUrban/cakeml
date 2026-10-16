(*****************************************************************************
 * Authenticated streaming boundary for the strengthened decimal batch.
 *
 * Every accepted packet consumes exactly one source job and one historical
 * root record.  In addition to numerical acceptance, the packet box covers
 * the source box, its six coordinate-root intervals are the canonical
 * decimal conversion of the source job's first six roots, and its four
 * historical roots decode exactly to the supplied root record.  Missing,
 * extra, malformed, reordered, or independently substituted inputs fail
 * closed.
 *****************************************************************************)
Theory compute_boundedCase10173PackedDecimalAuthenticated
Ancestors
  compute_boundedCase10173PackedDecimalJobBinding
  compute_boundedCase10173DecimalInputBinding
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
           bounded_case10173_decimal_packet_exact_auxiliary_binding
             packet object_job root_record
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
    bounded_case10173_decimal_packet_exact_auxiliary_binding
      packet object_job root_record /\
    bounded_packed_chars_case10173_decimal_authenticated_packets
      remaining rest object_jobs root_records (SUC current_count) =
        SOME result
Proof
  rw [bounded_packed_chars_case10173_decimal_authenticated_packets_def]
  >> every_case_tac
  >> gvs []
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
