(*****************************************************************************
 * Streaming source-job binding for the strengthened decimal batch.
 *
 * One authenticated object job is consumed for each checked decimal packet.
 * The decimal packet box must enclose the exact rational source box decoded
 * from that job; missing, extra, malformed, or reordered jobs fail closed.
 *****************************************************************************)
Theory compute_boundedCase10173PackedDecimalJobBinding
Ancestors
  compute_boundedCase10173HistoricalCellDecimalBoundary
  compute_boundedCase10173PackedDecimalBatch
  compute_boundedCase10173PackedJobBinding
Libs
  bossLib preamble

Definition bounded_packed_chars_case10173_decimal_job_packets_def:
  bounded_packed_chars_case10173_decimal_job_packets 0 bytes (Num n) count =
    (if bytes = [] /\ n = 0 then SOME count else NONE) /\
  bounded_packed_chars_case10173_decimal_job_packets 0 bytes
      (Pair job jobs) count = NONE /\
  bounded_packed_chars_case10173_decimal_job_packets (SUC remaining) bytes
      (Num n) count = NONE /\
  bounded_packed_chars_case10173_decimal_job_packets (SUC remaining) bytes
      (Pair object_job object_jobs) count =
    case bounded_packed_chars_case10173_packet bytes of
    | NONE => NONE
    | SOME (packet,rest) =>
        if bounded_packed_chars_case10173_decimal_packet_ok packet /\
           bounded_case10173_decimal_packet_box_binds_object_job
             packet object_job
        then bounded_packed_chars_case10173_decimal_job_packets
          remaining rest object_jobs (SUC count)
        else NONE
End

Definition bounded_packed_chars_case10173_decimal_full_job_check_def:
  bounded_packed_chars_case10173_decimal_full_job_check bytes encoded_jobs <=>
    case bounded_packed_chars_case10173_full_header bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_case10173_decimal_job_packets
          4173 rest encoded_jobs 0 = SOME 4173
End

Theorem bounded_packed_chars_case10173_decimal_job_packets_numerical_sound:
  !remaining bytes encoded_jobs count result.
    bounded_packed_chars_case10173_decimal_job_packets
      remaining bytes encoded_jobs count = SOME result ==>
    bounded_packed_chars_case10173_decimal_packets
      remaining bytes count = SOME result
Proof
  Induct
  >- (Cases_on `encoded_jobs`
      >> rw
           [bounded_packed_chars_case10173_decimal_job_packets_def,
            compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packets_def]
      >> gvs [])
  >> Cases_on `encoded_jobs`
  >> rw
       [bounded_packed_chars_case10173_decimal_job_packets_def,
        compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packets_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> gvs []
QED

Theorem bounded_packed_chars_case10173_decimal_job_packets_object_length:
  !remaining bytes encoded_jobs count result.
    bounded_packed_chars_case10173_decimal_job_packets
      remaining bytes encoded_jobs count = SOME result ==>
    bounded_case10173_object_jobs_length encoded_jobs = SOME remaining
Proof
  Induct
  >- (Cases_on `encoded_jobs`
      >> rw
           [bounded_packed_chars_case10173_decimal_job_packets_def,
            compute_boundedCase10173PackedJobBindingTheory.bounded_case10173_object_jobs_length_def]
      >> gvs [])
  >> Cases_on `encoded_jobs`
  >> rw
       [bounded_packed_chars_case10173_decimal_job_packets_def,
        compute_boundedCase10173PackedJobBindingTheory.bounded_case10173_object_jobs_length_def]
  >> every_case_tac
  >> gvs
       [compute_boundedCase10173HistoricalCellDecimalBoundaryTheory.bounded_case10173_decimal_packet_box_binds_object_job_def]
  >> res_tac
  >> gvs []
QED

Theorem bounded_packed_chars_case10173_decimal_job_packets_step:
  bounded_packed_chars_case10173_decimal_job_packets (SUC remaining) bytes
      (Pair object_job object_jobs) current_count = SOME result ==>
  ?packet rest.
    bounded_packed_chars_case10173_packet bytes = SOME (packet,rest) /\
    bounded_packed_chars_case10173_decimal_packet_ok packet /\
    bounded_case10173_decimal_packet_box_binds_object_job
      packet object_job /\
    bounded_packed_chars_case10173_decimal_job_packets remaining rest
      object_jobs (SUC current_count) = SOME result
Proof
  rw [bounded_packed_chars_case10173_decimal_job_packets_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_packed_chars_case10173_decimal_full_job_check_numerical_sound:
  bounded_packed_chars_case10173_decimal_full_job_check bytes encoded_jobs ==>
  bounded_packed_chars_case10173_decimal_full_check bytes
Proof
  rw
    [bounded_packed_chars_case10173_decimal_full_job_check_def,
     compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_full_check_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       bounded_packed_chars_case10173_decimal_job_packets_numerical_sound
QED

Theorem bounded_packed_chars_case10173_decimal_full_job_check_object_sound:
  bounded_packed_chars_case10173_decimal_full_job_check bytes encoded_jobs ==>
  bounded_packed_chars_case10173_decimal_full_object_contract bytes
Proof
  strip_tac
  >> imp_res_tac
       bounded_packed_chars_case10173_decimal_full_job_check_numerical_sound
  >> metis_tac
       [compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_full_check_object_sound]
QED

Theorem bounded_packed_chars_case10173_decimal_job_packets_rejects_missing_jobs:
  bounded_packed_chars_case10173_decimal_job_packets (SUC remaining) bytes
    (Num n) current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_decimal_job_packets_def]
QED

Theorem bounded_packed_chars_case10173_decimal_job_packets_rejects_extra_jobs:
  bounded_packed_chars_case10173_decimal_job_packets 0 []
    (Pair object_job object_jobs) current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_decimal_job_packets_def]
QED

Theorem bounded_packed_chars_case10173_decimal_job_packets_rejects_trailing_bytes:
  bytes <> [] ==>
  bounded_packed_chars_case10173_decimal_job_packets 0 bytes (Num 0)
    current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_decimal_job_packets_def]
QED

val _ = export_theory ();
