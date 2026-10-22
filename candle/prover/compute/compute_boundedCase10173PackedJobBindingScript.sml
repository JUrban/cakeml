(*****************************************************************************
 * Streaming packet/object-job box binding for a complete case-10173 batch.
 *
 * The byte parser and complete word checker remain the measured production
 * path.  In parallel, exactly one structurally shaped object job must be
 * consumed for every accepted packet, and that packet's box must enclose the
 * job's exact rational source box.  Missing, extra, malformed, or
 * positionally nonmatching job lists therefore fail closed at this boundary.
 *****************************************************************************)
Theory compute_boundedCase10173PackedJobBinding
Ancestors
  compute_boundedCase10173JobBinding
  compute_boundedCase10173PackedBatch
Libs
  bossLib preamble

Definition bounded_packed_chars_case10173_job_packets_def:
  bounded_packed_chars_case10173_job_packets 0 bytes (Num n) count =
    (if bytes = [] /\ n = 0 then SOME count else NONE) /\
  bounded_packed_chars_case10173_job_packets 0 bytes (Pair job jobs) count =
    NONE /\
  bounded_packed_chars_case10173_job_packets (SUC remaining) bytes
      (Num n) count = NONE /\
  bounded_packed_chars_case10173_job_packets (SUC remaining) bytes
      (Pair object_job object_jobs) count =
    case bounded_packed_chars_case10173_packet bytes of
    | NONE => NONE
    | SOME (packet,rest) =>
        if bounded_packed_chars_case10173_packet_ok packet /\
           bounded_case10173_packet_box_binds_object_job packet object_job
        then bounded_packed_chars_case10173_job_packets remaining rest
          object_jobs (SUC count)
        else NONE
End

Definition bounded_packed_chars_case10173_full_job_check_def:
  bounded_packed_chars_case10173_full_job_check bytes encoded_jobs <=>
    case bounded_packed_chars_case10173_full_header bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_case10173_job_packets
          4173 rest encoded_jobs 0 = SOME 4173
End

Definition bounded_case10173_object_jobs_length_def:
  bounded_case10173_object_jobs_length (Num 0 : cv) = SOME 0 /\
  bounded_case10173_object_jobs_length (Num (SUC n)) = NONE /\
  bounded_case10173_object_jobs_length (Pair object_job object_jobs) =
    case bounded_case10173_object_job_boxes object_job of
    | NONE => NONE
    | SOME source_boxes =>
        case bounded_case10173_object_jobs_length object_jobs of
        | NONE => NONE
        | SOME job_count => SOME (SUC job_count)
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Theorem bounded_packed_chars_case10173_job_packets_numerical_sound:
  !remaining bytes encoded_jobs count result.
    bounded_packed_chars_case10173_job_packets
      remaining bytes encoded_jobs count = SOME result ==>
    bounded_packed_chars_case10173_packets
      remaining bytes count = SOME result
Proof
  Induct
  >- (Cases_on `encoded_jobs`
      >> rw [bounded_packed_chars_case10173_job_packets_def,
             bounded_packed_chars_case10173_packets_def]
      >> gvs [])
  >> Cases_on `encoded_jobs`
  >> rw [bounded_packed_chars_case10173_job_packets_def,
         bounded_packed_chars_case10173_packets_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> gvs []
QED

Theorem bounded_packed_chars_case10173_job_packets_object_length:
  !remaining bytes encoded_jobs count result.
    bounded_packed_chars_case10173_job_packets
      remaining bytes encoded_jobs count = SOME result ==>
    bounded_case10173_object_jobs_length encoded_jobs = SOME remaining
Proof
  Induct
  >- (Cases_on `encoded_jobs`
      >> rw [bounded_packed_chars_case10173_job_packets_def,
             bounded_case10173_object_jobs_length_def]
      >> gvs [])
  >> Cases_on `encoded_jobs`
  >> rw [bounded_packed_chars_case10173_job_packets_def,
         bounded_case10173_object_jobs_length_def]
  >> every_case_tac
  >> gvs [bounded_case10173_packet_box_binds_object_job_def]
  >> res_tac
  >> gvs []
QED

Theorem bounded_packed_chars_case10173_job_packets_step:
  bounded_packed_chars_case10173_job_packets (SUC remaining) bytes
      (Pair object_job object_jobs) current_count = SOME result ==>
  ?packet rest.
    bounded_packed_chars_case10173_packet bytes = SOME (packet,rest) /\
    bounded_packed_chars_case10173_packet_ok packet /\
    bounded_case10173_packet_box_binds_object_job packet object_job /\
    bounded_packed_chars_case10173_job_packets remaining rest
      object_jobs (SUC current_count) = SOME result
Proof
  rw [bounded_packed_chars_case10173_job_packets_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_packed_chars_case10173_full_job_check_numerical_sound:
  bounded_packed_chars_case10173_full_job_check bytes encoded_jobs ==>
  bounded_packed_chars_case10173_full_check bytes
Proof
  rw [bounded_packed_chars_case10173_full_job_check_def,
      bounded_packed_chars_case10173_full_check_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       bounded_packed_chars_case10173_job_packets_numerical_sound
QED

Theorem bounded_packed_chars_case10173_job_packets_rejects_missing_jobs:
  bounded_packed_chars_case10173_job_packets (SUC remaining) bytes
    (Num n) current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_job_packets_def]
QED

Theorem bounded_packed_chars_case10173_job_packets_rejects_extra_jobs:
  bounded_packed_chars_case10173_job_packets 0 []
    (Pair object_job object_jobs) current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_job_packets_def]
QED

Theorem bounded_packed_chars_case10173_job_packets_rejects_trailing_bytes:
  bytes <> [] ==>
  bounded_packed_chars_case10173_job_packets 0 bytes (Num 0)
    current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_job_packets_def]
QED

Theorem bounded_packed_chars_case10173_job_packets_rejects_noncanonical_nil:
  n <> 0 ==>
  bounded_packed_chars_case10173_job_packets 0 [] (Num n)
    current_count = NONE
Proof
  simp [bounded_packed_chars_case10173_job_packets_def]
QED

val _ = export_theory ();
