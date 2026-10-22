(*****************************************************************************
 * Proof-only semantic trace for the complete packed case-10173 batch.
 *
 * The measured runtime remains the single streaming packet/job checker.  This
 * relation merely exposes, by theorem, the source-box and recomputed-root
 * obligations already established at every successful step.  It deliberately
 * does not compare independently rounded historical root bytes and performs no
 * second numerical evaluation.
 *****************************************************************************)
Theory compute_boundedCase10173PackedSemanticBinding
Ancestors
  compute_boundedCase10173PackedJobBinding
  compute_boundedCase10173SemanticBoundary
Libs
  bossLib preamble

Definition bounded_case10173_job_packets_semantically_bound_def:
  bounded_case10173_job_packets_semantically_bound 0 bytes (Num n) =
    (bytes = [] /\ n = 0) /\
  bounded_case10173_job_packets_semantically_bound 0 bytes
      (Pair object_job object_jobs) = F /\
  bounded_case10173_job_packets_semantically_bound (SUC remaining) bytes
      (Num n) = F /\
  bounded_case10173_job_packets_semantically_bound (SUC remaining) bytes
      (Pair object_job object_jobs) =
    ?packet rest source_boxes.
      bounded_packed_chars_case10173_packet bytes = SOME (packet,rest) /\
      bounded_case10173_packet_accepts packet /\
      bounded_case10173_object_job_boxes object_job = SOME source_boxes /\
      bounded_interval64_list_covers_object_q
        (bounded_case10173_packet_box_environment packet) source_boxes /\
      bounded_case10173_packet_complete_numerical_contract packet /\
      bounded_case10173_job_packets_semantically_bound remaining rest
        object_jobs
End

Theorem bounded_packed_chars_case10173_job_packets_semantically_bound:
  !remaining bytes encoded_jobs current_count result.
    bounded_packed_chars_case10173_job_packets remaining bytes encoded_jobs
      current_count = SOME result ==>
    bounded_case10173_job_packets_semantically_bound remaining bytes
      encoded_jobs
Proof
  Induct_on `remaining`
  >- (Cases_on `encoded_jobs`
      >> simp [bounded_packed_chars_case10173_job_packets_def,
               bounded_case10173_job_packets_semantically_bound_def])
  >> rpt gen_tac
  >> Cases_on `encoded_jobs`
  >- simp [bounded_packed_chars_case10173_job_packets_def]
  >> strip_tac
  >> drule
       compute_boundedCase10173PackedJobBindingTheory.bounded_packed_chars_case10173_job_packets_step
  >> strip_tac
  >> fs [compute_boundedCase10173PackedBatchTheory.bounded_packed_chars_case10173_packet_ok_def]
  >> imp_res_tac
       compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_binds_object_job_components
  >> imp_res_tac
       compute_boundedCase10173SemanticBoundaryTheory.bounded_case10173_packet_accepts_complete_numerical_contract
  >> simp [bounded_case10173_job_packets_semantically_bound_def]
  >> metis_tac []
QED

Theorem bounded_packed_chars_case10173_full_job_check_semantically_bound:
  bounded_packed_chars_case10173_full_job_check bytes encoded_jobs ==>
  ?packet_bytes.
    bounded_packed_chars_case10173_full_header bytes = SOME packet_bytes /\
    bounded_case10173_job_packets_semantically_bound 4173 packet_bytes
      encoded_jobs
Proof
  rw [bounded_packed_chars_case10173_full_job_check_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       bounded_packed_chars_case10173_job_packets_semantically_bound
  >> metis_tac []
QED

Theorem bounded_case10173_job_packets_semantically_bound_step:
  bounded_case10173_job_packets_semantically_bound (SUC remaining) bytes
      (Pair object_job object_jobs) ==>
  ?packet rest source_boxes.
    bounded_packed_chars_case10173_packet bytes = SOME (packet,rest) /\
    bounded_case10173_packet_accepts packet /\
    bounded_case10173_object_job_boxes object_job = SOME source_boxes /\
    bounded_interval64_list_covers_object_q
      (bounded_case10173_packet_box_environment packet) source_boxes /\
    bounded_case10173_packet_complete_numerical_contract packet /\
    bounded_case10173_job_packets_semantically_bound remaining rest object_jobs
Proof
  simp [bounded_case10173_job_packets_semantically_bound_def]
QED

val _ = export_theory ();
