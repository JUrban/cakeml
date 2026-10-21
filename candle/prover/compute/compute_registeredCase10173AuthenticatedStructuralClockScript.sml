(*****************************************************************************
 * Exact structural clock for an authenticated complete case-10173 stream.
 *
 * Authentication fixes every source job to three zero-terminated interval
 * lists of lengths 7, 7, and 6.  Consequently the structural canonicalizer
 * cost is 26 units per job plus the terminal unit, independently of every
 * encoded rational's numeric magnitude.
 *****************************************************************************)
Theory compute_registeredCase10173AuthenticatedStructuralClock
Ancestors
  compute_registeredCase10173CanonicalStructuralEval
  compute_registeredCase10173ProgramPreparationPacketEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_structural_list_length_eq_cv_list_length:
  !encoded.
    registered_case10173_structural_list_length encoded =
    registered_case10173_cv_list_length encoded
Proof
  Induct
  >> simp
       [compute_registeredCase10173CanonicalStructuralEvalTheory.registered_case10173_structural_list_length_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
QED

Theorem bounded_packed_chars_case10173_packet_box_environment_length:
  bounded_packed_chars_case10173_packet bytes = SOME (packet,rest) ==>
  LENGTH (bounded_case10173_packet_box_environment packet) = 6
Proof
  rw
    [compute_boundedCase10173PackedBatchTheory.bounded_packed_chars_case10173_packet_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedCase10173PackedBatchTheory.bounded_packed_chars_interval64_list_length
  >> gvs
       [compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def]
QED

Theorem bounded_packed_chars_case10173_packet_object_ok_sqrt_root_lengths:
  bounded_packed_chars_case10173_decimal_packet_object_ok packet ==>
  LENGTH (FST (bounded_case10173_decimal_packet_sqrt_roots packet)) = 6 /\
  LENGTH (SND (bounded_case10173_decimal_packet_sqrt_roots packet)) = 6
Proof
  Cases_on `packet`
  >> simp
       [compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_object_ok_def]
  >> strip_tac
  >> imp_res_tac
       compute_registeredCase10173ProgramPreparationPacketEvalTheory.registered_case10173_object_checked_cell_sqrt_certificate_length
  >> simp
       [compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_sqrt_roots_def,
        compute_registeredCase10173ProgramPreparationPacketEvalTheory.registered_case10173_sqrt64_center_intervals_length,
        compute_registeredCase10173ProgramPreparationPacketEvalTheory.registered_case10173_sqrt64_box_intervals_length]
QED

Theorem registered_case10173_authenticated_packets_structural_jobs_clock:
  !remaining bytes encoded_jobs encoded_roots current_count result.
    bounded_packed_chars_case10173_decimal_authenticated_packets
      remaining bytes encoded_jobs encoded_roots current_count = SOME result ==>
    registered_case10173_structural_jobs_clock encoded_jobs =
      26 * remaining + 1
Proof
  Induct_on `remaining`
  >- (rpt gen_tac
      >> Cases_on `encoded_jobs`
      >> Cases_on `encoded_roots`
      >> rw
           [compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_packets_def,
            compute_registeredCase10173CanonicalStructuralEvalTheory.registered_case10173_structural_jobs_clock_def]
      >> gvs [])
  >> rpt gen_tac
  >> Cases_on `encoded_jobs`
  >- simp
       [compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_packets_def]
  >> Cases_on `encoded_roots`
  >- simp
       [compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_packets_def]
  >> strip_tac
  >> drule
       compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_head_object_contract
  >> strip_tac
  >> imp_res_tac
       bounded_packed_chars_case10173_packet_object_ok_sqrt_root_lengths
  >> imp_res_tac
       compute_registeredCase10173ProgramPreparationPacketEvalTheory.registered_case10173_positive_q_interval_list_length
  >> imp_res_tac
       bounded_packed_chars_case10173_packet_box_environment_length
  >> qpat_x_assum
       `!bytes encoded_jobs encoded_roots current_count result. _`
       (qspecl_then
         [`rest`,`c0`,`c0'`,`SUC current_count`,`result`] mp_tac)
  >> simp []
  >> strip_tac
  >> gvs
       [compute_registeredCase10173CanonicalStructuralEvalTheory.registered_case10173_structural_jobs_clock_def,
        compute_registeredCase10173CanonicalStructuralEvalTheory.registered_case10173_structural_job_clock_def,
        registered_case10173_structural_list_length_eq_cv_list_length]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_authenticated_full_structural_jobs_clock:
  bounded_packed_chars_case10173_decimal_authenticated_full_check bytes
      encoded_jobs encoded_roots ==>
  registered_case10173_structural_jobs_clock encoded_jobs = 108499
Proof
  rw
    [compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_full_check_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_authenticated_packets_structural_jobs_clock
  >> gvs []
QED

val _ = export_theory ();
