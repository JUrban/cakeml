(*****************************************************************************
 * Authenticated-stream reduction for the registered historical evaluator.
 *
 * The packed decimal authenticator and the registered checked-jobs evaluator
 * recurse over the same source-job/root streams.  This theory synchronizes
 * those recursions once and for all.  The complete batch refinement is thereby
 * reduced to one reusable, local theorem saying that an authenticated packet
 * discharges the registered evaluator's head contract.
 *****************************************************************************)
Theory compute_registeredCase10173AuthenticatedEval
Ancestors
  compute_registeredCase10173CheckedJobsEval
  compute_boundedCase10173PackedDecimalAuthenticated
Libs
  bossLib preamble

Definition registered_case10173_decimal_authenticated_head_refines_def:
  registered_case10173_decimal_authenticated_head_refines
      head_clock_bound source_program <=>
    !packet object_job root_record.
      bounded_packed_chars_case10173_decimal_packet_ok packet /\
      bounded_case10173_decimal_packet_box_binds_object_job
        packet object_job /\
      bounded_case10173_decimal_packet_root_inputs_exact
        packet object_job root_record /\
      bounded_case10173_source_coordinate_sqrts_exact object_job /\
      bounded_case10173_source_coordinate_sqrt_decimals_exact
        packet object_job /\
      bounded_case10173_source_actual_sqrt_contract packet object_job /\
      bounded_case10173_literal_source_accepts_decimal packet /\
      bounded_case10173_decimal_packet_source_radii_exact
        packet object_job ==>
      ?box_sqrt_data center_sqrt_data boxes
       box_remainder box_program center_remainder center_program.
        object_job =
          Pair box_sqrt_data (Pair center_sqrt_data boxes) /\
        !clock refs.
          head_clock_bound < clock ==>
          registered_case10173_hist_checked_job_head_eval_ok clock
            source_program box_sqrt_data center_sqrt_data boxes root_record
            box_remainder box_program center_remainder center_program refs
End

Theorem registered_case10173_decimal_authenticated_packets_eval:
  !remaining bytes encoded_jobs encoded_roots current_count result clock refs.
    bounded_packed_chars_case10173_decimal_authenticated_packets
      remaining bytes encoded_jobs encoded_roots current_count = SOME result /\
    registered_case10173_decimal_authenticated_head_refines
      head_clock_bound source_program /\
    3 * remaining + head_clock_bound < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_checked_jobs_check»
        [from_cv source_program;from_cv encoded_jobs;from_cv encoded_roots])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  Induct_on `remaining`
  >- (rpt gen_tac
      >> Cases_on `encoded_jobs`
      >> Cases_on `encoded_roots`
      >> rw
           [compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_packets_def]
      >> gvs []
      >> assume_tac
           (Q.INST [`jobs_nil` |-> `0`, `roots_nil` |-> `0`]
             registered_case10173_hist_checked_jobs_check_nil_eval)
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
       compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_step
  >> strip_tac
  >> fs [registered_case10173_decimal_authenticated_head_refines_def]
  >> qpat_x_assum `!packet object_job root_record. _`
       (fn th =>
          assume_tac th
          >> mp_tac (Q.SPECL [`packet`,`c`,`c'`] th))
  >> simp []
  >> strip_tac
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_hist_checked_jobs_check_cons_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (qpat_x_assum `!bytes' encoded_jobs encoded_roots current_count'. _`
        match_mp_tac
      >> qexists_tac `rest`
      >> qexists_tac `SUC current_count`
      >> qexists_tac `result`
      >> simp []
      >> qpat_x_assum `!packet object_job root_record. _` ACCEPT_TAC)
  >> qexists_tac `box_program`
  >> qexists_tac `box_remainder`
  >> qexists_tac `center_program`
  >> qexists_tac `center_remainder`
  >> qpat_x_assum `!clock refs. _` match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_decimal_authenticated_full_eval:
  bounded_packed_chars_case10173_decimal_authenticated_full_check bytes
      encoded_jobs encoded_roots /\
  registered_case10173_decimal_authenticated_head_refines
    head_clock_bound source_program /\
  12519 + head_clock_bound < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_checked_jobs_check»
        [from_cv source_program;from_cv encoded_jobs;from_cv encoded_roots])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  rw
    [compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_full_check_def]
  >> every_case_tac
  >> gvs []
  >> irule registered_case10173_decimal_authenticated_packets_eval
  >> qexists_tac `x`
  >> qexists_tac `0`
  >> qexists_tac `head_clock_bound`
  >> qexists_tac `4173`
  >> qexists_tac `4173`
  >> simp []
QED

val _ = export_theory ();
