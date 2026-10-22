(*****************************************************************************
 * Root-record binding for the specialized case-10173 packet.
 *
 * The checked object route supplies four fixed-scale square-root intervals
 * per job.  The word route supplies the corresponding center-delta,
 * center-four-x0, box-delta, and box-four-x0 intervals at scale 2^40.  This
 * theory relates those representations explicitly and extracts the first
 * genuine job/root pair from the authenticated 16-cell call for a concrete
 * discriminator.  The two implementations use independent outward rounding,
 * so neither interval set is authorized as a replacement for the other.
 *****************************************************************************)
Theory compute_boundedCase10173RootBinding
Ancestors
  compute_boundedCase10173JobBinding
  compute_registeredCase10173HistoricalChunk16Data
Libs
  bossLib preamble wordsLib

val _ = monadsyntax.temp_enable_monad "option";

Definition bounded_object_interval_list_def:
  bounded_object_interval_list (Num 0 : cv) = SOME [] /\
  bounded_object_interval_list (Pair interval intervals) =
    do
      interval' <- bounded_object_interval_ints interval;
      intervals' <- bounded_object_interval_list intervals;
      return (interval'::intervals')
    od /\
  bounded_object_interval_list _ = NONE
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

(* Retain the original encoded intervals while checking them. *)
Definition bounded_interval64_list_covers_object_fixed_cv_def:
  bounded_interval64_list_covers_object_fixed_cv [] (Num 0 : cv) = T /\
  bounded_interval64_list_covers_object_fixed_cv
      (interval::intervals) (Pair encoded_interval encoded_intervals) =
    (bounded_interval64_covers_object_fixed interval encoded_interval /\
     bounded_interval64_list_covers_object_fixed_cv
       intervals encoded_intervals) /\
  bounded_interval64_list_covers_object_fixed_cv _ _ = F
End

Definition bounded_case10173_packet_root_intervals_def:
  bounded_case10173_packet_root_intervals
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) =
    [center_root_delta;center_root_four_x0;
     box_root_delta;box_root_four_x0]
End

Definition bounded_case10173_packet_roots_bind_object_record_def:
  bounded_case10173_packet_roots_bind_object_record packet root_record <=>
    bounded_interval64_list_covers_object_fixed_cv
      (bounded_case10173_packet_root_intervals packet) root_record
End

Definition bounded_interval64_list_overlaps_object_fixed_cv_def:
  bounded_interval64_list_overlaps_object_fixed_cv [] (Num 0 : cv) = T /\
  bounded_interval64_list_overlaps_object_fixed_cv
      (interval::intervals) (Pair encoded_interval encoded_intervals) =
    (bounded_interval64_overlaps_object_fixed interval encoded_interval /\
     bounded_interval64_list_overlaps_object_fixed_cv
       intervals encoded_intervals) /\
  bounded_interval64_list_overlaps_object_fixed_cv _ _ = F
End

Definition bounded_case10173_packet_roots_overlap_object_record_def:
  bounded_case10173_packet_roots_overlap_object_record packet root_record <=>
    bounded_interval64_list_overlaps_object_fixed_cv
      (bounded_case10173_packet_root_intervals packet) root_record
End

Definition bounded_case10173_checked_call_first_job_root_def:
  bounded_case10173_checked_call_first_job_root expression =
    case expression of
    | App function_name [a;b;c] =>
        (case (compute_exp_to_cv b,compute_exp_to_cv c) of
         | (SOME (Pair object_job remaining_jobs),
            SOME (Pair root_record remaining_roots)) =>
             SOME (Pair object_job root_record)
         | _ => NONE)
    | _ => NONE
End

Theorem bounded_interval64_list_covers_object_fixed_cv_decodes:
  !intervals encoded.
    bounded_interval64_list_covers_object_fixed_cv intervals encoded ==>
    ?object_intervals.
      bounded_object_interval_list encoded = SOME object_intervals /\
      LENGTH intervals = LENGTH object_intervals
Proof
  Induct
  >- (Cases_on `encoded`
      >> simp [bounded_interval64_list_covers_object_fixed_cv_def,
               bounded_object_interval_list_def]
      >> Cases_on `n`
      >> simp [bounded_interval64_list_covers_object_fixed_cv_def,
               bounded_object_interval_list_def])
  >> gen_tac
  >> Cases_on `encoded`
  >- (Cases_on `n`
      >> simp [bounded_interval64_list_covers_object_fixed_cv_def])
  >> simp [bounded_interval64_list_covers_object_fixed_cv_def]
  >> strip_tac
  >> drule
       compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_fixed_decodes
  >> strip_tac
  >> first_x_assum drule
  >> strip_tac
  >> qexists_tac `(object_lower,object_upper)::object_intervals`
  >> simp [bounded_object_interval_list_def]
QED

Theorem bounded_case10173_cell0_job_root_extraction:
  ?object_job root_record.
    bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp =
        SOME (Pair object_job root_record)
Proof
  simp [bounded_case10173_checked_call_first_job_root_def,
        compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def,
        compute_pureFastTheory.compute_exp_to_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case10173_cell0_historical_first_job_box_binding:
  ?object_job root_record.
    bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp =
        SOME (Pair object_job root_record) /\
    bounded_case10173_packet_box_binds_object_job
      bounded_case10173_cell0_packet object_job
Proof
  simp [bounded_case10173_checked_call_first_job_root_def,
        bounded_case10173_packet_box_binds_object_job_def,
        bounded_case10173_object_job_boxes_def,
        bounded_case10173_packet_box_environment_def,
        compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def,
        compute_pureFastTheory.compute_exp_to_cv_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

(* The genuine records are positionally aligned and intersect, but the
 * relation is not enclosure.  This theorem is an identity discriminator;
 * semantic authorization must come from validating each packet root against
 * the authenticated job's radicand. *)
Theorem bounded_case10173_cell0_historical_first_roots_overlap:
  ?object_job root_record.
    bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp =
        SOME (Pair object_job root_record) /\
    bounded_case10173_packet_roots_overlap_object_record
      bounded_case10173_cell0_packet root_record
Proof
  simp [bounded_case10173_checked_call_first_job_root_def,
        bounded_case10173_packet_roots_overlap_object_record_def,
        bounded_case10173_packet_root_intervals_def,
        bounded_interval64_list_overlaps_object_fixed_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_overlaps_object_fixed_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_overlaps_object_at_scale_def,
        compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def,
        compute_pureFastTheory.compute_exp_to_cv_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case10173_cell0_historical_roots_not_enclosed:
  ?object_job root_record.
    bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp =
        SOME (Pair object_job root_record) /\
    ~bounded_case10173_packet_roots_bind_object_record
      bounded_case10173_cell0_packet root_record
Proof
  simp [bounded_case10173_checked_call_first_job_root_def,
        bounded_case10173_packet_roots_bind_object_record_def,
        bounded_case10173_packet_root_intervals_def,
        bounded_interval64_list_covers_object_fixed_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_fixed_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_at_scale_def,
        compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def,
        compute_pureFastTheory.compute_exp_to_cv_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
