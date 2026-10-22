(*****************************************************************************
 * Reusable box binding between a complete case-10173 word packet and one
 * object-level Flyspeck job.
 *
 * This boundary intentionally authenticates only the source box.  The
 * object's source-square-root data, the four historical root records, and
 * batch topology remain separate obligations.  In particular, none of
 * those fields is silently authorized merely because two jobs share a box.
 *****************************************************************************)
Theory compute_boundedCase10173JobBinding
Ancestors
  compute_boundedObjectIntervalRelation
  compute_registeredCase10173Cell0Data
  compute_payloadFast
Libs
  bossLib preamble wordsLib

Definition bounded_case10173_packet_box_environment_def:
  bounded_case10173_packet_box_environment
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) =
    box_environment
End

(* The exact object-job representation is
 * [Pair box_sqrt_data (Pair center_sqrt_data boxes)]. *)
Definition bounded_case10173_object_job_boxes_def:
  bounded_case10173_object_job_boxes
      (Pair box_sqrt_data (Pair center_sqrt_data boxes) : cv) = SOME boxes /\
  bounded_case10173_object_job_boxes _ = NONE
End

Definition bounded_case10173_packet_box_binds_object_job_def:
  bounded_case10173_packet_box_binds_object_job packet job <=>
    case bounded_case10173_object_job_boxes job of
    | NONE => F
    | SOME source_boxes =>
        bounded_interval64_list_covers_object_q
          (bounded_case10173_packet_box_environment packet) source_boxes
End

(* A strict two-field development payload.  This is not yet the final batch
 * schema: it proves that a successful numerical packet is inseparable from
 * the object job whose box it covers. *)
Definition bounded_case10173_box_bound_payload_accept_def:
  bounded_case10173_box_bound_payload_accept payload <=>
    case payload of
    | Pair encoded_packet object_job =>
        (case bounded_cv_decode_case10173_packet encoded_packet of
         | NONE => F
         | SOME packet =>
             bounded_case10173_packet_accepts packet /\
             bounded_case10173_packet_box_binds_object_job
               packet object_job)
    | _ => F
End

(* Extract the first complete literal job without copying its large value.
 * Source/program identity and the other complete-call arguments remain
 * visible in the surrounding expression and can be authenticated by the
 * eventual registered entry point. *)
Definition bounded_case10173_complete_call_first_job_def:
  bounded_case10173_complete_call_first_job expression =
    case expression of
    | App function_name [a;b;c;d] =>
        (case compute_exp_to_cv d of
         | SOME (Pair object_job remaining_jobs) => SOME object_job
         | _ => NONE)
    | _ => NONE
End

Theorem bounded_case10173_packet_box_binds_object_job_components:
  bounded_case10173_packet_box_binds_object_job packet object_job ==>
  ?source_boxes.
    bounded_case10173_object_job_boxes object_job = SOME source_boxes /\
    bounded_interval64_list_covers_object_q
      (bounded_case10173_packet_box_environment packet) source_boxes
Proof
  rw [bounded_case10173_packet_box_binds_object_job_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_case10173_box_bound_payload_accept_sound:
  bounded_case10173_box_bound_payload_accept payload ==>
  ?encoded_packet object_job packet source_boxes.
    payload = Pair encoded_packet object_job /\
    bounded_cv_decode_case10173_packet encoded_packet = SOME packet /\
    bounded_case10173_packet_well_shaped packet /\
    bounded_case10173_packet_accepts packet /\
    bounded_case10173_object_job_boxes object_job = SOME source_boxes /\
    bounded_interval64_list_covers_object_q
      (bounded_case10173_packet_box_environment packet) source_boxes
Proof
  Cases_on `payload`
  >> rw [bounded_case10173_box_bound_payload_accept_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedCase10173PacketTheory.bounded_cv_decode_case10173_packet_well_shaped
  >> imp_res_tac bounded_case10173_packet_box_binds_object_job_components
  >> metis_tac []
QED

Theorem bounded_case10173_box_bound_payload_rejects_nonpair[simp]:
  ~bounded_case10173_box_bound_payload_accept (Num n)
Proof
  simp [bounded_case10173_box_bound_payload_accept_def]
QED

Theorem bounded_case10173_box_bound_payload_rejects_malformed_job[simp]:
  ~bounded_case10173_box_bound_payload_accept
    (Pair encoded_packet (Num n))
Proof
  simp [bounded_case10173_box_bound_payload_accept_def,
        bounded_case10173_packet_box_binds_object_job_def,
        bounded_case10173_object_job_boxes_def]
  >> every_case_tac
  >> simp []
QED

Theorem bounded_case10173_complete_call_first_job_rejects_variable[simp]:
  bounded_case10173_complete_call_first_job (Var name) = NONE
Proof
  simp [bounded_case10173_complete_call_first_job_def]
QED

Theorem bounded_case10173_cell0_box_bound_payload_accepts:
  ?object_job.
    bounded_case10173_complete_call_first_job
      registered_case10173_cell0_cexp = SOME object_job /\
    bounded_case10173_box_bound_payload_accept
      (Pair
        (bounded_cv_encode_case10173_packet
          bounded_case10173_cell0_packet)
        object_job)
Proof
  simp [bounded_case10173_complete_call_first_job_def,
        bounded_case10173_box_bound_payload_accept_def,
        bounded_case10173_packet_box_binds_object_job_def,
        bounded_case10173_object_job_boxes_def,
        bounded_case10173_packet_box_environment_def,
        compute_registeredCase10173Cell0DataTheory.registered_case10173_cell0_cexp_def,
        compute_pureFastTheory.compute_exp_to_cv_def,
        compute_boundedCase10173PacketTheory.bounded_cv_decode_case10173_packet_encode_exact,
        compute_boundedCase10173PacketTheory.bounded_case10173_cell0_packet_well_shaped,
        compute_boundedCase10173PacketTheory.bounded_case10173_cell0_packet_accepts]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
