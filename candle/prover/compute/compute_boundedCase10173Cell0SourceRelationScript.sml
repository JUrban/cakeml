(*****************************************************************************
 * First genuine source-binding instance for the reusable NL refinement.
 *
 * Extract the original rational box from the authenticated cell-0 compute
 * call itself, rather than copying a second box fixture, and prove that the
 * complete word checker's box interval encloses every source endpoint.  This
 * is the first part of the eventual varying-packet contract: accepted word
 * data must describe the object-level Flyspeck job it is used to prove.
 *****************************************************************************)
Theory compute_boundedCase10173Cell0SourceRelation
Ancestors
  compute_boundedObjectIntervalRelation
  compute_registeredCase10173Cell0Data
  compute_payloadFast
Libs
  bossLib preamble wordsLib

(* The object call has arguments [source; dimension; tokens; jobs].  A job is
 * [Pair box_sqrt_data (Pair center_sqrt_data boxes)] and jobs form a proper
 * cval list.  Every other expression/value shape fails closed. *)
Definition bounded_case10173_complete_call_first_boxes_def:
  bounded_case10173_complete_call_first_boxes expression =
    case expression of
    | App f [a;b;c;d] =>
        (case compute_exp_to_cv d of
         | SOME (Pair (Pair p (Pair q r)) s) => SOME r
         | _ => NONE)
    | _ => NONE
End

Theorem bounded_case10173_complete_call_first_boxes_rejects_variable[simp]:
  bounded_case10173_complete_call_first_boxes (Var name) = NONE
Proof
  simp [bounded_case10173_complete_call_first_boxes_def]
QED

Theorem bounded_case10173_cell0_source_box_relation:
  ?source_boxes.
    bounded_case10173_complete_call_first_boxes
      registered_case10173_cell0_cexp = SOME source_boxes /\
    bounded_interval64_list_covers_object_q
      bounded_case10173_cell0_box_environment source_boxes
Proof
  simp [bounded_case10173_complete_call_first_boxes_def,
        compute_registeredCase10173Cell0DataTheory.registered_case10173_cell0_cexp_def,
        compute_pureFastTheory.compute_exp_to_cv_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case10173_cell0_source_box_width:
  bounded_case10173_complete_call_first_boxes
      registered_case10173_cell0_cexp = SOME source_boxes ==>
  bounded_object_q_interval_list source_boxes = SOME object_intervals ==>
  LENGTH object_intervals = 6
Proof
  strip_tac
  >> strip_tac
  >> mp_tac bounded_case10173_cell0_source_box_relation
  >> disch_then (qx_choose_then `related_source_boxes` strip_assume_tac)
  >> gvs [bounded_interval64_list_covers_object_q_def]
  >> imp_res_tac LIST_REL_LENGTH
  >> fs [compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_box_environment_def]
QED

val _ = export_theory ();
