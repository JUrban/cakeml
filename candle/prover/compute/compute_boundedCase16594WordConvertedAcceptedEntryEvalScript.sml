(*****************************************************************************
 * Reusable accepted-entry theorem for exact object encodings of word inputs.
 *
 * A finite cell authentication should only need to supply its successful
 * fixed-word trace, packet contract, final acceptance, and elementary input
 * shape facts.  This theory discharges the representation and validity
 * obligations of the generic object-entry theorem once for every such cell.
 *****************************************************************************)
Theory compute_boundedCase16594WordConvertedAcceptedEntryEval
Ancestors
  compute_boundedCase16594ObjectDispatchJointAcceptedEntryEval
  compute_boundedAnalyticObjectCertificateRefinement
  compute_boundedPackedObjectSourceContractRefinement
  compute_boundedCase16594ObjectRuntimePreservation
Libs
  bossLib preamble

Theorem bounded_interval64_list_covers_own_object_q:
  !word_intervals.
    EVERY bounded_interval64_valid word_intervals ==>
    LIST_REL bounded_interval64_covers_object_q word_intervals
      (MAP bounded_interval64_object_q_cv word_intervals)
Proof
  Induct
  >> simp
       [LIST_REL_def,
        compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_covers_own_object_q]
QED

Theorem bounded_word64_object_q_list_equiv_refl:
  !word_values.
    LIST_REL bounded_case10173_q_cv_equiv
      (MAP bounded_word64_object_q_cv word_values)
      (MAP bounded_word64_object_q_cv word_values)
Proof
  Induct
  >> simp
       [LIST_REL_def,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded,
        compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl]
QED

Theorem bounded_case16594_word_converted_default_clock_capacity:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 3 <
    compute_default_clock
Proof
  rw
    [CONJUNCT1
       compute_boundedCase16594ObjectDispatchJointAcceptedEntryEvalTheory.bounded_case16594_object_joint_complete_runtime_payload_identity,
     GSYM
       compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_codes_identity,
     compute_boundedCase16594ObjectDispatchCell0TraceContractTheory.bounded_case16594_runtime_cell0_codes_cv_length,
     computeTheory.compute_default_clock]
QED

Theorem bounded_case16594_word_converted_complete_accepted_entry_eval:
  LENGTH word_radii = 6 /\
  LENGTH word_center_boxes = 6 /\
  LENGTH word_outer_boxes = 6 /\
  EVERY bounded_interval64_valid word_center_boxes /\
  EVERY bounded_interval64_valid word_outer_boxes /\
  bounded_taylor_radius_pairs word_radii = SOME weights /\
  bounded_analytic64_program_runtime_certificate_trace word_radii
    word_center_boxes word_outer_boxes bounded_case16594_prepared_program
    ([],word_certificates) = SOME (([word_result],[]),packets) /\
  bounded_case16594_word_dispatch_packet_contracts
    word_certificates packets /\
  bounded_packed_analytic_result_accepts word_result /\
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 3 < clock
  ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_dispatch_entry»
      [from_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv word_center_boxes));
       from_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv word_outer_boxes));
       from_cv
        (bounded_object_q_cv_list
          (MAP bounded_word64_object_q_cv word_radii));
       from_cv bounded_case16594_generic_prefix167_codes_cv;
       from_cv bounded_case16594_generic_prefix167_sources_cv;
       from_cv
         (bounded_object_q_cv_list
           (MAP bounded_interval64_object_q_cv packets))])
    (refs:hol_refs) =
      (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> `LIST_REL bounded_interval64_covers_object_q word_center_boxes
        (MAP bounded_interval64_object_q_cv word_center_boxes)` by
       metis_tac [bounded_interval64_list_covers_own_object_q]
  >> `LIST_REL bounded_interval64_covers_object_q word_outer_boxes
        (MAP bounded_interval64_object_q_cv word_outer_boxes)` by
       metis_tac [bounded_interval64_list_covers_own_object_q]
  >> `EVERY bounded_packed_q_interval_valid_cv
        (MAP bounded_interval64_object_q_cv word_center_boxes)` by
       metis_tac
         [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_interval64_list_covers_packed_q_interval_valid_cv]
  >> `EVERY bounded_packed_q_interval_valid_cv
        (MAP bounded_interval64_object_q_cv word_outer_boxes)` by
       metis_tac
         [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_interval64_list_covers_packed_q_interval_valid_cv]
  >> `EVERY bounded_object_q_interval_encoded
        (MAP bounded_interval64_object_q_cv word_center_boxes)` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_interval64_list_covers_object_q_encoded]
  >> `EVERY bounded_object_q_interval_encoded
        (MAP bounded_interval64_object_q_cv word_outer_boxes)` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_interval64_list_covers_object_q_encoded]
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        (MAP bounded_interval64_object_q_cv word_center_boxes)
        (MAP bounded_interval64_object_q_cv word_center_boxes)` by
       metis_tac
         [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_list_rel_refl]
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        (MAP bounded_interval64_object_q_cv word_outer_boxes)
        (MAP bounded_interval64_object_q_cv word_outer_boxes)` by
       metis_tac
         [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_list_rel_refl]
  >> `EVERY bounded_object_q_encoded
        (MAP bounded_word64_object_q_cv word_radii)` by
       simp
         [listTheory.EVERY_MAP,
          compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded]
  >> irule
       compute_boundedCase16594ObjectDispatchJointAcceptedEntryEvalTheory.bounded_case16594_object_joint_complete_accepted_entry_eval
  >> asm_rewrite_tac
       [bounded_word64_object_q_list_equiv_refl]
  >> simp []
  >> qexists_tac `word_radii`
  >> qexists_tac `weights`
  >> qexists_tac `word_center_boxes`
  >> qexists_tac `word_certificates`
  >> qexists_tac `word_outer_boxes`
  >> qexists_tac `word_result`
  >> asm_rewrite_tac
       [bounded_word64_object_q_list_equiv_refl]
QED

val _ = export_theory ();
