(*****************************************************************************
 * Authenticated numerical half of the production case-16594 whole callback. *
 *                                                                           *
 * The external certificate bytes, source descriptor, packed cells, and jobs *
 * are all call-time inputs.  The checker accepts only the canonical 167-step *
 * source, the versioned 875-by-31 certificate header, and a complete          *
 * streaming lockstep match.                                                  *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeJobsChecker
Ancestors
  compute_cvPackedBytes
  compute_boundedCase16594WordWholeCellsMatcher
Libs
  bossLib preamble intLib

Definition bounded_case16594_word_whole_jobs_checker_def:
  bounded_case16594_word_whole_jobs_checker certificate source_descriptor
      encoded_jobs <=>
    case cv_unpack_byte_tree certificate of
    | NONE => F
    | SOME bytes =>
        case bounded_packed_chars_analytic_header 875w 31w bytes of
        | NONE => F
        | SOME rest =>
            case source_descriptor of
            | Pair plan_codes source_and_cells =>
                (case source_and_cells of
                 | Pair source_instructions packed_cells =>
                     plan_codes =
                       bounded_case16594_generic_prefix167_codes_cv /\
                     source_instructions =
                       bounded_case16594_generic_prefix167_sources_cv /\
                     bounded_case16594_word_whole_cells_match 875 rest
                       packed_cells encoded_jobs = SOME (Num 1)
                 | _ => F)
            | _ => F
End

Theorem bounded_case16594_word_whole_jobs_checker_contract:
  bounded_case16594_word_whole_jobs_checker certificate source_descriptor
      encoded_jobs ==>
  ?bytes rest packed_cells.
    cv_unpack_byte_tree certificate = SOME bytes /\
    bounded_packed_chars_analytic_header 875w 31w bytes = SOME rest /\
    source_descriptor =
      Pair bounded_case16594_generic_prefix167_codes_cv
        (Pair bounded_case16594_generic_prefix167_sources_cv packed_cells) /\
    bounded_case16594_word_whole_cells_match 875 rest packed_cells
      encoded_jobs = SOME (Num 1)
Proof
  rw [bounded_case16594_word_whole_jobs_checker_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_case16594_word_whole_jobs_default_clock_capacity:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 875 + 12 <
    compute_default_clock
Proof
  rw
    [compute_boundedCase16594ObjectDispatchJointAcceptedEntryEvalTheory.bounded_case16594_object_joint_complete_runtime_payload_identity,
     GSYM
       compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_codes_identity,
     compute_boundedCase16594ObjectDispatchCell0TraceContractTheory.bounded_case16594_runtime_cell0_codes_cv_length,
     computeTheory.compute_default_clock]
QED

Theorem bounded_case16594_word_whole_jobs_checker_eval:
  bounded_case16594_word_whole_jobs_checker certificate
      (Pair bounded_case16594_generic_prefix167_codes_cv
        (Pair bounded_case16594_generic_prefix167_sources_cv packed_cells))
      encoded_jobs ==>
  compute_eval compute_default_clock
    bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_jobs_check»
      [from_cv bounded_case16594_generic_prefix167_codes_cv;
       from_cv bounded_case16594_generic_prefix167_sources_cv;
       from_cv packed_cells;from_cv encoded_jobs])
    (refs:hol_refs) = (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> imp_res_tac bounded_case16594_word_whole_jobs_checker_contract
  >> gvs []
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         compute_boundedCase16594WordWholeCellsMatcherTheory.bounded_case16594_word_whole_cells_match_eval_clock)
  >> qexists_tac `rest`
  >> qexists_tac `875`
  >> asm_rewrite_tac
       [bounded_case16594_word_whole_jobs_default_clock_capacity]
QED

Theorem bounded_case16594_word_whole_jobs_checker_rejects_source_code:
  plan_codes <> bounded_case16594_generic_prefix167_codes_cv ==>
  ~bounded_case16594_word_whole_jobs_checker certificate
    (Pair plan_codes
      (Pair bounded_case16594_generic_prefix167_sources_cv packed_cells))
    encoded_jobs
Proof
  simp [bounded_case16594_word_whole_jobs_checker_def]
  >> every_case_tac
  >> simp []
QED

Theorem bounded_case16594_word_whole_jobs_checker_rejects_source_program:
  source_instructions <>
      bounded_case16594_generic_prefix167_sources_cv ==>
  ~bounded_case16594_word_whole_jobs_checker certificate
    (Pair bounded_case16594_generic_prefix167_codes_cv
      (Pair source_instructions packed_cells)) encoded_jobs
Proof
  simp [bounded_case16594_word_whole_jobs_checker_def]
  >> every_case_tac
  >> simp []
QED

Theorem bounded_case16594_word_whole_jobs_checker_rejects_certificate_tree:
  cv_unpack_byte_tree certificate = NONE ==>
  ~bounded_case16594_word_whole_jobs_checker certificate source_descriptor
    encoded_jobs
Proof
  simp [bounded_case16594_word_whole_jobs_checker_def]
QED

val _ = export_theory ();
