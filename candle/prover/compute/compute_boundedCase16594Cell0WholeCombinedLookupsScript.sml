(*****************************************************************************
 * Evaluated lookups for the nine whole-call equations in the exact combined *
 * environment.  Saving these once keeps wrapper proofs from repeatedly      *
 * scanning the 175-equation dispatcher prefix.                               *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WholeCombinedLookups
Ancestors
  compute_boundedCase16594Cell0WholeCombinedEntry
Libs
  bossLib preamble

val whole_lookup_terms =
  [("whole_job_check",
    ``ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
        «candle_cv_q_packed_object_whole_job_check»``),
   ("whole_jobs_check",
    ``ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
        «candle_cv_q_packed_object_whole_jobs_check»``),
   ("whole_check",
    ``ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
        «candle_cv_q_packed_object_whole_check»``),
   ("bool_and",
    ``ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
        «candle_cv_bool_and»``),
   ("list_length",
    ``ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
        «candle_cv_list_length»``),
   ("boxes_split_exact_from",
    ``ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
        «candle_cv_q_boxes_split_exact_from»``),
   ("boxes_compact_join",
    ``ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
        «candle_cv_q_boxes_compact_join»``),
   ("compact_transition",
    ``ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
        «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition»``),
   ("compact_run",
    ``ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
        «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»``)];

val bounded_case16594_cell0_whole_combined_lookups =
  map
    (fn (suffix,term) =>
      save_thm
        ("bounded_case16594_cell0_whole_combined_" ^ suffix ^ "_lookup",
         EVAL term))
    whole_lookup_terms;

val _ = export_theory ();
