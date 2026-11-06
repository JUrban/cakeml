(*****************************************************************************
 * Development probe: execute genuine case-16594 cell 0 on the smallest box  *
 * that covers the source and is covered by the authenticated Taylor radii.      *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0TightWordRuntimeProbe
Ancestors
  compute_boundedCase16594Cell0AuthenticatedWordRuntimeTrace
Libs
  bossLib preamble cv_transLib

val prepared_input_tm =
  optionSyntax.dest_some
    (rhs
      (concl
        compute_boundedCase16594Cell0WordDataTheory.bounded_case16594_cell0_prepared_input_option_value));
val prepared_certificates_tm =
  optionSyntax.dest_some
    (rhs
      (concl
        compute_boundedCase16594Cell0WordDataTheory.bounded_case16594_cell0_prepared_certificates_option_value));
val (_,prepared_input_arguments) = strip_comb prepared_input_tm;
val [center_environment_tm,box_environment_tm,radii_tm,_,_] =
  prepared_input_arguments;

val tight_box_environment_tm =
  ``[BoundedInterval64
       (BoundedSigned64 F 5690192576066w)
       (BoundedSigned64 F 6013229092309w);
     BoundedInterval64
       (BoundedSigned64 F 4398046511104w)
       (BoundedSigned64 F 4721083027347w);
     BoundedInterval64
       (BoundedSigned64 F 5690192576066w)
       (BoundedSigned64 F 6013229092309w);
     BoundedInterval64
       (BoundedSigned64 F 4398046511104w)
       (BoundedSigned64 F 5044119543587w);
     BoundedInterval64
       (BoundedSigned64 F 11652156938728w)
       (BoundedSigned64 F 12074774848709w);
     BoundedInterval64
       (BoundedSigned64 F 5690192576066w)
       (BoundedSigned64 F 6336265608550w)] : bounded_interval64 list``;

val prepared_program_eval = EVAL ``bounded_case16594_prepared_program``;
val runtime_trace_tm =
  list_mk_comb
    (prim_mk_const
       {Name="bounded_analytic64_program_runtime_certificate_trace",
        Thy="compute_boundedAnalyticRuntimeCertificateTrace"},
     [radii_tm,center_environment_tm,tight_box_environment_tm,
      ``bounded_case16594_prepared_program``,
      pairSyntax.mk_pair
        (listSyntax.mk_list ([],``:bounded_taylor64``),
         prepared_certificates_tm)]);
val runtime_trace_computation_tm =
  rhs (concl (REWRITE_CONV [prepared_program_eval] runtime_trace_tm));

val _ =
  List.app cv_memLib.cv_from_to_add
    [compute_boundedAnalyticRuntimeCertificateTraceCVTheory.from_compute_bounded_to_compute_bounded_bounded128_thm,
     compute_boundedAnalyticRuntimeCertificateTraceWideCVTheory.from_compute_bounded_to_compute_bounded_bounded192_thm,
     compute_boundedAnalyticRuntimeCertificateTraceCVTheory.from_compute_boundedSigned_to_compute_boundedSigned_bounded_signed64_thm,
     compute_boundedAnalyticRuntimeCertificateTraceCVTheory.from_compute_boundedSigned_to_compute_boundedSigned_bounded_signed128_thm,
     compute_boundedAnalyticRuntimeCertificateTraceWideCVTheory.from_compute_boundedWideSigned_to_compute_boundedWideSigned_bounded_signed192_thm,
     compute_boundedAnalyticRuntimeCertificateTraceCVTheory.from_compute_boundedInterval_to_compute_boundedInterval_bounded_interval64_thm,
     compute_boundedAnalyticRuntimeCertificateTraceCVTheory.from_compute_boundedTaylorState_to_compute_boundedTaylorState_bounded_taylor64_thm,
     compute_boundedAnalyticRuntimeCertificateTraceCVTheory.from_compute_boundedTaylorProgram_to_compute_boundedTaylorProgram_bounded_taylor64_instruction_thm,
     compute_boundedAnalyticRuntimeCertificateTraceCVTheory.from_compute_boundedAnalyticProgram_to_compute_boundedAnalyticProgram_bounded_analytic64_instruction_thm,
     compute_boundedAnalyticRuntimeCertificateTraceCVTheory.from_compute_boundedAnalyticProgram_to_compute_boundedAnalyticProgram_bounded_analytic64_certificate_thm];

val runtime_trace_eval =
  REWRITE_RULE [GSYM prepared_program_eval]
    (time cv_eval runtime_trace_computation_tm);
val runtime_trace_value_tm = rhs (concl runtime_trace_eval);
val runtime_trace_result_tm = optionSyntax.dest_some runtime_trace_value_tm;
val (runtime_final_state_tm,runtime_packets_tm) =
  pairSyntax.dest_pair runtime_trace_result_tm;
val (runtime_stack_tm,runtime_remaining_certificates_tm) =
  pairSyntax.dest_pair runtime_final_state_tm;
val (runtime_stack_items,_) = listSyntax.dest_list runtime_stack_tm;
val (runtime_remaining_certificate_items,_) =
  listSyntax.dest_list runtime_remaining_certificates_tm;
val (runtime_packets,_) = listSyntax.dest_list runtime_packets_tm;
val runtime_result_tm =
  case runtime_stack_items of
    [result] => result
  | _ => raise Fail "tight runtime did not leave one result";
val _ =
  if List.null runtime_remaining_certificate_items andalso
     List.length runtime_packets = 134 then ()
  else raise Fail "tight runtime did not consume the exact certificate stream";

val guarded_result_tm =
  rhs
    (concl
      compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_result_def);
val guarded_packets_tm =
  rhs
    (concl
      compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_packets_def);
val result_matches_guarded = aconv runtime_result_tm guarded_result_tm;
val packets_match_guarded = aconv runtime_packets_tm guarded_packets_tm;
val _ =
  print
    ("CANDLE_CASE16594_CELL0_TIGHT_RUNTIME_PROBE" ^
     " instructions=167 packets=134 result_matches_guarded=" ^
     Bool.toString result_matches_guarded ^
     " packets_match_guarded=" ^ Bool.toString packets_match_guarded ^ "\n");

val bounded_case16594_cell0_tight_word_runtime_trace_def =
  new_definition
    ("bounded_case16594_cell0_tight_word_runtime_trace_def",
     mk_eq
       (mk_var
         ("bounded_case16594_cell0_tight_word_runtime_trace",
          type_of runtime_trace_tm),
        runtime_trace_tm));

val bounded_case16594_cell0_tight_word_runtime_trace_value =
  save_thm
    ("bounded_case16594_cell0_tight_word_runtime_trace_value",
     REWRITE_RULE
       [GSYM bounded_case16594_cell0_tight_word_runtime_trace_def]
       runtime_trace_eval);

val _ = export_theory ();
