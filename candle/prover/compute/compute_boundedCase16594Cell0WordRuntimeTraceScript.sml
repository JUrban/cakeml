(*****************************************************************************
 * Closed fixed-word runtime-certificate trace for genuine case-16594 cell 0.
 *
 * The input and typed certificates are taken from their proved cell-0 source
 * projections.  Build-time checks fail unless evaluation reaches an explicit
 * successful final state and exactly 134 emitted runtime intervals.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WordRuntimeTrace
Ancestors
  compute_boundedCase16594Cell0WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
Libs
  bossLib preamble wordsLib cv_transLib

val prepared_input_option_tm =
  rhs
    (concl
      compute_boundedCase16594Cell0WordDataTheory.bounded_case16594_cell0_prepared_input_option_value);
val prepared_certificates_option_tm =
  rhs
    (concl
      compute_boundedCase16594Cell0WordDataTheory.bounded_case16594_cell0_prepared_certificates_option_value);

val prepared_input_tm = optionSyntax.dest_some prepared_input_option_tm;
val prepared_certificates_tm =
  optionSyntax.dest_some prepared_certificates_option_tm;

val (prepared_input_constructor,prepared_input_arguments) =
  strip_comb prepared_input_tm;
val _ =
  if fst (dest_const prepared_input_constructor) =
       "BoundedCase16594PreparedInput" then ()
  else raise Fail "unexpected cell0 prepared-input constructor";
val [center_environment_tm,box_environment_tm,radii_tm,_,_] =
  prepared_input_arguments;

(* cv_eval needs closed data at the translated-function boundary.  Evaluate
 * the already-authenticated prepared plan once, use its literal value for
 * computation, and rewrite the resulting theorem back to the named plan. *)
val prepared_program_eval =
  EVAL ``bounded_case16594_prepared_program``;

val runtime_trace_tm =
  list_mk_comb
    (prim_mk_const
       {Name="bounded_analytic64_program_runtime_certificate_trace",
        Thy="compute_boundedAnalyticRuntimeCertificateTrace"},
     [radii_tm,center_environment_tm,box_environment_tm,
      ``bounded_case16594_prepared_program``,
      pairSyntax.mk_pair
        (listSyntax.mk_list ([],``:bounded_taylor64``),
         prepared_certificates_tm)]);

val runtime_trace_computation_tm =
  rhs (concl (REWRITE_CONV [prepared_program_eval] runtime_trace_tm));

val bounded_case16594_cell0_word_runtime_trace_def =
  new_definition
    ("bounded_case16594_cell0_word_runtime_trace_def",
     mk_eq
       (mk_var
         ("bounded_case16594_cell0_word_runtime_trace",
          type_of runtime_trace_tm),
        runtime_trace_tm));

(* Several prerequisite CV theories define extensionally equivalent encoders
 * for these shared datatypes.  Pin the exact encoder identities used by the
 * imported trace theorem before asking cv_eval to match that theorem. *)
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

val runtime_trace_literal_eval = time cv_eval runtime_trace_computation_tm;
val runtime_trace_eval =
  REWRITE_RULE [GSYM prepared_program_eval] runtime_trace_literal_eval;
val runtime_trace_value_tm = rhs (concl runtime_trace_eval);
val runtime_trace_result_tm = optionSyntax.dest_some runtime_trace_value_tm;
val (_,runtime_packets_tm) = pairSyntax.dest_pair runtime_trace_result_tm;
val (runtime_packets,_) = listSyntax.dest_list runtime_packets_tm;
val _ =
  if List.length runtime_packets = 134 then ()
  else raise Fail "unexpected cell0 emitted runtime-certificate count";

val bounded_case16594_cell0_word_runtime_trace_value =
  save_thm
    ("bounded_case16594_cell0_word_runtime_trace_value",
     REWRITE_RULE
       [GSYM bounded_case16594_cell0_word_runtime_trace_def]
       runtime_trace_eval);

Theorem bounded_case16594_cell0_word_runtime_trace_packet_length:
  ?final_state packets.
    bounded_case16594_cell0_word_runtime_trace =
      SOME (final_state,packets) /\
    LENGTH packets = 134
Proof
  rw [bounded_case16594_cell0_word_runtime_trace_value]
QED

val _ = export_theory ();
