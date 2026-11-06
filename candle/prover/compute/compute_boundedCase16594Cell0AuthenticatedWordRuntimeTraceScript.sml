(*****************************************************************************
 * Fixed-word trace on a box that actually encloses the authenticated
 * case-16594 cell-0 production payload.
 *
 * The initial DEVELOPMENT fixture is the inward-rounded source word box.
 * Coordinate 5 needs one upper-endpoint unit to cover the genuine exact
 * source; every other endpoint already covers it.  Use precisely that minimal
 * expansion, prove that it covers the authenticated object-q box, and
 * evaluate the unchanged 167-instruction checker with the unchanged typed
 * certificates.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0AuthenticatedWordRuntimeTrace
Ancestors
  compute_boundedCase16594Cell0WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594ObjectDispatchCell0PayloadIdentity
  compute_boundedAnalyticObjectCertificateRefinement
  compute_boundedPackedObjectEntryContract
Libs
  bossLib preamble wordsLib cv_transLib intLib

fun development_stage name =
  (print ("CANDLE_CASE16594_TIGHT_TRACE_STAGE " ^ name ^ "\n");
   TextIO.flushOut TextIO.stdOut);

Definition bounded_case16594_interval64_outward_one_def:
  bounded_case16594_interval64_outward_one
      (BoundedInterval64
        (BoundedSigned64 lower_negative lower_magnitude)
        (BoundedSigned64 upper_negative upper_magnitude)) =
    BoundedInterval64
      (BoundedSigned64 lower_negative
        (if lower_negative then lower_magnitude + 1w
         else lower_magnitude - 1w))
      (BoundedSigned64 upper_negative
        (if upper_negative then upper_magnitude - 1w
         else upper_magnitude + 1w))
End

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

fun define_literal name ty tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,ty),tm));

val bounded_case16594_cell0_source_word_center_environment_def =
  define_literal "bounded_case16594_cell0_source_word_center_environment"
    ``:bounded_interval64 list`` center_environment_tm;
val bounded_case16594_cell0_source_word_box_environment_def =
  define_literal "bounded_case16594_cell0_source_word_box_environment"
    ``:bounded_interval64 list`` box_environment_tm;
val bounded_case16594_cell0_source_word_radii_def =
  define_literal "bounded_case16594_cell0_source_word_radii"
    ``:word64 list`` radii_tm;
val bounded_case16594_cell0_source_word_certificates_def =
  define_literal "bounded_case16594_cell0_source_word_certificates"
    ``:bounded_analytic64_certificate list`` prepared_certificates_tm;

Definition bounded_case16594_cell0_authenticated_word_box_environment_def:
  bounded_case16594_cell0_authenticated_word_box_environment =
    [BoundedInterval64
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
       (BoundedSigned64 F 6336265608550w)]
End

fun cv_list_elements tm =
  let
    val (head,arguments) = strip_comb tm;
    val constructor = fst (dest_const head)
  in
    case (constructor,arguments) of
      ("Num",[number]) =>
        if aconv number numSyntax.zero_tm then []
        else raise Fail "nonzero authenticated object-list terminator"
    | ("Pair",[item,items]) => item :: cv_list_elements items
    | _ => raise Fail "malformed authenticated object-list payload"
  end;

fun cv_list_from_definition definition =
  listSyntax.mk_list (cv_list_elements (rhs (concl definition)),``:cv``);

val object_center_environment_tm =
  cv_list_from_definition
    compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_center_boxes_cv_def;
val object_box_environment_tm =
  cv_list_from_definition
    compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_outer_boxes_cv_def;

val bounded_case16594_cell0_authenticated_object_center_environment_def =
  define_literal "bounded_case16594_cell0_authenticated_object_center_environment"
    ``:cv list`` object_center_environment_tm;
val bounded_case16594_cell0_authenticated_object_box_environment_def =
  define_literal "bounded_case16594_cell0_authenticated_object_box_environment"
    ``:cv list`` object_box_environment_tm;

val _ = development_stage "before_center_coverage";
Theorem bounded_case16594_cell0_source_word_center_covers_authenticated:
  LIST_REL bounded_interval64_covers_object_q
    bounded_case16594_cell0_source_word_center_environment
    bounded_case16594_cell0_authenticated_object_center_environment
Proof
  simp
    [bounded_case16594_cell0_source_word_center_environment_def,
     bounded_case16594_cell0_authenticated_object_center_environment_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
     compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def,
     compute_boundedIntervalTheory.bounded_interval64_lower_def,
     compute_boundedIntervalTheory.bounded_interval64_upper_def,
     compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> wordsLib.WORD_EVAL_TAC
  >> intLib.ARITH_TAC
QED
val _ = development_stage "after_center_coverage";

Theorem bounded_case16594_cell0_authenticated_word_box_covers_authenticated:
  LIST_REL bounded_interval64_covers_object_q
    bounded_case16594_cell0_authenticated_word_box_environment
    bounded_case16594_cell0_authenticated_object_box_environment
Proof
  simp
    [bounded_case16594_cell0_authenticated_word_box_environment_def,
     bounded_case16594_interval64_outward_one_def,
     bounded_case16594_cell0_source_word_box_environment_def,
     bounded_case16594_cell0_authenticated_object_box_environment_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
     compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def,
     compute_boundedIntervalTheory.bounded_interval64_lower_def,
     compute_boundedIntervalTheory.bounded_interval64_upper_def,
     compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> wordsLib.WORD_EVAL_TAC
  >> intLib.ARITH_TAC
QED
val _ = development_stage "after_box_coverage";

val authenticated_box_eval =
  SIMP_CONV (srw_ss())
    [bounded_case16594_cell0_authenticated_word_box_environment_def,
     bounded_case16594_interval64_outward_one_def,
     bounded_case16594_cell0_source_word_box_environment_def]
    ``bounded_case16594_cell0_authenticated_word_box_environment``;
val authenticated_box_tm = rhs (concl authenticated_box_eval);
val (authenticated_box_items,_) = listSyntax.dest_list authenticated_box_tm;
val _ =
  if List.length authenticated_box_items = 6 then ()
  else raise Fail "authenticated word box did not normalize to six values";
val prepared_program_eval = EVAL ``bounded_case16594_prepared_program``;

val runtime_trace_tm =
  list_mk_comb
    (prim_mk_const
       {Name="bounded_analytic64_program_runtime_certificate_trace",
        Thy="compute_boundedAnalyticRuntimeCertificateTrace"},
     [radii_tm,center_environment_tm,authenticated_box_tm,
      ``bounded_case16594_prepared_program``,
      pairSyntax.mk_pair
        (listSyntax.mk_list ([],``:bounded_taylor64``),
         prepared_certificates_tm)]);
val runtime_trace_computation_tm =
  rhs (concl (REWRITE_CONV [prepared_program_eval] runtime_trace_tm));

val bounded_case16594_cell0_authenticated_word_runtime_trace_def =
  new_definition
    ("bounded_case16594_cell0_authenticated_word_runtime_trace_def",
     mk_eq
       (mk_var
         ("bounded_case16594_cell0_authenticated_word_runtime_trace",
          type_of runtime_trace_tm),
        runtime_trace_tm));

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

val _ = development_stage "before_runtime_cv_eval";
val runtime_trace_literal_eval = time cv_eval runtime_trace_computation_tm;
val _ = development_stage "after_runtime_cv_eval";
val runtime_trace_eval =
  REWRITE_RULE [GSYM prepared_program_eval] runtime_trace_literal_eval;
val runtime_trace_value_tm = rhs (concl runtime_trace_eval);
val runtime_trace_result_tm = optionSyntax.dest_some runtime_trace_value_tm;
val (runtime_final_state_tm,runtime_packets_tm) =
  pairSyntax.dest_pair runtime_trace_result_tm;
val (runtime_stack_tm,runtime_remaining_certificates_tm) =
  pairSyntax.dest_pair runtime_final_state_tm;
val (runtime_stack_items,_) = listSyntax.dest_list runtime_stack_tm;
val (runtime_remaining_certificate_items,_) =
  listSyntax.dest_list runtime_remaining_certificates_tm;
val runtime_result_tm =
  case runtime_stack_items of
    [result] => result
  | _ => raise Fail "authenticated-box runtime did not leave one result";
val _ =
  if List.null runtime_remaining_certificate_items then ()
  else raise Fail "authenticated-box runtime did not consume certificates";
val (runtime_packets,_) = listSyntax.dest_list runtime_packets_tm;
val _ =
  if List.length runtime_packets = 134 then ()
  else raise Fail "unexpected authenticated-box runtime-certificate count";

val bounded_case16594_cell0_authenticated_word_runtime_final_state_def =
  define_literal "bounded_case16594_cell0_authenticated_word_runtime_final_state"
    (type_of runtime_final_state_tm) runtime_final_state_tm;
val bounded_case16594_cell0_authenticated_word_result_def =
  define_literal "bounded_case16594_cell0_authenticated_word_result"
    ``:bounded_taylor64`` runtime_result_tm;
val bounded_case16594_cell0_authenticated_word_runtime_packets_def =
  define_literal "bounded_case16594_cell0_authenticated_word_runtime_packets"
    ``:bounded_interval64 list`` runtime_packets_tm;

val bounded_case16594_cell0_authenticated_word_runtime_trace_value =
  save_thm
    ("bounded_case16594_cell0_authenticated_word_runtime_trace_value",
     REWRITE_RULE
       [GSYM authenticated_box_eval,
        GSYM bounded_case16594_cell0_authenticated_word_runtime_trace_def]
       runtime_trace_eval);

Theorem bounded_case16594_cell0_authenticated_word_runtime_trace_exact:
  bounded_case16594_cell0_authenticated_word_runtime_trace =
    SOME
      (bounded_case16594_cell0_authenticated_word_runtime_final_state,
       bounded_case16594_cell0_authenticated_word_runtime_packets) /\
  LENGTH bounded_case16594_cell0_authenticated_word_runtime_packets = 134
Proof
  rw
    [bounded_case16594_cell0_authenticated_word_runtime_trace_value,
     bounded_case16594_cell0_authenticated_word_runtime_final_state_def,
     bounded_case16594_cell0_authenticated_word_runtime_packets_def]
QED

Theorem bounded_case16594_cell0_authenticated_word_runtime_final_state_shape:
  bounded_case16594_cell0_authenticated_word_runtime_final_state =
    ([bounded_case16594_cell0_authenticated_word_result],[])
Proof
  rw
    [bounded_case16594_cell0_authenticated_word_runtime_final_state_def,
     bounded_case16594_cell0_authenticated_word_result_def]
QED

val runtime_program_run_eval =
  MATCH_MP
    compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_projects_run
    runtime_trace_eval;

val bounded_case16594_cell0_authenticated_word_program_run =
  save_thm
    ("bounded_case16594_cell0_authenticated_word_program_run",
     REWRITE_RULE
       [GSYM bounded_case16594_cell0_source_word_radii_def,
        GSYM bounded_case16594_cell0_source_word_center_environment_def,
        GSYM authenticated_box_eval,
        GSYM bounded_case16594_cell0_source_word_certificates_def,
        GSYM bounded_case16594_cell0_authenticated_word_result_def]
       runtime_program_run_eval);

Theorem bounded_case16594_cell0_authenticated_word_program_eval:
  bounded_analytic64_program_eval
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_prepared_program
      bounded_case16594_cell0_source_word_certificates =
    SOME bounded_case16594_cell0_authenticated_word_result
Proof
  simp
    [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_eval_def,
     bounded_case16594_cell0_authenticated_word_program_run]
QED

val _ = export_theory ();
