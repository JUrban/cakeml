(*****************************************************************************
 * Bounded multi-cell discriminator for the genuine case-16594 word packets.
 *
 * Cell 0 already has a complete authenticated word trace and packet-contract
 * theorem.  This theory projects genuine cells 1--3 from the pinned 875-row
 * input/certificate dictionaries, evaluates the unchanged 167-instruction
 * word trace, and checks every production atan guard in the resulting packet
 * streams.  It deliberately stops at four cells: the purpose is to validate
 * the all-cell data/proof shape before scaling the finite authentication.
 *****************************************************************************)
Theory compute_boundedCase16594Prefix4WordPacketContracts
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Prefix4WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
Libs
  bossLib preamble wordsLib cv_transLib

fun development_stage name =
  (print ("CANDLE_CASE16594_PREFIX4_PACKET_STAGE " ^ name ^ "\n");
   TextIO.flushOut TextIO.stdOut);

val runtime_trace_constant =
  prim_mk_const
    {Name="bounded_analytic64_program_runtime_certificate_trace",
     Thy="compute_boundedAnalyticRuntimeCertificateTrace"};
val interval_to_object_q =
  prim_mk_const
    {Name="bounded_interval64_object_q_cv",
     Thy="compute_boundedAnalyticObjectCertificateRefinement"};
val atan_contract_constant =
  prim_mk_const
    {Name="bounded_case16594_object_atan_fixed_pure_contract",
     Thy="compute_boundedCase16594ObjectCertifiedAtanDispatchInvariant"};
val packet_contract_constant =
  prim_mk_const
    {Name="bounded_case16594_word_dispatch_packet_contracts",
     Thy="compute_boundedCase16594Cell0WordDispatchPacketContracts"};

(* Reinstall the runtime datatype conversions used by the trace evaluator. *)
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

val prepared_program_eval = EVAL ``bounded_case16594_prepared_program``;
val atan_packet_offsets = [7,31,46,70,85,109,124];

val prepared_input_value_theorems =
  [compute_boundedCase16594Prefix4WordDataTheory.bounded_case16594_prefix4_cell1_prepared_input_option_value,
   compute_boundedCase16594Prefix4WordDataTheory.bounded_case16594_prefix4_cell2_prepared_input_option_value,
   compute_boundedCase16594Prefix4WordDataTheory.bounded_case16594_prefix4_cell3_prepared_input_option_value];
val prepared_certificates_value_theorems =
  [compute_boundedCase16594Prefix4WordDataTheory.bounded_case16594_prefix4_cell1_prepared_certificates_option_value,
   compute_boundedCase16594Prefix4WordDataTheory.bounded_case16594_prefix4_cell2_prepared_certificates_option_value,
   compute_boundedCase16594Prefix4WordDataTheory.bounded_case16594_prefix4_cell3_prepared_certificates_option_value];

val field_variables =
  [``center_input:cv``, ``box_input:cv``, ``center_result:cv``,
   ``center_square:cv``, ``center_derivative:cv``, ``box_square:cv``,
   ``box_derivative:cv``, ``box_derivative_square:cv``];

val guard_templates =
  [("center_result",
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_atn_certificate»
          [from_cv (center_input:cv); from_cv (center_result:cv)])``),
   ("center_square",
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_encloses»
          [from_cv (center_square:cv);
           App «candle_cv_q_interval_normalize»
             [App «candle_cv_q_interval_square»
               [from_cv (center_input:cv)]]])``),
   ("center_inverse",
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_inv_certificate»
          [App «candle_cv_q_packed_object_atn_denominator»
             [from_cv (center_square:cv)];
           from_cv (center_derivative:cv)])``),
   ("box_square",
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_encloses»
          [from_cv (box_square:cv);
           App «candle_cv_q_interval_normalize»
             [App «candle_cv_q_interval_square»
               [from_cv (box_input:cv)]]])``),
   ("box_inverse",
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_inv_certificate»
          [App «candle_cv_q_packed_object_atn_denominator»
             [from_cv (box_square:cv)];
           from_cv (box_derivative:cv)])``),
   ("derivative_square",
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_square_outer_certificate»
          [from_cv (box_derivative:cv); from_cv (box_derivative:cv);
           from_cv (box_derivative_square:cv)])``)];

fun define_literal name ty tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,ty),tm));

fun interval_object_q_literal interval =
  rhs (concl (EVAL (mk_comb (interval_to_object_q,interval))));

fun instantiate_fields fields tm =
  Term.subst
    (ListPair.map
      (fn (variable,field) => {redex=variable,residue=field})
      (field_variables,fields)) tm;

fun evaluate_guard packet_prefix fields (guard_name,guard_template) =
  let
    val theorem_name = packet_prefix ^ "_" ^ guard_name ^ "_pure_eval";
    val result = time cv_eval (instantiate_fields fields guard_template);
    val _ =
      print
        ("CANDLE_CASE16594_PREFIX4_GUARD theorem=" ^ theorem_name ^
         " result=" ^ term_to_string (rhs (concl result)) ^ "\n");
  in
    save_thm (theorem_name,result)
  end;

fun prove_atan_packet_contract cell_index runtime_packets
      (packet_index,packet_offset) =
  let
    val packet_prefix =
      "bounded_case16594_prefix4_cell" ^ Int.toString cell_index ^
      "_word_atan" ^ Int.toString packet_index;
    val word_fields = List.take (List.drop (runtime_packets,packet_offset),8);
    val object_fields = map interval_object_q_literal word_fields;
    val guard_theorems =
      map (evaluate_guard packet_prefix object_fields) guard_templates;
    val contract_tm = list_mk_comb (atan_contract_constant,object_fields);
  in
    save_thm
      (packet_prefix ^ "_fixed_pure_contract",
       prove
         (contract_tm,
          simp
            (compute_boundedCase16594ObjectCertifiedAtanDispatchInvariantTheory.bounded_case16594_object_atan_fixed_pure_contract_def::
             guard_theorems)))
  end;

fun prove_cell_packet_contract cell_index =
  let
    val index_name = Int.toString cell_index;
    val prefix = "bounded_case16594_prefix4_cell" ^ index_name;
    val local_index = cell_index - 1;
    val prepared_input_tm =
      optionSyntax.dest_some
        (rhs
          (concl
            (List.nth (prepared_input_value_theorems,local_index))));
    val (prepared_input_constructor,prepared_input_arguments) =
      strip_comb prepared_input_tm;
    val _ =
      if fst (dest_const prepared_input_constructor) =
           "BoundedCase16594PreparedInput" andalso
         List.length prepared_input_arguments = 5 then ()
      else raise Fail (prefix ^ " malformed prepared input");
    val center_environment_tm = List.nth (prepared_input_arguments,0);
    val box_environment_tm = List.nth (prepared_input_arguments,1);
    val radii_tm = List.nth (prepared_input_arguments,2);
    val prepared_certificates_tm =
      optionSyntax.dest_some
        (rhs
          (concl
            (List.nth
              (prepared_certificates_value_theorems,local_index))));
    val (prepared_certificates,_) =
      listSyntax.dest_list prepared_certificates_tm;
    val _ =
      if List.length prepared_certificates = 31 then ()
      else raise Fail (prefix ^ " certificate width drift");
    val runtime_trace_tm =
      list_mk_comb
        (runtime_trace_constant,
         [radii_tm,center_environment_tm,box_environment_tm,
          ``bounded_case16594_prepared_program``,
          pairSyntax.mk_pair
            (listSyntax.mk_list ([],``:bounded_taylor64``),
             prepared_certificates_tm)]);
    val runtime_trace_computation_tm =
      rhs (concl (REWRITE_CONV [prepared_program_eval] runtime_trace_tm));
    val _ = development_stage ("before_cell" ^ index_name ^ "_runtime_trace");
    val runtime_trace_literal_eval = time cv_eval runtime_trace_computation_tm;
    val _ = development_stage ("after_cell" ^ index_name ^ "_runtime_trace");
    val runtime_trace_eval =
      REWRITE_RULE [GSYM prepared_program_eval] runtime_trace_literal_eval;
    val runtime_trace_result_tm =
      optionSyntax.dest_some (rhs (concl runtime_trace_eval));
    val (runtime_final_state_tm,runtime_packets_tm) =
      pairSyntax.dest_pair runtime_trace_result_tm;
    val (runtime_stack_tm,runtime_remaining_certificates_tm) =
      pairSyntax.dest_pair runtime_final_state_tm;
    val (runtime_stack,_) = listSyntax.dest_list runtime_stack_tm;
    val (runtime_remaining_certificates,_) =
      listSyntax.dest_list runtime_remaining_certificates_tm;
    val (runtime_packets,_) = listSyntax.dest_list runtime_packets_tm;
    val _ =
      if List.length runtime_stack = 1 andalso
         List.null runtime_remaining_certificates andalso
         List.length runtime_packets = 134 then ()
      else raise Fail (prefix ^ " rejected or changed packet topology");
    val certificates_def =
      define_literal (prefix ^ "_word_certificates")
        ``:bounded_analytic64_certificate list`` prepared_certificates_tm;
    val packets_def =
      define_literal (prefix ^ "_word_runtime_packets")
        ``:bounded_interval64 list`` runtime_packets_tm;
    val trace_def =
      define_literal (prefix ^ "_word_runtime_trace")
        (type_of runtime_trace_tm) runtime_trace_tm;
    val trace_exact =
      save_thm
        (prefix ^ "_word_runtime_trace_exact",
         REWRITE_RULE
           [GSYM trace_def,GSYM certificates_def,GSYM packets_def]
           runtime_trace_eval);
    val atan_contracts =
      ListPair.map
        (prove_atan_packet_contract cell_index runtime_packets)
        ([0,1,2,3,4,5,6],atan_packet_offsets);
    val conversion_identities =
      map
        (fn word_field =>
          EVAL (mk_comb (interval_to_object_q,word_field)))
        (List.concat
          (map
            (fn offset => List.take (List.drop (runtime_packets,offset),8))
            atan_packet_offsets));
    val certificates_constant = lhs (concl certificates_def);
    val packets_constant = lhs (concl packets_def);
    val contract_tm =
      list_mk_comb
        (packet_contract_constant,[certificates_constant,packets_constant]);
    val packet_contract =
      save_thm
        (prefix ^ "_word_dispatch_packet_contracts",
         prove
           (contract_tm,
            simp
              ([compute_boundedCase16594Cell0WordDispatchPacketContractsTheory.bounded_case16594_word_dispatch_packet_contracts_def,
                certificates_def,packets_def,
                compute_boundedIntervalTheory.bounded_interval64_lower_def,
                compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
                compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
                compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
                compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def] @
               conversion_identities)
            >> simp atan_contracts));
  in
    (trace_exact,packet_contract)
  end;

val _ = development_stage "before_cells1_through3";
val prefix4_new_cell_results = map prove_cell_packet_contract [1,2,3];
val _ = development_stage "after_cells1_through3";

val prefix4_packet_contracts =
  compute_boundedCase16594Cell0WordDispatchPacketContractsTheory.bounded_case16594_cell0_word_dispatch_packet_contracts::
  map snd prefix4_new_cell_results;

fun conjoin_theorems [theorem] = theorem
  | conjoin_theorems (theorem::theorems) =
      CONJ theorem (conjoin_theorems theorems)
  | conjoin_theorems [] = raise Fail "no prefix-4 packet contracts";

val bounded_case16594_prefix4_word_dispatch_packet_contracts =
  save_thm
    ("bounded_case16594_prefix4_word_dispatch_packet_contracts",
     conjoin_theorems prefix4_packet_contracts);

val _ = export_theory ();
