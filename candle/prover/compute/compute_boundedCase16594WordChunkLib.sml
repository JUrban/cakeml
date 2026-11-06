(*****************************************************************************
 * Runtime finite-authentication builder for genuine case-16594 word cells.
 *
 * A separate certificate-only data theory must first materialize the proved
 * input and certificate literals.  This runtime library then checks the
 * complete 167-step trace and packet guards and instantiates the production
 * entry theorem.  The separation is mandatory because certificate preparation
 * and runtime tracing generated distinct converters for a shared datatype.
 *****************************************************************************)
structure compute_boundedCase16594WordChunkLib = struct

open HolKernel boolLib bossLib;

fun pad4 index =
  let
    val text = Int.toString index;
    val width = String.size text;
  in
    String.implode (List.tabulate (Int.max (0,4 - width),fn _ => #"0")) ^ text
  end;

fun cell_prefix cell_index =
  "bounded_case16594_all_cell" ^ pad4 cell_index;

fun stage message =
  (print ("CANDLE_CASE16594_WORD_CHUNK " ^ message ^ "\n");
   TextIO.flushOut TextIO.stdOut);

fun define_literal name ty tm =
  new_definition (name ^ "_def",mk_eq (mk_var (name,ty),tm));

fun conjoin_theorems [theorem] = theorem
  | conjoin_theorems (theorem::theorems) =
      CONJ theorem (conjoin_theorems theorems)
  | conjoin_theorems [] = raise Fail "empty word-cell chunk";

fun theorem_variable name theorem =
  case List.find
         (fn variable => fst (dest_var variable) = name)
         (free_vars (concl theorem)) of
    SOME variable => variable
  | NONE => raise Fail ("missing theorem variable " ^ name);

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
val radius_pairs_constant =
  ``bounded_taylor_radius_pairs :
      word64 list -> (word64 # word64 # bool) list option``;
val result_accepts_constant =
  prim_mk_const
    {Name="bounded_packed_analytic_result_accepts",
     Thy="compute_boundedPackedAnalyticCheck"};

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

fun install_runtime_conversions () =
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
    val result =
      time cv_transLib.cv_eval (instantiate_fields fields guard_template);
    val _ =
      print
        ("CANDLE_CASE16594_WORD_CHUNK_GUARD theorem=" ^ theorem_name ^
         " result=" ^ term_to_string (rhs (concl result)) ^ "\n");
  in
    save_thm (theorem_name,result)
  end;

fun prove_atan_packet_contract prefix runtime_packets
      (packet_index,packet_offset) =
  let
    val packet_prefix = prefix ^ "_word_atan" ^ Int.toString packet_index;
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

fun authenticate_cells
      {data_theory:string,cell_indices:int list,chunk_prefix:string} =
  let
    val _ = install_runtime_conversions ();
    val prepared_program_eval = EVAL ``bounded_case16594_prepared_program``;
    val atan_packet_offsets = [7,31,46,70,85,109,124];
    val generic_entry_theorem =
      compute_boundedCase16594WordConvertedAcceptedEntryEvalTheory.bounded_case16594_word_converted_complete_accepted_entry_eval;

    fun fetch suffix cell_index =
      DB.fetch data_theory (cell_prefix cell_index ^ suffix);

    fun authenticate_cell cell_index =
      let
        val prefix = cell_prefix cell_index;
        val input_value = fetch "_prepared_input_option_value" cell_index;
        val certificates_value =
          fetch "_prepared_certificates_option_value" cell_index;
        val prepared_input_tm =
          optionSyntax.dest_some (rhs (concl input_value));
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
          optionSyntax.dest_some (rhs (concl certificates_value));
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
        val _ = stage ("before_cell" ^ pad4 cell_index ^ "_runtime_trace");
        val runtime_trace_literal_eval =
          time cv_transLib.cv_eval runtime_trace_computation_tm;
        val _ = stage ("after_cell" ^ pad4 cell_index ^ "_runtime_trace");
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
        val word_result_tm =
          case runtime_stack of
            [result] => result
          | _ => raise Fail (prefix ^ " non-singleton final stack");
        val _ =
          if List.null runtime_remaining_certificates andalso
             List.length runtime_packets = 134 then ()
          else raise Fail (prefix ^ " rejected or changed packet topology");

        val certificates_def =
          define_literal (prefix ^ "_word_certificates")
            ``:bounded_analytic64_certificate list``
            prepared_certificates_tm;
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
            (prove_atan_packet_contract prefix runtime_packets)
            ([0,1,2,3,4,5,6],atan_packet_offsets);
        val conversion_identities =
          map
            (fn word_field =>
              EVAL (mk_comb (interval_to_object_q,word_field)))
            (List.concat
              (map
                (fn offset =>
                  List.take (List.drop (runtime_packets,offset),8))
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

        val word_radii_def =
          define_literal (prefix ^ "_word_radii")
            (type_of radii_tm) radii_tm;
        val word_center_boxes_def =
          define_literal (prefix ^ "_word_center_boxes")
            (type_of center_environment_tm) center_environment_tm;
        val word_outer_boxes_def =
          define_literal (prefix ^ "_word_outer_boxes")
            (type_of box_environment_tm) box_environment_tm;
        val word_result_def =
          define_literal (prefix ^ "_word_result")
            (type_of word_result_tm) word_result_tm;
        val word_radii_constant = lhs (concl word_radii_def);
        val word_center_boxes_constant = lhs (concl word_center_boxes_def);
        val word_outer_boxes_constant = lhs (concl word_outer_boxes_def);
        val word_result_constant = lhs (concl word_result_def);
        val radius_pairs_eval =
          EVAL (mk_comb (radius_pairs_constant,radii_tm));
        val word_weights_tm =
          optionSyntax.dest_some (rhs (concl radius_pairs_eval));
        val word_weights_def =
          define_literal (prefix ^ "_word_weights")
            (type_of word_weights_tm) word_weights_tm;
        val word_weights_constant = lhs (concl word_weights_def);
        val radius_pairs =
          save_thm
            (prefix ^ "_word_radius_pairs",
             REWRITE_RULE
               [GSYM word_radii_def,GSYM word_weights_def]
               radius_pairs_eval);

        fun prove_closed suffix tm definition =
          save_thm
            (prefix ^ suffix,prove (tm,rw [definition] >> EVAL_TAC));

        val radii_length =
          prove_closed "_word_radii_length"
            (Term.subst
              [{redex=``word_radii:word64 list``,
                residue=word_radii_constant}]
              ``LENGTH (word_radii:word64 list) = 6``)
            word_radii_def;
        val center_boxes_length =
          prove_closed "_word_center_boxes_length"
            (Term.subst
              [{redex=``word_center_boxes:bounded_interval64 list``,
                residue=word_center_boxes_constant}]
              ``LENGTH (word_center_boxes:bounded_interval64 list) = 6``)
            word_center_boxes_def;
        val outer_boxes_length =
          prove_closed "_word_outer_boxes_length"
            (Term.subst
              [{redex=``word_outer_boxes:bounded_interval64 list``,
                residue=word_outer_boxes_constant}]
              ``LENGTH (word_outer_boxes:bounded_interval64 list) = 6``)
            word_outer_boxes_def;
        val center_boxes_valid =
          prove_closed "_word_center_boxes_valid"
            (Term.subst
              [{redex=``word_center_boxes:bounded_interval64 list``,
                residue=word_center_boxes_constant}]
              ``EVERY bounded_interval64_valid
                  (word_center_boxes:bounded_interval64 list)``)
            word_center_boxes_def;
        val outer_boxes_valid =
          prove_closed "_word_outer_boxes_valid"
            (Term.subst
              [{redex=``word_outer_boxes:bounded_interval64 list``,
                residue=word_outer_boxes_constant}]
              ``EVERY bounded_interval64_valid
                  (word_outer_boxes:bounded_interval64 list)``)
            word_outer_boxes_def;
        val trace_call_exact =
          save_thm
            (prefix ^ "_word_runtime_trace_call_exact",
             REWRITE_RULE
               [trace_def,GSYM word_radii_def,GSYM word_center_boxes_def,
                GSYM word_outer_boxes_def,GSYM certificates_def,
                GSYM packets_def,GSYM word_result_def]
               trace_exact);
        val result_accepts =
          save_thm
            (prefix ^ "_word_result_accepts",
             prove
               (mk_comb (result_accepts_constant,word_result_constant),
                rw
                  [word_result_def,
                   compute_boundedPackedAnalyticCheckTheory.bounded_packed_analytic_result_accepts_def,
                   compute_boundedIntervalTheory.bounded_interval64_upper_def,
                   compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_def,
                   compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def]
                >> wordsLib.WORD_EVAL_TAC));
        val specialized_entry_theorem =
          INST
            [{redex=theorem_variable "word_radii" generic_entry_theorem,
              residue=word_radii_constant},
             {redex=theorem_variable "word_center_boxes" generic_entry_theorem,
              residue=word_center_boxes_constant},
             {redex=theorem_variable "word_outer_boxes" generic_entry_theorem,
              residue=word_outer_boxes_constant},
             {redex=theorem_variable "weights" generic_entry_theorem,
              residue=word_weights_constant},
             {redex=theorem_variable "word_certificates" generic_entry_theorem,
              residue=certificates_constant},
             {redex=theorem_variable "word_result" generic_entry_theorem,
              residue=word_result_constant},
             {redex=theorem_variable "packets" generic_entry_theorem,
              residue=packets_constant},
             {redex=theorem_variable "clock" generic_entry_theorem,
              residue=``compute_default_clock``}]
            generic_entry_theorem;
        val entry_premises =
          conjoin_theorems
            [radii_length,center_boxes_length,outer_boxes_length,
             center_boxes_valid,outer_boxes_valid,radius_pairs,
             trace_call_exact,packet_contract,result_accepts,
             compute_boundedCase16594WordConvertedAcceptedEntryEvalTheory.bounded_case16594_word_converted_default_clock_capacity];
        val entry_eval_unnamed =
          MP specialized_entry_theorem entry_premises;
        val (entry_eval_lhs,_) = dest_eq (concl entry_eval_unnamed);
        val (entry_eval_head,entry_eval_arguments) =
          strip_comb entry_eval_lhs;
        val _ =
          if fst (dest_const entry_eval_head) = "compute_eval" andalso
             List.length entry_eval_arguments = 4 then ()
          else raise Fail (prefix ^ " malformed entry-evaluation conclusion");
        val entry_cexp_tm = List.nth (entry_eval_arguments,2);
        val entry_cexp_def =
          define_literal (prefix ^ "_word_converted_entry_cexp")
            (type_of entry_cexp_tm) entry_cexp_tm;
        val entry_eval =
          save_thm
            (prefix ^ "_word_converted_entry_eval",
             REWRITE_RULE [GSYM entry_cexp_def] entry_eval_unnamed);
        val _ = stage ("after_cell" ^ pad4 cell_index ^ "_entry_eval");
      in
        {trace_exact=trace_exact,
         packet_contract=packet_contract,
         entry_eval=entry_eval}
      end;

    val results = map authenticate_cell cell_indices;
    val packet_contracts = map #packet_contract results;
    val entry_evals = map #entry_eval results;
    val packet_contracts_conjunction =
      save_thm
        (chunk_prefix ^ "_word_dispatch_packet_contracts",
         conjoin_theorems packet_contracts);
    val entry_evals_conjunction =
      save_thm
        (chunk_prefix ^ "_word_converted_entry_evals",
         conjoin_theorems entry_evals);
  in
    {results=results,
     packet_contracts=packet_contracts_conjunction,
     entry_evals=entry_evals_conjunction}
  end;

end
