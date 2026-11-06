(*****************************************************************************
 * Production entry-evaluation discriminator for genuine cells 1--3.
 *
 * The preceding prefix-4 theory authenticates the complete fixed-word trace
 * and every packet guard.  This theory crosses the actual production-entry
 * boundary for the three new cells by instantiating the reusable word-object
 * theorem.  All cell terms are extracted from saved kernel theorems rather
 * than duplicated as a second handwritten data representation.
 *****************************************************************************)
Theory compute_boundedCase16594Prefix4WordConvertedEntryEval
Ancestors
  compute_boundedCase16594Prefix4WordPacketContracts
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib

fun define_literal name ty tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,ty),tm));

fun theorem_variable name theorem =
  case List.find
         (fn variable => fst (dest_var variable) = name)
         (free_vars (concl theorem)) of
    SOME variable => variable
  | NONE => raise Fail ("missing theorem variable " ^ name);

fun conjoin_theorems [theorem] = theorem
  | conjoin_theorems (theorem::theorems) =
      CONJ theorem (conjoin_theorems theorems)
  | conjoin_theorems [] = raise Fail "no entry premises";

val runtime_trace_definitions =
  [compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell1_word_runtime_trace_def,
   compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell2_word_runtime_trace_def,
   compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell3_word_runtime_trace_def];
val runtime_trace_exact_theorems =
  [compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell1_word_runtime_trace_exact,
   compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell2_word_runtime_trace_exact,
   compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell3_word_runtime_trace_exact];
val certificate_definitions =
  [compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell1_word_certificates_def,
   compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell2_word_certificates_def,
   compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell3_word_certificates_def];
val packet_definitions =
  [compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell1_word_runtime_packets_def,
   compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell2_word_runtime_packets_def,
   compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell3_word_runtime_packets_def];
val packet_contract_theorems =
  [compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell1_word_dispatch_packet_contracts,
   compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell2_word_dispatch_packet_contracts,
   compute_boundedCase16594Prefix4WordPacketContractsTheory.bounded_case16594_prefix4_cell3_word_dispatch_packet_contracts];

val radius_pairs_constant =
  ``bounded_taylor_radius_pairs :
      word64 list -> (word64 # word64 # bool) list option``;
val result_accepts_constant =
  prim_mk_const
    {Name="bounded_packed_analytic_result_accepts",
     Thy="compute_boundedPackedAnalyticCheck"};

val generic_entry_theorem =
  compute_boundedCase16594WordConvertedAcceptedEntryEvalTheory.bounded_case16594_word_converted_complete_accepted_entry_eval;

fun prove_cell_entry cell_index =
  let
    val local_index = cell_index - 1;
    val index_name = Int.toString cell_index;
    val prefix = "bounded_case16594_prefix4_cell" ^ index_name;
    val trace_def = List.nth (runtime_trace_definitions,local_index);
    val trace_exact = List.nth (runtime_trace_exact_theorems,local_index);
    val certificates_def = List.nth (certificate_definitions,local_index);
    val packets_def = List.nth (packet_definitions,local_index);
    val packet_contract = List.nth (packet_contract_theorems,local_index);
    val _ =
      (print ("CANDLE_CASE16594_PREFIX4_ENTRY before_cell" ^ index_name ^ "\n");
       TextIO.flushOut TextIO.stdOut);

    val (_,runtime_trace_call) = dest_eq (concl trace_def);
    val (runtime_trace_head,runtime_trace_arguments) =
      strip_comb runtime_trace_call;
    val _ =
      if fst (dest_const runtime_trace_head) =
           "bounded_analytic64_program_runtime_certificate_trace" andalso
         List.length runtime_trace_arguments = 5 then ()
      else raise Fail (prefix ^ " malformed runtime trace definition");
    val word_radii_tm = List.nth (runtime_trace_arguments,0);
    val word_center_boxes_tm = List.nth (runtime_trace_arguments,1);
    val word_outer_boxes_tm = List.nth (runtime_trace_arguments,2);
    val initial_state_tm = List.nth (runtime_trace_arguments,4);
    val (initial_stack_tm,word_certificates_tm) =
      pairSyntax.dest_pair initial_state_tm;
    val (initial_stack,_) = listSyntax.dest_list initial_stack_tm;
    val _ =
      if List.null initial_stack then ()
      else raise Fail (prefix ^ " nonempty initial trace stack");

    val (_,runtime_trace_value) = dest_eq (concl trace_exact);
    val runtime_trace_result = optionSyntax.dest_some runtime_trace_value;
    val (runtime_final_state_tm,word_packets_tm) =
      pairSyntax.dest_pair runtime_trace_result;
    val (runtime_stack_tm,runtime_remaining_certificates_tm) =
      pairSyntax.dest_pair runtime_final_state_tm;
    val (runtime_stack,_) = listSyntax.dest_list runtime_stack_tm;
    val (runtime_remaining_certificates,_) =
      listSyntax.dest_list runtime_remaining_certificates_tm;
    val word_result_tm =
      case runtime_stack of
        [result] => result
      | _ => raise Fail (prefix ^ " non-singleton final trace stack");
    val _ =
      if List.null runtime_remaining_certificates then ()
      else raise Fail (prefix ^ " unconsumed trace certificates");

    val word_certificates_constant = lhs (concl certificates_def);
    val word_packets_constant = lhs (concl packets_def);
    val _ =
      if aconv word_certificates_tm (rhs (concl certificates_def)) andalso
         aconv word_packets_tm word_packets_constant then ()
      else raise Fail (prefix ^ " trace/data identity drift");

    val word_radii_def =
      define_literal (prefix ^ "_word_radii")
        (type_of word_radii_tm) word_radii_tm;
    val word_center_boxes_def =
      define_literal (prefix ^ "_word_center_boxes")
        (type_of word_center_boxes_tm) word_center_boxes_tm;
    val word_outer_boxes_def =
      define_literal (prefix ^ "_word_outer_boxes")
        (type_of word_outer_boxes_tm) word_outer_boxes_tm;
    val word_result_def =
      define_literal (prefix ^ "_word_result")
        (type_of word_result_tm) word_result_tm;

    val word_radii_constant = lhs (concl word_radii_def);
    val word_center_boxes_constant = lhs (concl word_center_boxes_def);
    val word_outer_boxes_constant = lhs (concl word_outer_boxes_def);
    val word_result_constant = lhs (concl word_result_def);

    val radius_pairs_eval =
      EVAL (mk_comb (radius_pairs_constant,word_radii_tm));
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

    fun prove_closed name tm definition =
      save_thm
        (name,prove (tm,rw [definition] >> EVAL_TAC));

    val radii_length =
      prove_closed (prefix ^ "_word_radii_length")
        (Term.subst
          [{redex=``word_radii:word64 list``,residue=word_radii_constant}]
          ``LENGTH (word_radii:word64 list) = 6``)
        word_radii_def;
    val center_boxes_length =
      prove_closed (prefix ^ "_word_center_boxes_length")
        (Term.subst
          [{redex=``word_center_boxes:bounded_interval64 list``,
            residue=word_center_boxes_constant}]
          ``LENGTH (word_center_boxes:bounded_interval64 list) = 6``)
        word_center_boxes_def;
    val outer_boxes_length =
      prove_closed (prefix ^ "_word_outer_boxes_length")
        (Term.subst
          [{redex=``word_outer_boxes:bounded_interval64 list``,
            residue=word_outer_boxes_constant}]
          ``LENGTH (word_outer_boxes:bounded_interval64 list) = 6``)
        word_outer_boxes_def;
    val center_boxes_valid =
      prove_closed (prefix ^ "_word_center_boxes_valid")
        (Term.subst
          [{redex=``word_center_boxes:bounded_interval64 list``,
            residue=word_center_boxes_constant}]
          ``EVERY bounded_interval64_valid
              (word_center_boxes:bounded_interval64 list)``)
        word_center_boxes_def;
    val outer_boxes_valid =
      prove_closed (prefix ^ "_word_outer_boxes_valid")
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
          residue=word_certificates_constant},
         {redex=theorem_variable "word_result" generic_entry_theorem,
          residue=word_result_constant},
         {redex=theorem_variable "packets" generic_entry_theorem,
          residue=word_packets_constant},
         {redex=theorem_variable "clock" generic_entry_theorem,
          residue=``compute_default_clock``}]
        generic_entry_theorem;
    val entry_premises =
      conjoin_theorems
        [radii_length,center_boxes_length,outer_boxes_length,
         center_boxes_valid,outer_boxes_valid,radius_pairs,
         trace_call_exact,packet_contract,result_accepts,
         compute_boundedCase16594WordConvertedAcceptedEntryEvalTheory.bounded_case16594_word_converted_default_clock_capacity];
    val entry_eval_unnamed = MP specialized_entry_theorem entry_premises;
    val (entry_eval_lhs,_) = dest_eq (concl entry_eval_unnamed);
    val (entry_eval_head,entry_eval_arguments) = strip_comb entry_eval_lhs;
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
  in
    entry_eval
  end;

val bounded_case16594_prefix4_cells1_through3_word_converted_entry_evals =
  save_thm
    ("bounded_case16594_prefix4_cells1_through3_word_converted_entry_evals",
     conjoin_theorems (map prove_cell_entry [1,2,3]));

val _ = export_theory ();
