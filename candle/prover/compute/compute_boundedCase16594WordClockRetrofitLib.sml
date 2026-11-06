(*****************************************************************************
 * Recover clock-parametric entry theorems from completed word-cell          *
 * authentication theories.                                                  *
 *                                                                            *
 * Authentication already saved every closed numerical and guard premise.    *
 * This library only re-instantiates the generic evaluator theorem; it never  *
 * replays the runtime trace or certificate computations.                     *
 *****************************************************************************)
structure compute_boundedCase16594WordClockRetrofitLib = struct

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

fun conjoin_theorems [theorem] = theorem
  | conjoin_theorems (theorem::theorems) =
      CONJ theorem (conjoin_theorems theorems)
  | conjoin_theorems [] = raise Fail "empty word-cell clock retrofit";

val normalized_generic_entry_theorem =
  SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
    compute_boundedCase16594WordConvertedAcceptedEntryEvalTheory.bounded_case16594_word_converted_complete_accepted_entry_eval;

val default_clock_term = ``compute_default_clock``;
val clock_variable = mk_var ("clock",type_of default_clock_term);

val default_capacity_theorem =
  compute_boundedCase16594WordConvertedAcceptedEntryEvalTheory.bounded_case16594_word_converted_default_clock_capacity;

fun save_clock_entry_from_saved_facts
      {prefix:string,entry_cexp_def:thm,default_entry_eval:thm,
       radii_length:thm,center_boxes_length:thm,outer_boxes_length:thm,
       center_boxes_valid:thm,outer_boxes_valid:thm,radius_pairs:thm,
       trace_call_exact:thm,packet_contract:thm,result_accepts:thm} =
  let
    val evaluator_conclusion =
      Term.subst
        [{redex=default_clock_term,residue=clock_variable}]
        (concl default_entry_eval);
    val capacity_condition =
      Term.subst
        [{redex=default_clock_term,residue=clock_variable}]
        (concl default_capacity_theorem);
    val quantified_variables =
      clock_variable ::
      List.filter
        (fn variable => fst (dest_var variable) <> "clock")
        (free_vars evaluator_conclusion);
    val goal =
      list_mk_forall
        (quantified_variables,mk_imp (capacity_condition,evaluator_conclusion));
  in
    save_thm
      (prefix ^ "_word_converted_entry_eval_clock",
       prove
         (goal,
          rpt gen_tac
          >> strip_tac
          >> rw [entry_cexp_def]
          >> irule normalized_generic_entry_theorem
          >> asm_rewrite_tac
               [radii_length,center_boxes_length,outer_boxes_length,
                center_boxes_valid,outer_boxes_valid,radius_pairs,
                trace_call_exact,packet_contract,result_accepts]
          >> metis_tac [trace_call_exact,packet_contract,result_accepts]))
  end;

fun retrofit_cells
      {auth_theory:string,cell_indices:int list,chunk_prefix:string} =
  let
    fun fetch suffix cell_index =
      DB.fetch auth_theory (cell_prefix cell_index ^ suffix);

    fun retrofit_cell cell_index =
      let
        val prefix = cell_prefix cell_index;
        val entry_cexp_def = fetch "_word_converted_entry_cexp_def" cell_index;
        val default_entry_eval = fetch "_word_converted_entry_eval" cell_index;
        val radii_length = fetch "_word_radii_length" cell_index;
        val center_boxes_length = fetch "_word_center_boxes_length" cell_index;
        val outer_boxes_length = fetch "_word_outer_boxes_length" cell_index;
        val center_boxes_valid = fetch "_word_center_boxes_valid" cell_index;
        val outer_boxes_valid = fetch "_word_outer_boxes_valid" cell_index;
        val radius_pairs = fetch "_word_radius_pairs" cell_index;
        val trace_call_exact = fetch "_word_runtime_trace_call_exact" cell_index;
        val packet_contract = fetch "_word_dispatch_packet_contracts" cell_index;
        val result_accepts = fetch "_word_result_accepts" cell_index;
        val clock_entry_eval =
          save_clock_entry_from_saved_facts
            {prefix=prefix,
             entry_cexp_def=entry_cexp_def,
             default_entry_eval=default_entry_eval,
             radii_length=radii_length,
             center_boxes_length=center_boxes_length,
             outer_boxes_length=outer_boxes_length,
             center_boxes_valid=center_boxes_valid,
             outer_boxes_valid=outer_boxes_valid,
             radius_pairs=radius_pairs,
             trace_call_exact=trace_call_exact,
             packet_contract=packet_contract,
             result_accepts=result_accepts};
      in
        clock_entry_eval
      end;

    val entry_evals = map retrofit_cell cell_indices;
    val entry_evals_conjunction =
      save_thm
        (chunk_prefix ^ "_word_converted_entry_evals_clock",
         conjoin_theorems entry_evals);
  in
    {entry_evals=entry_evals,
     entry_evals_conjunction=entry_evals_conjunction}
  end;

end
