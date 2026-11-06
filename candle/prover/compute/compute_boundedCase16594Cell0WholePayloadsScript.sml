(*****************************************************************************
 * Authenticate the four literal payloads of the imported HOL Light whole   *
 * call and expose the topology subcall without re-encoding any data.         *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WholePayloads
Ancestors
  compute_boundedCase16594Cell0WholeCombinedLookups
  compute_payloadListFast
Libs
  bossLib preamble

fun define_literal name term =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,type_of term),term));

val literal_payloads_eval =
  EVAL
    ``compute_literal_call_payloads
        «candle_cv_q_packed_object_whole_check»
        bounded_case16594_cell0_whole_hol_light_entry``;

val literal_payloads_term =
  optionSyntax.dest_some (rhs (concl literal_payloads_eval));

val (literal_payloads,_) = listSyntax.dest_list literal_payloads_term;

val _ =
  if List.length literal_payloads = 4 then ()
  else raise Fail "case16594 cell0 whole-call payload arity drift";

val source_descriptor_def =
  define_literal "bounded_case16594_cell0_whole_source_descriptor"
    (List.nth (literal_payloads,0));
val tree_dim_def =
  define_literal "bounded_case16594_cell0_whole_tree_dim"
    (List.nth (literal_payloads,1));
val tokens_def =
  define_literal "bounded_case16594_cell0_whole_tokens"
    (List.nth (literal_payloads,2));
val encoded_jobs_def =
  define_literal "bounded_case16594_cell0_whole_encoded_jobs"
    (List.nth (literal_payloads,3));

val bounded_case16594_cell0_whole_literal_payloads =
  save_thm
    ("bounded_case16594_cell0_whole_literal_payloads",
     REWRITE_RULE
       [GSYM source_descriptor_def,GSYM tree_dim_def,GSYM tokens_def,
        GSYM encoded_jobs_def]
       literal_payloads_eval);

val bounded_case16594_cell0_whole_entry_from_payloads =
  save_thm
    ("bounded_case16594_cell0_whole_entry_from_payloads",
     MATCH_MP
       compute_payloadListFastTheory.compute_literal_call_payloads_sound
       bounded_case16594_cell0_whole_literal_payloads
     |> SIMP_RULE (srw_ss()) []);

Definition bounded_case16594_cell0_whole_topology_cexp_def:
  bounded_case16594_cell0_whole_topology_cexp =
    App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
      [from_cv bounded_case16594_cell0_whole_tree_dim;
       from_cv bounded_case16594_cell0_whole_tokens;
       from_cv bounded_case16594_cell0_whole_encoded_jobs;
       Num 0]
End

val _ = export_theory ();
