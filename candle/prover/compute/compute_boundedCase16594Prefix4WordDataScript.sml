(*****************************************************************************
 * Prepared word inputs and certificates for genuine case-16594 cells 1--3.
 *
 * This theory deliberately stops before loading the runtime-trace cv theory.
 * Certificate preparation and runtime tracing independently generated cv
 * converters for the certificate datatype; materializing the proved source
 * values here keeps each computation in its own authenticated representation
 * context.  The downstream packet theory consumes only these HOL literals.
 *****************************************************************************)
Theory compute_boundedCase16594Prefix4WordData
Ancestors
  compute_boundedCase16594PreparedInput
  compute_boundedCase16594PreparedCertificatesCV
Libs
  bossLib preamble wordsLib cv_transLib

fun development_stage name =
  (print ("CANDLE_CASE16594_PREFIX4_DATA_STAGE " ^ name ^ "\n");
   TextIO.flushOut TextIO.stdOut);

val input_rows_tm =
  rhs
    (concl
      compute_boundedCase16594InputDataTheory.bounded_case16594_inputs_def);
val center_radius_rows_tm =
  rhs
    (concl
      compute_boundedCase16594CenterRadiusDataTheory.bounded_case16594_center_radius_inputs_def);
val certificate_plan_rows_tm =
  rhs
    (concl
      compute_boundedCase16594AnalyticCertificateDataTheory.bounded_case16594_certificate_plans_def);

val (input_rows,_) = listSyntax.dest_list input_rows_tm;
val (center_radius_rows,_) = listSyntax.dest_list center_radius_rows_tm;
val (certificate_plan_rows,_) = listSyntax.dest_list certificate_plan_rows_tm;

val _ =
  if List.length input_rows = 875 andalso
     List.length center_radius_rows = 875 andalso
     List.length certificate_plan_rows = 875 then ()
  else raise Fail "unexpected case16594 source row count";

val prepare_input_tm =
  prim_mk_const
    {Name="bounded_case16594_prepare_input",
     Thy="compute_boundedCase16594PreparedInput"};
val prepare_certificate_list_tm =
  prim_mk_const
    {Name="bounded_case16594_prepare_certificate_list",
     Thy="compute_boundedCase16594PreparedCertificates"};

fun define_literal name ty tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,ty),tm));

fun prepare_cell cell_index =
  let
    val index_name = Int.toString cell_index;
    val prefix = "bounded_case16594_prefix4_cell" ^ index_name;
    val input_option_tm =
      mk_comb
        (mk_comb (prepare_input_tm,List.nth (input_rows,cell_index)),
         List.nth (center_radius_rows,cell_index));
    val certificates_option_tm =
      mk_comb
        (prepare_certificate_list_tm,
         List.nth (certificate_plan_rows,cell_index));
    val input_def =
      define_literal (prefix ^ "_prepared_input_option")
        ``:bounded_case16594_prepared_input option`` input_option_tm;
    val certificates_def =
      define_literal (prefix ^ "_prepared_certificates_option")
        ``:bounded_analytic64_certificate list option``
        certificates_option_tm;
    val input_value =
      save_thm
        (prefix ^ "_prepared_input_option_value",
         REWRITE_RULE [GSYM input_def] (EVAL input_option_tm));
    val _ = development_stage ("before_cell" ^ index_name ^ "_certificates");
    val certificates_value =
      save_thm
        (prefix ^ "_prepared_certificates_option_value",
         REWRITE_RULE [GSYM certificates_def]
           (time cv_eval certificates_option_tm));
    val _ = development_stage ("after_cell" ^ index_name ^ "_certificates");
    val prepared_certificates =
      optionSyntax.dest_some (rhs (concl certificates_value));
    val (certificate_values,_) = listSyntax.dest_list prepared_certificates;
    val _ =
      if List.length certificate_values = 31 then ()
      else raise Fail (prefix ^ " certificate width drift");
  in
    (input_value,certificates_value)
  end;

val _ = development_stage "before_cells1_through3";
val prefix4_word_data_results = map prepare_cell [1,2,3];
val _ = development_stage "after_cells1_through3";

val _ = export_theory ();
