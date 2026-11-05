(*****************************************************************************
 * Cell-0 fixed-word input and typed certificates projected from the pinned
 * 875-cell source fixtures without evaluating or copying the other 874 rows.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WordData
Ancestors
  compute_boundedCase16594PreparedInput
  compute_boundedCase16594PreparedCertificatesCV
Libs
  bossLib preamble wordsLib cv_transLib

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

val cell0_input_tm = List.hd input_rows;
val cell0_center_radius_tm = List.hd center_radius_rows;
val cell0_certificate_plan_tm = List.hd certificate_plan_rows;

val prepare_input_tm =
  prim_mk_const
    {Name="bounded_case16594_prepare_input",
     Thy="compute_boundedCase16594PreparedInput"};
val prepare_certificate_list_tm =
  prim_mk_const
    {Name="bounded_case16594_prepare_certificate_list",
     Thy="compute_boundedCase16594PreparedCertificates"};

val cell0_prepared_input_option_tm =
  mk_comb (mk_comb (prepare_input_tm,cell0_input_tm),cell0_center_radius_tm);
val cell0_prepared_certificates_option_tm =
  mk_comb (prepare_certificate_list_tm,cell0_certificate_plan_tm);

val bounded_case16594_cell0_prepared_input_option_def =
  new_definition
    ("bounded_case16594_cell0_prepared_input_option_def",
     mk_eq
       (mk_var
         ("bounded_case16594_cell0_prepared_input_option",
          ``:bounded_case16594_prepared_input option``),
        cell0_prepared_input_option_tm));

val bounded_case16594_cell0_prepared_certificates_option_def =
  new_definition
    ("bounded_case16594_cell0_prepared_certificates_option_def",
     mk_eq
       (mk_var
         ("bounded_case16594_cell0_prepared_certificates_option",
          ``:bounded_analytic64_certificate list option``),
        cell0_prepared_certificates_option_tm));

val bounded_case16594_cell0_prepared_input_option_value =
  save_thm
    ("bounded_case16594_cell0_prepared_input_option_value",
     REWRITE_RULE
       [GSYM bounded_case16594_cell0_prepared_input_option_def]
       (EVAL cell0_prepared_input_option_tm));

val bounded_case16594_cell0_prepared_certificates_option_value =
  save_thm
    ("bounded_case16594_cell0_prepared_certificates_option_value",
     REWRITE_RULE
       [GSYM bounded_case16594_cell0_prepared_certificates_option_def]
       (cv_eval cell0_prepared_certificates_option_tm));

Theorem bounded_case16594_cell0_prepared_input_exists:
  ?prepared.
    bounded_case16594_cell0_prepared_input_option = SOME prepared
Proof
  rw [bounded_case16594_cell0_prepared_input_option_value]
QED

Theorem bounded_case16594_cell0_prepared_certificates_valid:
  IS_SOME bounded_case16594_cell0_prepared_certificates_option /\
  OPTION_MAP LENGTH bounded_case16594_cell0_prepared_certificates_option =
    SOME 31
Proof
  rw [bounded_case16594_cell0_prepared_certificates_option_value]
QED

val _ = export_theory ();
