(*****************************************************************************
 * Certificate-only data builder for restartable case-16594 word chunks.
 *
 * Keep this library separate from the runtime-trace helper: the certificate
 * preparation and runtime theories have independently generated converters
 * for a shared datatype.  A data theory must materialize its proved literals
 * before any runtime converter is loaded.
 *****************************************************************************)
structure compute_boundedCase16594WordDataChunkLib = struct

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
  (print ("CANDLE_CASE16594_WORD_DATA_CHUNK " ^ message ^ "\n");
   TextIO.flushOut TextIO.stdOut);

fun define_literal name ty tm =
  new_definition (name ^ "_def",mk_eq (mk_var (name,ty),tm));

fun prepare_data_cells cell_indices =
  let
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
    val (certificate_plan_rows,_) =
      listSyntax.dest_list certificate_plan_rows_tm;
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

    fun prepare_cell cell_index =
      let
        val prefix = cell_prefix cell_index;
        val _ =
          if 0 <= cell_index andalso cell_index < 875 then ()
          else raise Fail (prefix ^ " out-of-range row index");
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
        val _ = stage ("before_cell" ^ pad4 cell_index ^ "_certificates");
        val certificates_value =
          save_thm
            (prefix ^ "_prepared_certificates_option_value",
             REWRITE_RULE [GSYM certificates_def]
               (time cv_transLib.cv_eval certificates_option_tm));
        val _ = stage ("after_cell" ^ pad4 cell_index ^ "_certificates");
        val prepared_certificates =
          optionSyntax.dest_some (rhs (concl certificates_value));
        val (certificate_values,_) =
          listSyntax.dest_list prepared_certificates;
        val _ =
          if List.length certificate_values = 31 then ()
          else raise Fail (prefix ^ " certificate width drift");
      in
        (input_value,certificates_value)
      end;
  in
    map prepare_cell cell_indices
  end;

end
