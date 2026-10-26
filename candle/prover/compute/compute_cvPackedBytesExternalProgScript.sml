(*****************************************************************************
 * Standalone development executable for the external fast-NL data path.
 *
 * This intentionally performs no NL acceptance check.  It measures and
 * validates certificate packing/unpacking plus canonical parsing of source,
 * jobs, and roots independently of the much larger authenticated-checker
 * translation ancestry.
 *****************************************************************************)
Theory compute_cvPackedBytesExternalProg
Ancestors
  basisProg
  compute_cvPackedBytesRuntime
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "basisProg";

val _ = register_type ``:compute_exec$cv``;

val _ = translate
  compute_cvPackedBytesTheory.cv_packed_bytes_chunk_limit_def;
val _ = translate cv_pack_byte_chunk_aux_def;
val _ = translate cv_packed_byte_leaf_def;
val _ = translate cv_packed_byte_branch_def;
val _ = translate cv_pack_byte_leaves_aux_def;
val _ = translate cv_pack_byte_tree_round_def;
val _ = translate cv_balance_byte_tree_def;
val _ = translate cv_pack_byte_tree_def;

val _ = translate compute_cvPackedBytesTheory.cv_unpack_byte_chunk_def;
val _ = translate compute_cvPackedBytesTheory.cv_unpack_byte_tree_append_def;
val _ = translate compute_cvPackedBytesTheory.cv_unpack_byte_tree_def;

val _ = translate cv_flat_space_def;
val _ = translate cv_flat_skip_space_def;
val _ = translate cv_flat_digit_value_def;
val _ = translate cv_flat_parse_digits_def;
val _ = translate cv_flat_num_result_def;
val _ = translate cv_flat_parse_term_def;
val _ = translate cv_flat_parse_one_def;
val _ = translate cv_flat_parse_list_aux_def;
val _ = translate cv_flat_parse_list_def;

Definition cv_external_certificate_ready_def:
  cv_external_certificate_ready certificate_bytes <=>
    case cv_pack_byte_tree certificate_bytes of
    | NONE => F
    | SOME certificate =>
        cv_unpack_byte_tree certificate = SOME certificate_bytes
End

Definition cv_external_metadata_ready_def:
  cv_external_metadata_ready source_text jobs_text roots_text <=>
    cv_flat_parse_one source_text <> NONE /\
    cv_flat_parse_list jobs_text <> NONE /\
    cv_flat_parse_list roots_text <> NONE
End


Definition cv_external_fast_nl_data_ready_def:
  cv_external_fast_nl_data_ready certificate_bytes source_text jobs_text
      roots_text <=>
    cv_external_certificate_ready certificate_bytes /\
    cv_external_metadata_ready source_text jobs_text roots_text
End

val _ = translate cv_external_certificate_ready_def;
val _ = translate cv_external_metadata_ready_def;
val _ = translate cv_external_fast_nl_data_ready_def;

Quote main = cakeml:
  fun read_all path =
    let
      val stream = TextIO.openIn path
      val contents = TextIO.inputAll stream
      val _ = TextIO.closeIn stream
    in
      contents
    end

  fun main u =
    case CommandLine.arguments () of
      [mode,certificate_path] =>
        if mode = "--certificate" andalso
           cv_external_certificate_ready
             (String.explode (read_all certificate_path))
        then TextIO.print "certificate-ready\n"
        else TextIO.print "rejected\n"
    | [first_path,source_path,jobs_path,roots_path] =>
        if first_path = "--metadata" then
          if cv_external_metadata_ready
               (String.explode (read_all source_path))
               (String.explode (read_all jobs_path))
               (String.explode (read_all roots_path))
          then TextIO.print "metadata-ready\n"
          else TextIO.print "rejected\n"
        else
          let
            val certificate_bytes = String.explode (read_all first_path)
            val source_text = String.explode (read_all source_path)
            val jobs_text = String.explode (read_all jobs_path)
            val roots_text = String.explode (read_all roots_path)
          in
            if cv_external_fast_nl_data_ready
                 certificate_bytes source_text jobs_text roots_text
            then TextIO.print "data-ready\n"
            else TextIO.print "rejected\n"
          end
    | _ => TextIO.output TextIO.stdErr
        "usage: data-check CERT SOURCE JOBS ROOTS | --certificate CERT | --metadata SOURCE JOBS ROOTS\n"

  val _ = main ()
End

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand;

Definition compute_cv_packed_bytes_external_prog_def:
  compute_cv_packed_bytes_external_prog = ^prog
End

val _ = export_theory ();
