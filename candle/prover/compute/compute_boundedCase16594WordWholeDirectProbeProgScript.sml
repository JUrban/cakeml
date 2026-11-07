(*****************************************************************************
 * Bounded executable probe for the proved complete direct case-16594 path. *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeDirectProbeProg
Ancestors
  compute_boundedCase16594WordWholeDirectExternalInputProg
  compute_boundedCase16594Cell0WholeHolLightData
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends
  "compute_boundedCase16594WordWholeDirectExternalInputProg";

fun translate_closed def =
  def |> CONV_RULE (RAND_CONV EVAL) |> translate;

val _ = translate_closed
  compute_boundedCase16594Cell0WholeHolLightDataTheory.bounded_case16594_cell0_whole_hol_light_result_def;

Quote main = cakeml:
  fun read_all path =
    let
      val stream = TextIO.openIn path
      val contents = TextIO.inputAll stream
      val _ = TextIO.closeIn stream
    in
      contents
    end

  fun replace_cv_head replacement value =
    case value of
      Pair head tail => Pair replacement tail
    | _ => Num 0

  fun drop_cv_head value =
    case value of
      Pair head tail => tail
    | _ => Num 0

  fun mutate_first_byte bytes =
    case bytes of
      [] => []
    | head::tail => #"\000"::tail

  fun check_case16594_whole_direct mode certificate_path packed_cells_path
      tokens_path jobs_path =
    let
      val certificate_bytes =
        String.explode (read_all certificate_path)
      val packed_cells_text =
        String.explode (read_all packed_cells_path)
      val tokens_text = String.explode (read_all tokens_path)
      val jobs_text = String.explode (read_all jobs_path)
    in
      case cv_pack_byte_tree certificate_bytes of
        None => false
      | Some certificate =>
          case cv_flat_parse_list packed_cells_text of
            None => false
          | Some packed_cells =>
              case cv_flat_parse_list tokens_text of
                None => false
              | Some tokens =>
                  case cv_flat_parse_list jobs_text of
                    None => false
                  | Some jobs =>
                      let
                        val source_descriptor =
                          Pair bounded_case16594_generic_prefix167_codes_cv
                            (Pair
                              bounded_case16594_generic_prefix167_sources_cv
                              packed_cells)
                        val expected = Some
                          bounded_case16594_cell0_whole_hol_light_result
                        fun run certificate_value source_value dim_value
                            tokens_value jobs_value =
                          bounded_case16594_word_whole_direct_checker
                            certificate_value source_value dim_value
                            tokens_value jobs_value
                      in
                        if mode = "positive" then
                          run certificate source_descriptor (Num 6)
                            tokens jobs = expected
                        else if mode = "certificate" then
                          (case cv_pack_byte_tree
                              (mutate_first_byte certificate_bytes) of
                             None => true
                           | Some changed =>
                               run changed source_descriptor (Num 6)
                                 tokens jobs <> expected)
                        else if mode = "source" then
                          run certificate
                            (Pair (Num 0)
                              (Pair
                                bounded_case16594_generic_prefix167_sources_cv
                                packed_cells))
                            (Num 6) tokens jobs <> expected
                        else if mode = "cell" then
                          run certificate
                            (Pair bounded_case16594_generic_prefix167_codes_cv
                              (Pair
                                bounded_case16594_generic_prefix167_sources_cv
                                (replace_cv_head (Num 0) packed_cells)))
                            (Num 6) tokens jobs <> expected
                        else if mode = "token" then
                          run certificate source_descriptor (Num 6)
                            (replace_cv_head (Num 999) tokens) jobs <>
                            expected
                        else if mode = "job" then
                          run certificate source_descriptor (Num 6) tokens
                            (replace_cv_head (Num 0) jobs) <> expected
                        else if mode = "dimension" then
                          run certificate source_descriptor (Num 0)
                            tokens jobs <> expected
                        else if mode = "truncated-cells" then
                          run certificate
                            (Pair bounded_case16594_generic_prefix167_codes_cv
                              (Pair
                                bounded_case16594_generic_prefix167_sources_cv
                                (drop_cv_head packed_cells)))
                            (Num 6) tokens jobs <> expected
                        else if mode = "truncated-jobs" then
                          run certificate source_descriptor (Num 6) tokens
                            (drop_cv_head jobs) <> expected
                        else if mode = "truncated-tokens" then
                          run certificate source_descriptor (Num 6)
                            (drop_cv_head tokens) jobs <> expected
                        else false
                      end
    end

  fun main u =
    case CommandLine.arguments () of
      [mode,certificate_path,packed_cells_path,tokens_path,jobs_path] =>
        if check_case16594_whole_direct mode certificate_path
             packed_cells_path tokens_path jobs_path
        then TextIO.print "accepted\n"
        else TextIO.print "rejected\n"
    | _ => TextIO.output TextIO.stdErr
        "usage: direct-checker MODE CERTIFICATE PACKED_CELLS TOKENS JOBS\n"

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

Definition compute_bounded_case16594_word_whole_direct_probe_prog_def:
  compute_bounded_case16594_word_whole_direct_probe_prog = ^prog
End

val _ = export_theory ();
