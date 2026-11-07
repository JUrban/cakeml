(*****************************************************************************
 * Bounded executable probe for the proved complete direct case-16594 path. *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeDirectProbeProg
Ancestors
  compute_boundedCase16594WordWholeDirectExternalInputProg
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends
  "compute_boundedCase16594WordWholeDirectExternalInputProg";

(*
 * Both [compute_exp] and [cv] deliberately use the HOL constructor names
 * [Num] and [Pair].  A CakeML quotation cannot disambiguate those constructors
 * from surrounding function applications, so keep every probe-side cv
 * construction behind an explicitly typed, translated definition.
 *)
Definition bounded_case16594_direct_probe_cv_num_def:
  bounded_case16594_direct_probe_cv_num (value:num) = (Num value : cv)
End

Definition bounded_case16594_direct_probe_cv_pair_def:
  bounded_case16594_direct_probe_cv_pair (left:cv) (right:cv) =
    (Pair left right : cv)
End

Definition bounded_case16594_direct_probe_replace_cv_head_def:
  (bounded_case16594_direct_probe_replace_cv_head replacement
      (Pair head tail : cv) = Pair replacement tail) /\
  (bounded_case16594_direct_probe_replace_cv_head replacement
      (Num value : cv) = Num 0)
End

Definition bounded_case16594_direct_probe_drop_cv_head_def:
  (bounded_case16594_direct_probe_drop_cv_head (Pair head tail : cv) = tail) /\
  (bounded_case16594_direct_probe_drop_cv_head (Num value : cv) = Num 0)
End

val _ = translate bounded_case16594_direct_probe_cv_num_def;
val _ = translate bounded_case16594_direct_probe_cv_pair_def;
val _ = translate bounded_case16594_direct_probe_replace_cv_head_def;
val _ = translate bounded_case16594_direct_probe_drop_cv_head_def;

Quote main = cakeml:
  fun read_all path =
    let
      val stream = TextIO.openIn path
      val contents = TextIO.inputAll stream
      val _ = TextIO.closeIn stream
    in
      contents
    end

  fun mutate_first_byte bytes =
    case bytes of
      [] => []
    | head::tail => #"\000"::tail

  fun positive_verdict result =
    case result of
      None => "rejected\n"
    | Some value => "accepted\n"

  fun rejection_verdict result =
    case result of
      None => "accepted\n"
    | Some value => "rejected\n"

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
        None => "rejected\n"
      | Some certificate =>
          case cv_flat_parse_list packed_cells_text of
            None => "rejected\n"
          | Some packed_cells =>
              case cv_flat_parse_list tokens_text of
                None => "rejected\n"
              | Some tokens =>
                  case cv_flat_parse_list jobs_text of
                    None => "rejected\n"
                  | Some jobs =>
                      let
                        val source_descriptor =
                          bounded_case16594_direct_probe_cv_pair
                            bounded_case16594_generic_prefix167_codes_cv
                            (bounded_case16594_direct_probe_cv_pair
                              bounded_case16594_generic_prefix167_sources_cv
                              packed_cells)
                        fun run certificate_value source_value dim_value
                            tokens_value jobs_value =
                          bounded_case16594_word_whole_direct_checker
                            certificate_value source_value dim_value
                            tokens_value jobs_value
                      in
                        if mode = "positive" then
                          positive_verdict
                            (run certificate source_descriptor
                              (bounded_case16594_direct_probe_cv_num 6)
                              tokens jobs)
                        else if mode = "certificate" then
                          (case cv_pack_byte_tree
                              (mutate_first_byte certificate_bytes) of
                             None => "accepted\n"
                           | Some changed =>
                               rejection_verdict
                                 (run changed source_descriptor
                                   (bounded_case16594_direct_probe_cv_num 6)
                                   tokens jobs))
                        else if mode = "source" then
                          rejection_verdict
                            (run certificate
                              (bounded_case16594_direct_probe_cv_pair
                                (bounded_case16594_direct_probe_cv_num 0)
                                (bounded_case16594_direct_probe_cv_pair
                                  bounded_case16594_generic_prefix167_sources_cv
                                  packed_cells))
                              (bounded_case16594_direct_probe_cv_num 6)
                              tokens jobs)
                        else if mode = "cell" then
                          rejection_verdict
                            (run certificate
                              (bounded_case16594_direct_probe_cv_pair
                                bounded_case16594_generic_prefix167_codes_cv
                                (bounded_case16594_direct_probe_cv_pair
                                  bounded_case16594_generic_prefix167_sources_cv
                                  (bounded_case16594_direct_probe_replace_cv_head
                                    (bounded_case16594_direct_probe_cv_num 0)
                                    packed_cells)))
                              (bounded_case16594_direct_probe_cv_num 6)
                              tokens jobs)
                        else if mode = "token" then
                          rejection_verdict
                            (run certificate source_descriptor
                              (bounded_case16594_direct_probe_cv_num 6)
                              (bounded_case16594_direct_probe_replace_cv_head
                                (bounded_case16594_direct_probe_cv_num 999)
                                tokens) jobs)
                        else if mode = "job" then
                          rejection_verdict
                            (run certificate source_descriptor
                              (bounded_case16594_direct_probe_cv_num 6) tokens
                              (bounded_case16594_direct_probe_replace_cv_head
                                (bounded_case16594_direct_probe_cv_num 0)
                                jobs))
                        else if mode = "dimension" then
                          rejection_verdict
                            (run certificate source_descriptor
                              (bounded_case16594_direct_probe_cv_num 0)
                              tokens jobs)
                        else if mode = "truncated-cells" then
                          rejection_verdict
                            (run certificate
                              (bounded_case16594_direct_probe_cv_pair
                                bounded_case16594_generic_prefix167_codes_cv
                                (bounded_case16594_direct_probe_cv_pair
                                  bounded_case16594_generic_prefix167_sources_cv
                                  (bounded_case16594_direct_probe_drop_cv_head
                                    packed_cells)))
                              (bounded_case16594_direct_probe_cv_num 6)
                              tokens jobs)
                        else if mode = "truncated-jobs" then
                          rejection_verdict
                            (run certificate source_descriptor
                              (bounded_case16594_direct_probe_cv_num 6) tokens
                              (bounded_case16594_direct_probe_drop_cv_head jobs))
                        else if mode = "truncated-tokens" then
                          rejection_verdict
                            (run certificate source_descriptor
                              (bounded_case16594_direct_probe_cv_num 6)
                              (bounded_case16594_direct_probe_drop_cv_head
                                tokens) jobs)
                        else "rejected\n"
                      end
    end

  fun main u =
    case CommandLine.arguments () of
      [mode,certificate_path,packed_cells_path,tokens_path,jobs_path] =>
        TextIO.print
          (check_case16594_whole_direct mode certificate_path
            packed_cells_path tokens_path jobs_path)
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
