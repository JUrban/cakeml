(*****************************************************************************
 * Small typed executable for the direct compact-topology stack machine.    *
 *                                                                           *
 * This deliberately excludes the complete numerical checker and generic    *
 * evaluator translation ancestry.  It is a bounded representation probe.   *
 *****************************************************************************)
Theory compute_boundedCase16594WordDirectTopologyLightProg
Ancestors
  basisProg
  compute_cvPackedBytesRuntime
  compute_boundedCase16594WordDirectTopology
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "basisProg";

val _ = register_type ``:compute_exec$cv``;

val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_space_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_skip_space_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_digit_value_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_parse_digits_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_num_result_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_parse_term_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_parse_one_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_parse_list_aux_def;
val _ = translate
  compute_cvPackedBytesRuntimeTheory.cv_flat_parse_list_def;

val _ = translate
  compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_cv_list_length_def;
val _ = translate
  compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_boxes_join_def;
val _ = translate
  compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_boxes_split_exact_from_def;
val _ = translate
  compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_topology_transition_def;
val _ = translate
  compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_topology_run_def;
val _ = translate
  compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_topology_result_def;

fun translate_closed def =
  def |> CONV_RULE (RAND_CONV EVAL) |> translate;

val _ = translate_closed
  compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_complete875_topology_result_def;

Quote main = cakeml:
  fun topology_read_all path =
    let
      val stream = TextIO.openIn path
      val contents = TextIO.inputAll stream
      val _ = TextIO.closeIn stream
    in
      contents
    end

  fun topology_describe expected result =
    case result of
      None => "none\n"
    | Some actual =>
        if actual = expected then "accepted\n" else "some-different\n"

  fun topology_light mode tokens_path jobs_path =
    if mode = "literal" then
      let
        val source =
          Pair (Num 1)
            (Pair (Num 2)
              (Pair (Num 3)
                (Pair (Num 4)
                  (Pair (Num 5)
                    (Pair (Num 6) (Num 0))))))
        val tokens = Pair (Num 0) (Num 0)
        val jobs =
          Pair (Pair (Num 7) (Pair (Num 8) source)) (Num 0)
        val expected = Pair (Num 1)
          (Pair (Num 0) (Pair source (Num 0)))
      in
        topology_describe expected
          (bounded_case16594_direct_topology_result (Num 6) tokens jobs)
      end
    else
      let
        val tokens_text = String.explode (topology_read_all tokens_path)
        val jobs_text = String.explode (topology_read_all jobs_path)
      in
        case cv_flat_parse_list tokens_text of
          None => "parse-tokens\n"
        | Some tokens =>
            case cv_flat_parse_list jobs_text of
              None => "parse-jobs\n"
            | Some jobs =>
                topology_describe
                  bounded_case16594_complete875_topology_result
                  (bounded_case16594_direct_topology_result (Num 6)
                    tokens jobs)
      end

  fun main u =
    case CommandLine.arguments () of
      [mode,tokens_path,jobs_path] =>
        TextIO.print (topology_light mode tokens_path jobs_path)
    | _ => TextIO.output TextIO.stdErr
        "usage: direct-topology-light MODE TOKENS JOBS\n"

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

Definition compute_bounded_case16594_word_direct_topology_light_prog_def:
  compute_bounded_case16594_word_direct_topology_light_prog = ^prog
End

val _ = export_theory ();
