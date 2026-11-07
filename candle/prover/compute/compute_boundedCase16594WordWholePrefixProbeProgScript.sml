(*****************************************************************************
 * Development-only prefix probe for the complete case-16594 G6 matcher.    *
 *                                                                           *
 * This intentionally stops after a requested number of successful cells.  *
 * It is not a production checker and proves no acceptance claim; it exists *
 * only to measure the time/heap scaling of the already translated numerical *
 * matcher without speculating with another 875-cell high-memory run.        *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholePrefixProbeProg
Ancestors
  compute_boundedCase16594WordWholeExternalInputProg
Libs
  preamble ml_translatorLib ml_progLib basis

Definition bounded_case16594_word_whole_cells_prefix_match_def:
  bounded_case16594_word_whole_cells_prefix_match 0 bytes packed_cells jobs =
      T /\
  bounded_case16594_word_whole_cells_prefix_match (SUC remaining) bytes
      packed_cells jobs =
    case bounded_packed_chars_analytic_cell 6 31 bytes of
    | NONE => F
    | SOME (parsed_cell,rest) =>
        case packed_cells of
        | Pair packed_cell packed_cells_tail =>
            (case jobs of
             | Pair job jobs_tail =>
                 (case bounded_case16594_word_whole_cell_match
                         parsed_cell packed_cell job of
                  | NONE => F
                  | SOME source_box =>
                      bounded_case16594_word_whole_cells_prefix_match
                        remaining rest packed_cells_tail jobs_tail)
             | _ => F)
        | _ => F
End

Definition bounded_case16594_word_whole_prefix_probe_def:
  bounded_case16594_word_whole_prefix_probe remaining certificate
      packed_cells jobs <=>
    case cv_unpack_byte_tree certificate of
    | NONE => F
    | SOME bytes =>
        case bounded_packed_chars_analytic_header 875w 31w bytes of
        | NONE => F
        | SOME rest =>
            bounded_case16594_word_whole_cells_prefix_match remaining rest
              packed_cells jobs
End

val _ = translation_extends
  "compute_boundedCase16594WordWholeExternalInputProg";

val _ = translate bounded_case16594_word_whole_cells_prefix_match_def;
val _ = translate bounded_case16594_word_whole_prefix_probe_def;

Quote main = cakeml:
  fun read_all path =
    let
      val stream = TextIO.openIn path
      val contents = TextIO.inputAll stream
      val _ = TextIO.closeIn stream
    in
      contents
    end

  fun run_prefix mode certificate packed_cells jobs =
    if mode = "0" then
      bounded_case16594_word_whole_prefix_probe 0 certificate
        packed_cells jobs
    else if mode = "1" then
      bounded_case16594_word_whole_prefix_probe 1 certificate
        packed_cells jobs
    else if mode = "2" then
      bounded_case16594_word_whole_prefix_probe 2 certificate
        packed_cells jobs
    else if mode = "4" then
      bounded_case16594_word_whole_prefix_probe 4 certificate
        packed_cells jobs
    else if mode = "8" then
      bounded_case16594_word_whole_prefix_probe 8 certificate
        packed_cells jobs
    else if mode = "16" then
      bounded_case16594_word_whole_prefix_probe 16 certificate
        packed_cells jobs
    else if mode = "32" then
      bounded_case16594_word_whole_prefix_probe 32 certificate
        packed_cells jobs
    else if mode = "64" then
      bounded_case16594_word_whole_prefix_probe 64 certificate
        packed_cells jobs
    else if mode = "128" then
      bounded_case16594_word_whole_prefix_probe 128 certificate
        packed_cells jobs
    else if mode = "256" then
      bounded_case16594_word_whole_prefix_probe 256 certificate
        packed_cells jobs
    else if mode = "512" then
      bounded_case16594_word_whole_prefix_probe 512 certificate
        packed_cells jobs
    else false

  fun check_prefix mode certificate_path packed_cells_path jobs_path =
    let
      val certificate_bytes =
        String.explode (read_all certificate_path)
      val packed_cells_text =
        String.explode (read_all packed_cells_path)
      val jobs_text = String.explode (read_all jobs_path)
    in
      case cv_pack_byte_tree certificate_bytes of
        None => false
      | Some certificate =>
          case cv_flat_parse_list packed_cells_text of
            None => false
          | Some packed_cells =>
              case cv_flat_parse_list jobs_text of
                None => false
              | Some jobs => run_prefix mode certificate packed_cells jobs
    end

  fun main u =
    case CommandLine.arguments () of
      [mode,certificate_path,packed_cells_path,jobs_path] =>
        if check_prefix mode certificate_path packed_cells_path jobs_path
        then TextIO.print "accepted\n"
        else TextIO.print "rejected\n"
    | _ => TextIO.output TextIO.stdErr
        "usage: prefix-probe CELL_COUNT CERTIFICATE PACKED_CELLS JOBS\n"

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

Definition compute_bounded_case16594_word_whole_prefix_probe_prog_def:
  compute_bounded_case16594_word_whole_prefix_probe_prog = ^prog
End

val _ = export_theory ();
