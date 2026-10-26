(* Development executable for the reusable external NL checker.
 *
 * The four command-line payload roles are stable across supported families:
 * certificate bytes, source descriptor, encoded jobs, and encoded roots.
 * Family selection is performed only by the authenticated checker contracts.
 *)
Theory compute_registeredNLExternalWitnessedFastProg
Ancestors
  compute_registeredNLExternalWitnessedCheckerProg
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends
  "compute_registeredNLExternalWitnessedCheckerProg";

Quote main = cakeml:
  fun read_all path =
    let
      val stream = TextIO.openIn path
      val contents = TextIO.inputAll stream
      val _ = TextIO.closeIn stream
    in
      contents
    end

  fun check_external_nl certificate_path source_path jobs_path roots_path =
    let
      val certificate_bytes = String.explode (read_all certificate_path)
      val source_text = String.explode (read_all source_path)
      val jobs_text = String.explode (read_all jobs_path)
      val roots_text = String.explode (read_all roots_path)
    in
      case cv_pack_byte_tree certificate_bytes of
        None => false
      | Some certificate =>
          case cv_external_parse_one source_text of
            None => false
          | Some source_program =>
              case cv_flat_parse_list jobs_text of
                None => false
              | Some encoded_jobs =>
                  case cv_flat_parse_list roots_text of
                    None => false
                  | Some encoded_roots =>
                      registered_nl_external_witnessed_checker
                        certificate source_program encoded_jobs encoded_roots
    end

  fun main u =
    case CommandLine.arguments () of
      [certificate_path,source_path,jobs_path,roots_path] =>
        if check_external_nl
             certificate_path source_path jobs_path roots_path
        then TextIO.print "accepted\n"
        else TextIO.print "rejected\n"
    | _ => TextIO.output TextIO.stdErr
        "usage: checker CERTIFICATE SOURCE JOBS ROOTS\n"

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

Definition compute_registered_nl_external_witnessed_fast_prog_def:
  compute_registered_nl_external_witnessed_fast_prog = ^prog
End

val _ = export_theory ();
