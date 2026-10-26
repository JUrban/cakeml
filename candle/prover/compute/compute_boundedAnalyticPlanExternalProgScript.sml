(*****************************************************************************
 * Development executable for the versioned generic analytic-plan checker.
 *
 * Certificate bytes, the decoded source program, and plan metadata are all
 * external data.  This program is a behavioral/regression boundary only; its
 * acceptance is not a release claim until the generic analytic refinement
 * theorem and registered Candle handoff are complete.
 *****************************************************************************)
Theory compute_boundedAnalyticPlanExternalProg
Ancestors
  compute_boundedAnalyticPlanCVProg compute_cvNativeRuntime
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_boundedAnalyticPlanCVProg";

(* Accept both the canonical flat cv spelling and the compact native spelling
 * used by the genuine Flyspeck source capture. *)
val _ = translate compute_cvPackedBytesRuntimeTheory.cv_flat_space_def;
val _ = translate compute_cvPackedBytesRuntimeTheory.cv_flat_skip_space_def;
val _ = translate compute_cvPackedBytesRuntimeTheory.cv_flat_digit_value_def;
val _ = translate compute_cvPackedBytesRuntimeTheory.cv_flat_parse_digits_def;
val _ = translate compute_cvPackedBytesRuntimeTheory.cv_flat_num_result_def;
val _ = translate compute_cvPackedBytesRuntimeTheory.cv_flat_parse_term_def;
val _ = translate compute_cvPackedBytesRuntimeTheory.cv_flat_parse_one_def;
val _ = translate compute_cvNativeRuntimeTheory.cv_native_parse_term_def;
val _ = translate compute_cvNativeRuntimeTheory.cv_native_parse_one_def;
val _ = translate compute_cvNativeRuntimeTheory.cv_external_parse_one_def;

Quote main = cakeml:
  fun read_all path =
    let
      val stream = TextIO.openIn path
      val contents = TextIO.inputAll stream
      val _ = TextIO.closeIn stream
    in
      contents
    end

  fun check_external_plan certificate_path source_path metadata_path =
    let
      val certificate_bytes = String.explode (read_all certificate_path)
      val source_text = String.explode (read_all source_path)
      val metadata_text = String.explode (read_all metadata_path)
    in
      case cv_external_parse_one source_text of
        None => false
      | Some source_program =>
          case cv_external_parse_one metadata_text of
            None => false
          | Some metadata =>
              bounded_analytic_source_plan_check
                source_program metadata certificate_bytes
    end

  fun main u =
    case CommandLine.arguments () of
      [certificate_path,source_path,metadata_path] =>
        if check_external_plan certificate_path source_path metadata_path
        then TextIO.print "accepted\n"
        else TextIO.print "rejected\n"
    | _ => TextIO.output TextIO.stdErr
        "usage: checker CERTIFICATE SOURCE METADATA\n"

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

Definition compute_bounded_analytic_plan_external_prog_def:
  compute_bounded_analytic_plan_external_prog = ^prog
End

val _ = export_theory ();
