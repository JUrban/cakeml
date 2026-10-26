(*****************************************************************************
 * Development executable for the data-driven case-10173 checker.
 *
 * All four per-inequality values are external inputs.  The certificate is
 * packed into the same balanced cv representation used by the witnessed
 * dispatch seam.  Source, jobs, and roots use the canonical flat prefix
 * representation exported from Candle.  None of these values is embedded in
 * this program as the supplied payload.  The current development checker is
 * still specialized to case 10173 and therefore compiles its expected source
 * identity through the existing historical closed call.  The full certificate
 * and 4,173 supplied jobs and roots are not compiled in, but that source
 * identity still brings a small amount of case-specific closed-call data.
 * Acceptance is decided by the authenticated checker.  This executable is an
 * R2 integration test, not yet the reusable all-NL runtime admitted by R3.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10WitnessedFastProg
Ancestors
  compute_boundedCase10173PackedDecimalAuthenticatedProg
  compute_cvPackedBytesRuntime
  compute_registeredCase10173AuthenticatedFastDispatch
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends
  "compute_boundedCase10173PackedDecimalAuthenticatedProg";

(* Compact certificate construction. *)
val _ = translate
  compute_cvPackedBytesTheory.cv_packed_bytes_chunk_limit_def;
val _ = translate cv_pack_byte_chunk_aux_def;
val _ = translate cv_packed_byte_leaf_def;
val _ = translate cv_packed_byte_branch_def;
val _ = translate cv_pack_byte_leaves_aux_def;
val _ = translate cv_pack_byte_tree_round_def;
val _ = translate cv_balance_byte_tree_def;
val _ = translate cv_pack_byte_tree_def;

(* Canonical external cv-data parser. *)
val _ = translate cv_flat_space_def;
val _ = translate cv_flat_skip_space_def;
val _ = translate cv_flat_digit_value_def;
val _ = translate cv_flat_parse_digits_def;
val _ = translate cv_flat_num_result_def;
val _ = translate cv_flat_parse_term_def;
val _ = translate cv_flat_parse_one_def;
val _ = translate cv_flat_parse_list_aux_def;
val _ = translate cv_flat_parse_list_def;

(* The balanced decoder and the same authenticated Boolean used by the
   proved fast-dispatch refinement. *)
val _ = translate compute_cvPackedBytesTheory.cv_unpack_byte_chunk_def;
val _ = translate compute_cvPackedBytesTheory.cv_unpack_byte_tree_append_def;
val _ = translate compute_cvPackedBytesTheory.cv_unpack_byte_tree_def;
val _ = translate compute_pureFastTheory.compute_exp_to_cv_def;
val _ = translate
  compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def;
val _ = translate
  compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_source_program_def;
val _ = translate
  compute_registeredCase10173AuthenticatedFastDispatchTheory.registered_case10173_decimal_authenticated_fast_checker_def;

Definition registered_case10173_external_witnessed_checker_def:
  registered_case10173_external_witnessed_checker
      certificate source_program encoded_jobs encoded_roots <=>
    case cv_unpack_byte_tree certificate of
    | NONE => F
    | SOME bytes =>
        registered_case10173_decimal_authenticated_fast_checker
          bytes source_program encoded_jobs encoded_roots
End

val _ = translate registered_case10173_external_witnessed_checker_def;

Quote main = cakeml:
  fun read_all path =
    let
      val stream = TextIO.openIn path
      val contents = TextIO.inputAll stream
      val _ = TextIO.closeIn stream
    in
      contents
    end

  fun check_external_case10173 certificate_path source_path jobs_path roots_path =
    let
      val certificate_bytes = String.explode (read_all certificate_path)
      val source_text = String.explode (read_all source_path)
      val jobs_text = String.explode (read_all jobs_path)
      val roots_text = String.explode (read_all roots_path)
    in
      case cv_pack_byte_tree certificate_bytes of
        None => false
      | Some certificate =>
          case cv_flat_parse_one source_text of
            None => false
          | Some source_program =>
              case cv_flat_parse_list jobs_text of
                None => false
              | Some encoded_jobs =>
                  case cv_flat_parse_list roots_text of
                    None => false
                  | Some encoded_roots =>
                      registered_case10173_external_witnessed_checker
                        certificate source_program encoded_jobs encoded_roots
    end

  fun main u =
    case CommandLine.arguments () of
      [certificate_path,source_path,jobs_path,roots_path] =>
        if check_external_case10173
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

Definition compute_registered_case10173_tag10_witnessed_fast_prog_def:
  compute_registered_case10173_tag10_witnessed_fast_prog = ^prog
End

val _ = export_theory ();
