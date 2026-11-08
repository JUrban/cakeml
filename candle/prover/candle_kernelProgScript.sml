(*
  Adds Candle specific functions to the kernel module from the saved direct
  compute suffix.  The expensive pure nonlinear checker and the stateful
  compute wrapper are translated in reusable predecessor theories; this final
  layer adds printing, closes Kernel, and extracts the complete program.
*)
Theory candle_kernelProg
Libs
  preamble ml_translatorLib ml_monad_translatorLib ml_progLib
  basisFunctionsLib runtime_checkLib
Ancestors
  candle_directComputeKernelProg print_thm runtime_check

val _ = m_translation_extends "candle_directComputeKernelProg";

val _ = (use_long_names := false);

val _ = ml_prog_update open_local_block;

val r = translate ty_to_v_def;
val r = translate term_to_v_def;
val r = translate thm_to_v_def;
val r = translate update_to_v_def;
val r = translate thm_to_string_def;

val _ = ml_prog_update open_local_in_block;

Quote add_cakeml:
  val print_thm = fn th => case th of Sequent tms c =>
    let
      val ctxt = !the_context
      val str = thm_to_string ctxt th
      val arr = Word8Array.array 0 (Word8.fromInt 0)
    in
      #(kernel_ffi) str arr
    end;
End

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);

(* Extract the complete Candle kernel program. *)

val _ = Globals.max_print_depth := 10;

fun define_abbrev_conv name tm = let
  val def = define_abbrev true name tm
  in GSYM def |> SPEC_ALL end

Theorem candle_prog_thm =
  get_Decls_thm (get_ml_prog_state())
  |> CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_code"))
  |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_env"))
  |> CONV_RULE ((RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_state"));

Theorem EqualityType_TYPE_TYPE = EqualityType_rule [] “:type”;

Theorem EqualityType_TERM_TYPE = EqualityType_rule [] “:term”;

Theorem EqualityType_THM_TYPE = EqualityType_rule [] “:thm”;

Theorem EqualityType_UPDATE_TYPE = EqualityType_rule [] “:update”;

val _ = (print_asts := true);
