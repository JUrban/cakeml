(******************************************************************************
 * Freeze the standard Candle kernel datatype ABI before reflected checkers. *
 *                                                                            *
 * The kernel's pattern-matching proofs depend on the constructor identifiers *
 * and stamps allocated from [basisProg].  Any program prefix installed ahead *
 * of the kernel must therefore extend this theory rather than [basisProg]    *
 * directly.                                                                  *
 ******************************************************************************)
Theory candle_kernelTypesProg
Ancestors
  basisProg holKernel
Libs
  preamble ml_translatorLib ml_progLib

val _ = translation_extends "basisProg";

(* Match the historical names exported by [ml_hol_kernel_funsProg]. *)
val _ = (use_full_type_names := false);

val _ = register_type ``:type``;
val _ = register_type ``:term``;
val _ = register_type ``:thm``;
val _ = register_exn_type ``:hol_exn``;
val _ = register_type ``:update``;

(* Keep later reflected-checker invariants fully qualified, as before. *)
val _ = (use_full_type_names := true);

val (hol_var_name, hol_var_modules) =
  lookup_cons_name "%%holSyntax%%term%%Var%%";

val _ =
  if aconv hol_var_name (mlstringSyntax.mk_mlstring "Var") andalso
     null hol_var_modules
  then print "CANDLE_KERNEL_TYPE_ABI_CONSTRUCTOR_OK Var\n"
  else failwith "Candle kernel type ABI: holSyntax.term.Var is not Var";

val _ =
  if can (find_term (aconv ``TypeStamp «Var» 22``))
         (concl (theorem "TERM_TYPE_def"))
  then print "CANDLE_KERNEL_TYPE_ABI_STAMP_OK Var/22\n"
  else failwith "Candle kernel type ABI: holSyntax.term stamp is not 22";

val _ = export_theory ();
