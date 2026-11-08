(*****************************************************************************
 * Minimal reusable translation state for the pure compute evaluator.       *
 *                                                                           *
 * This deliberately excludes the historical case-10173 constants and main  *
 * program from compute_pureFastCase10173Cell0Prog.  G6 needs only the       *
 * general evaluator used by the proved whole-checker topology branch.       *
 *****************************************************************************)
Theory compute_evalPureBaseProg
Ancestors
  compute_boundedPackedAnalyticCheckProg
  compute_evalPure
  compute_pureFast
Libs
  preamble ml_translatorLib ml_progLib

val _ = translation_extends "compute_boundedPackedAnalyticCheckProg";

val _ = register_type ``:compute_syntax$binop``;
val _ = register_type ``:compute_syntax$uop``;
val _ = register_type ``:compute_syntax$compute_exp``;
val _ = register_type ``:compute_exec$cv``;

val (compute_var_name, compute_var_modules) =
  lookup_cons_name "%%compute_syntax%%compute_exp%%Var%%";

val _ =
  if aconv compute_var_name (mlstringSyntax.mk_mlstring "Var_1") andalso
     null compute_var_modules
  then print "CANDLE_COMPUTE_EXP_ABI_CONSTRUCTOR_OK Var_1\n"
  else failwith "reflected checker ABI: compute_exp.Var is not Var_1";

val _ =
  if can (find_term (aconv ``TypeStamp «Var_1» 40``))
         (concl (theorem "COMPUTE_SYNTAX_COMPUTE_EXP_TYPE_def"))
  then print "CANDLE_COMPUTE_EXP_ABI_STAMP_OK Var_1/40\n"
  else failwith "reflected checker ABI: compute_exp stamp is not 40";

val _ = translate compute_evalPureTheory.compute_pure_to_num_def;
val _ = translate compute_evalPureTheory.compute_pure_uop_def;
val _ = translate
  (compute_evalPureTheory.compute_pure_binop_def
   |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);
val _ = translate compute_evalPureTheory.compute_pure_remove_binding_def;
val _ = translate compute_evalPureTheory.compute_pure_subst_def;
val _ = translate compute_evalPureTheory.compute_eval_pure_def;
val _ = translate compute_pureFastTheory.compute_exp_to_cv_def;

val _ = export_theory ();
