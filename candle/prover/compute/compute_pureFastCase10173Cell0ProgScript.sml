(*****************************************************************************
 * Direct CakeML timing program for the exact genuine 271-equation call.
 *
 * The translated evaluator and data are identical to the general evaluator
 * installed in Kernel.compute.  The companion test theory proves its exact
 * result and refinement to the verified evaluator; this program isolates the
 * recurring execution cost from HOL theorem construction and REPL loading.
 *****************************************************************************)
Theory compute_pureFastCase10173Cell0Prog
Ancestors
  basisProg
  compute_pureFastCase10173Cell0Test
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "basisProg";

val _ = register_type ``:compute_syntax$binop``;
val _ = register_type ``:compute_syntax$uop``;
val _ = register_type ``:compute_syntax$compute_exp``;
val _ = register_type ``:compute_exec$cv``;

val _ = translate compute_evalPureTheory.compute_pure_to_num_def;
val _ = translate compute_evalPureTheory.compute_pure_uop_def;
val _ = translate
  (compute_evalPureTheory.compute_pure_binop_def
   |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);
val _ = translate compute_evalPureTheory.compute_pure_remove_binding_def;
val _ = translate compute_evalPureTheory.compute_pure_subst_def;
val _ = translate compute_evalPureTheory.compute_eval_pure_def;
val _ = translate compute_pureFastTheory.compute_exp_to_cv_def;
val _ = translate compute_pureFastTheory.compute_pure_fast_fuel_def;
val _ = translate compute_pureFastTheory.compute_pure_fast_eval_def;

val _ = translate
  compute_registeredCase10173Cell0DataTheory.registered_case10173_cell0_ceqs_def;
val _ = translate
  compute_registeredCase10173Cell0DataTheory.registered_case10173_cell0_cexp_def;
val _ = translate
  compute_registeredCase10173Cell0DataTheory.registered_case10173_cell0_result_def;

Definition pure_fast_case10173_cell0_check_def:
  pure_fast_case10173_cell0_check () =
    (compute_pure_fast_eval registered_case10173_cell0_ceqs
       registered_case10173_cell0_cexp =
     SOME registered_case10173_cell0_result)
End

Theorem pure_fast_case10173_cell0_check_value:
  pure_fast_case10173_cell0_check ()
Proof
  simp [pure_fast_case10173_cell0_check_def,
        registered_case10173_cell0_pure_fast_eval_value]
QED

val _ = translate pure_fast_case10173_cell0_check_def;

Quote main = cakeml:
  if pure_fast_case10173_cell0_check ()
  then TextIO.print "accepted\n"
  else TextIO.print "rejected\n";
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

Definition compute_pure_fast_case10173_cell0_prog_def:
  compute_pure_fast_case10173_cell0_prog = ^prog
End

val _ = export_theory ();
