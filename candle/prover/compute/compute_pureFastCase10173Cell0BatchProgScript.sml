(*****************************************************************************
 * Shared-preparation timing program for the exact genuine cell-0 call.
 *
 * The equation bundle, call, and expected result are evaluated once and
 * passed to the repetition loop.  Consequently a run separates process/data
 * preparation from the recurring cost of the same complete evaluator.  This
 * is deliberately a repeated-cell control, not a varied-certificate batch.
 *****************************************************************************)
Theory compute_pureFastCase10173Cell0BatchProg
Ancestors
  compute_pureFastCase10173Cell0Prog
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_pureFastCase10173Cell0Prog";

Definition pure_fast_case10173_cell0_repeat_with_def:
  pure_fast_case10173_cell0_repeat_with ceqs cexp expected 0 = T /\
  pure_fast_case10173_cell0_repeat_with ceqs cexp expected (SUC n) =
    (compute_pure_fast_eval ceqs cexp = SOME expected /\
     pure_fast_case10173_cell0_repeat_with ceqs cexp expected n)
End

Definition pure_fast_case10173_cell0_batch_def:
  pure_fast_case10173_cell0_batch n =
    pure_fast_case10173_cell0_repeat_with
      registered_case10173_cell0_ceqs
      registered_case10173_cell0_cexp
      registered_case10173_cell0_result n
End

Theorem pure_fast_case10173_cell0_batch_value:
  !n. pure_fast_case10173_cell0_batch n
Proof
  simp [pure_fast_case10173_cell0_batch_def]
  >> Induct
  >> simp [pure_fast_case10173_cell0_repeat_with_def,
           compute_pureFastCase10173Cell0TestTheory.registered_case10173_cell0_pure_fast_eval_value]
QED

val _ = translate pure_fast_case10173_cell0_repeat_with_def;
val _ = translate pure_fast_case10173_cell0_batch_def;

Quote main = cakeml:
  if pure_fast_case10173_cell0_batch 5
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

Definition compute_pure_fast_case10173_cell0_batch_prog_def:
  compute_pure_fast_case10173_cell0_batch_prog = ^prog
End

val _ = export_theory ();
