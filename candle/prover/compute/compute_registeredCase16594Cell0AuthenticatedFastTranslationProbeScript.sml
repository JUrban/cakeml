(******************************************************************************
 * Pre-bootstrap executable probe for the exact case-16594 cell-0 callback.   *
 *                                                                            *
 * This uses a standalone mlbasicsProg translator state and does not alter     *
 * candle_kernelProg or build a Candle runtime.  The generated closed program  *
 * checks the exact branch, equation-environment rejection, all six entry-     *
 * argument mutations, a wrong entry root, and unchanged fallback.             *
 ******************************************************************************)
Theory compute_registeredCase16594Cell0AuthenticatedFastTranslationProbe
Ancestors
  mlbasicsProg
  compute_fastPrepend
  compute_boundedCase16594Cell0AuthenticatedFastObjectEntryLiteral
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "mlbasicsProg";

val _ = register_type ``:cv``;
val _ = register_type ``:uop``;
val _ = register_type ``:binop``;
val _ = register_type ``:compute_exp``;

Definition case16594_fast_probe_replace_app_argument_def:
  case16594_fast_probe_replace_app_argument index replacement expression =
    case expression of
    | App name arguments => App name (LUPDATE replacement index arguments)
    | _ => Num 0
End

Definition case16594_fast_probe_fallback_def:
  case16594_fast_probe_fallback ceqs cexp = SOME (Num 2 : cv)
End

Definition case16594_fast_callback_translation_probe_def:
  case16594_fast_callback_translation_probe () =
    let ceqs = bounded_case16594_object_dispatch_cell0_ceqs in
    let entry =
      bounded_case16594_cell0_authenticated_fast_object_entry_literal_cexp
    in
    registered_case16594_cell0_authenticated_fast_object_entry_literal_eval
      ceqs entry = SOME (Num 1) /\
    registered_case16594_cell0_authenticated_fast_object_entry_literal_eval
      (TL ceqs) entry = NONE /\
    registered_case16594_cell0_authenticated_fast_object_entry_literal_eval
      ceqs (case16594_fast_probe_replace_app_argument 0 (Num 0) entry) =
      NONE /\
    registered_case16594_cell0_authenticated_fast_object_entry_literal_eval
      ceqs (case16594_fast_probe_replace_app_argument 1 (Num 0) entry) =
      NONE /\
    registered_case16594_cell0_authenticated_fast_object_entry_literal_eval
      ceqs (case16594_fast_probe_replace_app_argument 2 (Num 0) entry) =
      NONE /\
    registered_case16594_cell0_authenticated_fast_object_entry_literal_eval
      ceqs (case16594_fast_probe_replace_app_argument 3 (Num 0) entry) =
      NONE /\
    registered_case16594_cell0_authenticated_fast_object_entry_literal_eval
      ceqs (case16594_fast_probe_replace_app_argument 4 (Num 0) entry) =
      NONE /\
    registered_case16594_cell0_authenticated_fast_object_entry_literal_eval
      ceqs (case16594_fast_probe_replace_app_argument 5 (Num 0) entry) =
      NONE /\
    registered_case16594_cell0_authenticated_fast_object_entry_literal_eval
      ceqs (Num 0) = NONE /\
    compute_fast_eval_prepend
      registered_case16594_cell0_authenticated_fast_object_entry_literal_eval
      case16594_fast_probe_fallback ceqs
      (case16594_fast_probe_replace_app_argument 5 (Num 0) entry) =
      SOME (Num 2)
End

val _ = translate
  compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def;
val _ = translate
  compute_boundedCase16594Cell0AuthenticatedFastObjectEntryLiteralTheory.bounded_case16594_cell0_authenticated_fast_object_entry_literal_cexp_def;
val _ = translate
  compute_boundedCase16594Cell0AuthenticatedFastObjectEntryLiteralTheory.registered_case16594_cell0_authenticated_fast_object_entry_literal_eval_def;
val _ = translate
  compute_fastPrependTheory.compute_fast_eval_prepend_def;
val _ = translate case16594_fast_probe_replace_app_argument_def;
val _ = translate case16594_fast_probe_fallback_def;
val _ = translate case16594_fast_callback_translation_probe_def;

Quote main = cakeml:
  if case16594_fast_callback_translation_probe ()
  then ()
  else raise Bind;
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

Definition compute_registered_case16594_cell0_authenticated_fast_translation_probe_prog_def:
  compute_registered_case16594_cell0_authenticated_fast_translation_probe_prog =
    ^prog
End

val _ = export_theory ();
