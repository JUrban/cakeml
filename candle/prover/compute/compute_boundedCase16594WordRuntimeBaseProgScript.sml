(*****************************************************************************
 * Preserved translation base for exact case-16594 runtime data conversion. *
 *****************************************************************************)
Theory compute_boundedCase16594WordRuntimeBaseProg
Ancestors
  compute_boundedCase16594WordConversionProg
  compute_boundedCase16594ObjectDispatchCell0Data
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_boundedCase16594WordConversionProg";

val _ = translate
  compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def;

(* Needed when the pure atan guard expressions are materialized. *)
val _ = translate compute_execTheory.from_cv_def;

val _ = export_theory ();
