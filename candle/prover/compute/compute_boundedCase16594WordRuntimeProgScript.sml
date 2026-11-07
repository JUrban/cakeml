(*****************************************************************************
 * Translation closure for the exact case-16594 fixed-word runtime checker. *
 *                                                                           *
 * This layer sits above the shared numerical and pure-evaluator state and   *
 * below the final whole-checker callback.  The functions are translated in *
 * dependency order so failures expose one missing runtime edge at a time.  *
 *****************************************************************************)
Theory compute_boundedCase16594WordRuntimeProg
Ancestors
  compute_boundedCase16594WordSourceIdentityProg
  compute_boundedCase16594WordWholeJobsChecker
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_boundedCase16594WordSourceIdentityProg";

(* Header validation and the complete source/certificate identity check. *)
val _ = translate
  compute_boundedCase16594WordWholeJobsCheckerTheory.bounded_case16594_word_whole_jobs_checker_def;

val _ = export_theory ();
