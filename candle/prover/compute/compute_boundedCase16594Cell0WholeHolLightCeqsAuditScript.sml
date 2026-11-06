(*****************************************************************************
 * Mechanical audit of the two names duplicated between the imported        *
 * whole-call slice and the production dispatcher environment.               *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WholeHolLightCeqsAudit
Ancestors
  compute_boundedCase16594Cell0WholeHolLightData
  compute_boundedCase16594ObjectDispatchCell0Data
Libs
  bossLib preamble

Theorem bounded_case16594_cell0_whole_hol_light_duplicate_lookups:
  ALOOKUP bounded_case16594_cell0_whole_hol_light_ceqs
    «candle_cv_bool_and» =
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
    «candle_cv_bool_and» /\
  ALOOKUP bounded_case16594_cell0_whole_hol_light_ceqs
    «candle_cv_list_length» =
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
    «candle_cv_list_length»
Proof
  rw
    [compute_boundedCase16594Cell0WholeHolLightDataTheory.bounded_case16594_cell0_whole_hol_light_ceqs_def,
     compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def]
QED

val _ = export_theory ();
