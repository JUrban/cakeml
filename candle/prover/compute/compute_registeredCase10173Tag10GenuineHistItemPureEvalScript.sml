(*****************************************************************************
 * One-time proof-producing evaluation of the unchanged genuine historical
 * item in the corrected tag-10 equation environment.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10GenuineHistItemPureEval
Ancestors
  compute_registeredCase10173HistoricalChunk16Tag10Data
  compute_registeredCase10173GenuineProgramMemoEval
  compute_evalPure
Libs
  bossLib preamble cv_transLib

val _ = cv_trans registered_case10173_historical_chunk16_tag10_ceqs_def;

val registered_case10173_tag10_genuine_hist_item_pure_eval =
  time cv_eval
    ``compute_eval_pure 100000
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_item»
          [from_cv registered_case10173_genuine_center_boxes;
           from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_genuine_encoded_radii;
           from_cv registered_case10173_first_job_roots])``;

val _ = save_thm
  ("registered_case10173_tag10_genuine_hist_item_pure_eval",
   registered_case10173_tag10_genuine_hist_item_pure_eval);

Theorem registered_case10173_tag10_genuine_hist_item_pure_eval_value:
  compute_eval_pure 100000
      registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_item»
        [from_cv registered_case10173_genuine_center_boxes;
         from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_genuine_encoded_radii;
         from_cv registered_case10173_first_job_roots]) =
    SOME (from_cv registered_case10173_genuine_hist_item)
Proof
  simp
    [registered_case10173_tag10_genuine_hist_item_pure_eval,
     compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_tag10_genuine_hist_item_eval:
  100000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_item»
        [from_cv registered_case10173_genuine_center_boxes;
         from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_genuine_encoded_radii;
         from_cv registered_case10173_first_job_roots])
      (refs:hol_refs) =
    (M_success (from_cv registered_case10173_genuine_hist_item),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `100000`
  >> simp [registered_case10173_tag10_genuine_hist_item_pure_eval_value]
QED

val _ = export_theory ();
