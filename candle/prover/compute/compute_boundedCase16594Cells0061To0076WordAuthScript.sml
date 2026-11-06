(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 61--76.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0061To0076WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0061To0076WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkLib

val bounded_case16594_cells0061_to_0076_word_authentication =
  compute_boundedCase16594WordChunkLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0061To0076WordData",
     cell_indices=List.tabulate (16,fn offset => 61 + offset),
     chunk_prefix="bounded_case16594_cells0061_to_0076"};

val _ = export_theory ();
