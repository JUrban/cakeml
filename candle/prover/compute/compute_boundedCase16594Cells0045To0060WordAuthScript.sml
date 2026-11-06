(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 45--60.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0045To0060WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0045To0060WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkLib

val bounded_case16594_cells0045_to_0060_word_authentication =
  compute_boundedCase16594WordChunkLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0045To0060WordData",
     cell_indices=List.tabulate (16,fn offset => 45 + offset),
     chunk_prefix="bounded_case16594_cells0045_to_0060"};

val _ = export_theory ();
