(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 317--332.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0317To0332WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0317To0332WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkClockLib

val bounded_case16594_cells0317_to_0332_word_authentication =
  compute_boundedCase16594WordChunkClockLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0317To0332WordData",
     cell_indices=List.tabulate (16,fn offset => 317 + offset),
     chunk_prefix="bounded_case16594_cells0317_to_0332"};

val _ = export_theory ();
