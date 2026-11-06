(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 189--204.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0189To0204WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0189To0204WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkClockLib

val bounded_case16594_cells0189_to_0204_word_authentication =
  compute_boundedCase16594WordChunkClockLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0189To0204WordData",
     cell_indices=List.tabulate (16,fn offset => 189 + offset),
     chunk_prefix="bounded_case16594_cells0189_to_0204"};

val _ = export_theory ();
