(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 285--300.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0285To0300WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0285To0300WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkClockLib

val bounded_case16594_cells0285_to_0300_word_authentication =
  compute_boundedCase16594WordChunkClockLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0285To0300WordData",
     cell_indices=List.tabulate (16,fn offset => 285 + offset),
     chunk_prefix="bounded_case16594_cells0285_to_0300"};

val _ = export_theory ();
