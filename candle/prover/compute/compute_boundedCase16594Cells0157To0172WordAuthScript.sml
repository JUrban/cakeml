(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 157--172.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0157To0172WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0157To0172WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkClockLib

val bounded_case16594_cells0157_to_0172_word_authentication =
  compute_boundedCase16594WordChunkClockLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0157To0172WordData",
     cell_indices=List.tabulate (16,fn offset => 157 + offset),
     chunk_prefix="bounded_case16594_cells0157_to_0172"};

val _ = export_theory ();
