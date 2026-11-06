(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 237--252.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0237To0252WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0237To0252WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkClockLib

val bounded_case16594_cells0237_to_0252_word_authentication =
  compute_boundedCase16594WordChunkClockLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0237To0252WordData",
     cell_indices=List.tabulate (16,fn offset => 237 + offset),
     chunk_prefix="bounded_case16594_cells0237_to_0252"};

val _ = export_theory ();
