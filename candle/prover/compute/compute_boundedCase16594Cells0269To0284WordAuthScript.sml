(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 269--284.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0269To0284WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0269To0284WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkClockLib

val bounded_case16594_cells0269_to_0284_word_authentication =
  compute_boundedCase16594WordChunkClockLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0269To0284WordData",
     cell_indices=List.tabulate (16,fn offset => 269 + offset),
     chunk_prefix="bounded_case16594_cells0269_to_0284"};

val _ = export_theory ();
