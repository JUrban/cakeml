(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 301--316.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0301To0316WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0301To0316WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkClockLib

val bounded_case16594_cells0301_to_0316_word_authentication =
  compute_boundedCase16594WordChunkClockLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0301To0316WordData",
     cell_indices=List.tabulate (16,fn offset => 301 + offset),
     chunk_prefix="bounded_case16594_cells0301_to_0316"};

val _ = export_theory ();
