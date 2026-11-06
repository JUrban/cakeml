(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 205--220.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0205To0220WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0205To0220WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkClockLib

val bounded_case16594_cells0205_to_0220_word_authentication =
  compute_boundedCase16594WordChunkClockLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0205To0220WordData",
     cell_indices=List.tabulate (16,fn offset => 205 + offset),
     chunk_prefix="bounded_case16594_cells0205_to_0220"};

val _ = export_theory ();
