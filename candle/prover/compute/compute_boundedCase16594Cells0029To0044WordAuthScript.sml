(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 29--44.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0029To0044WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0029To0044WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkLib

val bounded_case16594_cells0029_to_0044_word_authentication =
  compute_boundedCase16594WordChunkLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0029To0044WordData",
     cell_indices=List.tabulate (16,fn offset => 29 + offset),
     chunk_prefix="bounded_case16594_cells0029_to_0044"};

val _ = export_theory ();
