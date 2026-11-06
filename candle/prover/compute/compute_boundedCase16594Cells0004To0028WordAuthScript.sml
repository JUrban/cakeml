(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 4--28.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0004To0028WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0004To0028WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkLib

val bounded_case16594_cells0004_to_0028_word_authentication =
  compute_boundedCase16594WordChunkLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0004To0028WordData",
     cell_indices=List.tabulate (25,fn offset => 4 + offset),
     chunk_prefix="bounded_case16594_cells0004_to_0028"};

val _ = export_theory ();
