(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 125--140.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0125To0140WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0125To0140WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkLib

val bounded_case16594_cells0125_to_0140_word_authentication =
  compute_boundedCase16594WordChunkLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0125To0140WordData",
     cell_indices=List.tabulate (16,fn offset => 125 + offset),
     chunk_prefix="bounded_case16594_cells0125_to_0140"};

val _ = export_theory ();
