(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 77--92.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0077To0092WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0077To0092WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkLib

val bounded_case16594_cells0077_to_0092_word_authentication =
  compute_boundedCase16594WordChunkLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0077To0092WordData",
     cell_indices=List.tabulate (16,fn offset => 77 + offset),
     chunk_prefix="bounded_case16594_cells0077_to_0092"};

val _ = export_theory ();
