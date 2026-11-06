(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 141--156.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0141To0156WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0141To0156WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkLib

val bounded_case16594_cells0141_to_0156_word_authentication =
  compute_boundedCase16594WordChunkLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0141To0156WordData",
     cell_indices=List.tabulate (16,fn offset => 141 + offset),
     chunk_prefix="bounded_case16594_cells0141_to_0156"};

val _ = export_theory ();
