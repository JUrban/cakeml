(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 93--108.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0093To0108WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0093To0108WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkLib

val bounded_case16594_cells0093_to_0108_word_authentication =
  compute_boundedCase16594WordChunkLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0093To0108WordData",
     cell_indices=List.tabulate (16,fn offset => 93 + offset),
     chunk_prefix="bounded_case16594_cells0093_to_0108"};

val _ = export_theory ();
