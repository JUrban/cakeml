(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 253--268.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0253To0268WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0253To0268WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkClockLib

val bounded_case16594_cells0253_to_0268_word_authentication =
  compute_boundedCase16594WordChunkClockLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0253To0268WordData",
     cell_indices=List.tabulate (16,fn offset => 253 + offset),
     chunk_prefix="bounded_case16594_cells0253_to_0268"};

val _ = export_theory ();
