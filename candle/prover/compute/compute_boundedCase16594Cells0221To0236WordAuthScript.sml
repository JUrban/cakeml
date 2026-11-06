(*****************************************************************************
 * Restartable complete authentication chunk for genuine source rows 221--236.
 *****************************************************************************)
Theory compute_boundedCase16594Cells0221To0236WordAuth
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594Cells0221To0236WordData
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticRuntimeCertificateTraceWideCV
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble wordsLib cv_transLib
  compute_boundedCase16594WordChunkClockLib

val bounded_case16594_cells0221_to_0236_word_authentication =
  compute_boundedCase16594WordChunkClockLib.authenticate_cells
    {data_theory="compute_boundedCase16594Cells0221To0236WordData",
     cell_indices=List.tabulate (16,fn offset => 221 + offset),
     chunk_prefix="bounded_case16594_cells0221_to_0236"};

val _ = export_theory ();
