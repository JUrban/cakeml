(*****************************************************************************
 * Kernel theorem constructor for genuine cells [2048,2064).                *
 *                                                                           *
 * This establishes the trusted compute_with handoff for the exact bounded  *
 * call.  The next runtime experiment will invoke this constructor and feed  *
 * its ordinary equality theorem to the existing Flyspeck source adapter.    *
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalChunkAt2048Count16Kernel
Ancestors
  computeProof
  compute_registeredCase10173HistoricalChunkAt2048Count16Fast
Libs
  bossLib preamble

Definition compute_registered_case10173_historical_chunk_at2048_count16_def:
  compute_registered_case10173_historical_chunk_at2048_count16
      (ths,ceqs) tm =
    compute_with
      registered_case10173_historical_chunk_at2048_count16_fast_eval
      (ths,ceqs) tm
End

Theorem compute_registered_case10173_historical_chunk_at2048_count16_thm:
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_registered_case10173_historical_chunk_at2048_count16
      (ths,ceqs) tm s = (res,s') ==>
    s' = s /\
    (!th. res = M_success th ==> THM ctxt th) /\
    (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs
       [compute_registered_case10173_historical_chunk_at2048_count16_def]
  >> strip_tac
  >> assume_tac
       registered_case10173_historical_chunk_at2048_count16_fast_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac
       `registered_case10173_historical_chunk_at2048_count16_fast_eval`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

val _ = export_theory ();
