(*****************************************************************************
 * Stable packet-level acceptance for the corrected genuine first NL job.
 *****************************************************************************)
Theory compute_registeredCase10173FastGenuinePacketData
Ancestors
  compute_registeredCase10173SourceAlignedLiteralData
  compute_boundedCase10173PackedDecimalBatch
Libs
  bossLib preamble wordsLib

Theorem registered_case10173_source_aligned_decimal_packet_ok:
  bounded_packed_chars_case10173_decimal_packet_ok
    bounded_case10173_decimal_packet0_source_aligned
Proof
  EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_source_aligned_decimal_packet_well_shaped:
  bounded_case10173_packet_well_shaped
    bounded_case10173_decimal_packet0_source_aligned
Proof
  simp
    [compute_boundedCase10173PacketTheory.bounded_case10173_packet_well_shaped_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_sqrt_certificates_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
QED

val _ = export_theory ();
