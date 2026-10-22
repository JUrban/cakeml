(*****************************************************************************
 * Closed literal-source result for the source-aligned first genuine job.
 *
 * The older packet-0 fixture used tighter square-root certificates than the
 * source program.  This theorem deliberately evaluates the source-aligned
 * packet whose certificates are the ones authenticated against the actual
 * Taylor-completed operands.
 *****************************************************************************)
Theory compute_registeredCase10173SourceAlignedLiteralData
Ancestors
  compute_boundedCase10173LiteralSourceDecimalData
  compute_boundedCase10173DecimalInputBinding
Libs
  bossLib preamble wordsLib

Theorem registered_case10173_source_aligned_literal_source_accepts:
  bounded_case10173_literal_source_accepts_decimal
    bounded_case10173_decimal_packet0_source_aligned
Proof
  EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
