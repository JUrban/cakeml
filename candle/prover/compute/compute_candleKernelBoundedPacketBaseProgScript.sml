(*****************************************************************************
 * First saved kernel-lineage checkpoint for the specialized NL packet path.
 *
 * Only definitions reachable from bounded_case10173_packet_check_cv are
 * replayed here.  Extending candle_kernelProg keeps the Candle and checker
 * constructors in one translator state; no AST or saved-state splice occurs.
 *****************************************************************************)
Theory compute_candleKernelBoundedPacketBaseProg
Ancestors
  candle_kernelProg compute_bounded
Libs
  preamble ml_translatorLib ml_monad_translatorLib ml_progLib

val _ = m_translation_extends "candle_kernelProg";

val _ = register_type ``:bounded128``;
val _ = register_type ``:bounded192``;

val _ = translate compute_boundedTheory.bounded_word64_add_carry_def;
val _ = translate compute_boundedTheory.bounded_word64_mul_full_chunks22_def;
val _ = translate compute_boundedTheory.bounded_word64_mul_shift_floor40_def;
val _ = translate compute_boundedTheory.bounded128_shift_floor40_words_def;
val _ = translate compute_boundedTheory.bounded128_add_words_def;
val _ = translate compute_boundedTheory.bounded192_add_words_def;

val _ = export_theory ();
