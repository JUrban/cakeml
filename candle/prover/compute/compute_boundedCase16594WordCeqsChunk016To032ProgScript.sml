(*****************************************************************************
 * Exact case-16594 CEQ translation chunk 016--032.
 *****************************************************************************)
Theory compute_boundedCase16594WordCeqsChunk016To032Prog
Ancestors
  compute_boundedCase16594WordCeqsChunk000To016Prog
  compute_boundedCase16594ObjectDispatchCell0Data
Libs
  preamble ml_translatorLib ml_progLib basis
  compute_boundedCase16594WordCeqsChunkLib

val _ = translation_extends "compute_boundedCase16594WordCeqsChunk000To016Prog";

val bounded_case16594_word_ceqs_chunk016_to_032_def =
  compute_boundedCase16594WordCeqsChunkLib.translate_chunk
    {original_def=
       compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def,
     start=16,
     count=16,
     name="bounded_case16594_word_ceqs_chunk016_to_032"};

val _ = export_theory ();
