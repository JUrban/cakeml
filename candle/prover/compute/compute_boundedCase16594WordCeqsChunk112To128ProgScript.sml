(*****************************************************************************
 * Exact case-16594 CEQ translation chunk 112--128.
 *****************************************************************************)
Theory compute_boundedCase16594WordCeqsChunk112To128Prog
Ancestors
  compute_boundedCase16594WordCeqsChunk096To112Prog
  compute_boundedCase16594ObjectDispatchCell0Data
Libs
  preamble ml_translatorLib ml_progLib basis
  compute_boundedCase16594WordCeqsChunkLib

val _ = translation_extends "compute_boundedCase16594WordCeqsChunk096To112Prog";

val bounded_case16594_word_ceqs_chunk112_to_128_def =
  compute_boundedCase16594WordCeqsChunkLib.translate_chunk
    {original_def=
       compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def,
     start=112,
     count=16,
     name="bounded_case16594_word_ceqs_chunk112_to_128"};

val _ = export_theory ();
