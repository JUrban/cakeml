(*****************************************************************************
 * Exact case-16594 CEQ translation chunk 096--112.
 *****************************************************************************)
Theory compute_boundedCase16594WordCeqsChunk096To112Prog
Ancestors
  compute_boundedCase16594WordCeqsChunk080To096Prog
  compute_boundedCase16594ObjectDispatchCell0Data
Libs
  preamble ml_translatorLib ml_progLib basis
  compute_boundedCase16594WordCeqsChunkLib

val _ = translation_extends "compute_boundedCase16594WordCeqsChunk080To096Prog";

val bounded_case16594_word_ceqs_chunk096_to_112_def =
  compute_boundedCase16594WordCeqsChunkLib.translate_chunk
    {original_def=
       compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def,
     start=96,
     count=16,
     name="bounded_case16594_word_ceqs_chunk096_to_112"};

val _ = export_theory ();
