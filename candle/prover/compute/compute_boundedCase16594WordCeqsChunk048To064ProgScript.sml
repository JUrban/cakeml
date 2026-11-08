(*****************************************************************************
 * Exact case-16594 CEQ translation chunk 048--064.
 *****************************************************************************)
Theory compute_boundedCase16594WordCeqsChunk048To064Prog
Ancestors
  compute_boundedCase16594WordCeqsChunk032To048Prog
  compute_boundedCase16594ObjectDispatchCell0Data
Libs
  preamble ml_translatorLib ml_progLib basis
  compute_boundedCase16594WordCeqsChunkLib

val _ = translation_extends "compute_boundedCase16594WordCeqsChunk032To048Prog";

val bounded_case16594_word_ceqs_chunk048_to_064_def =
  compute_boundedCase16594WordCeqsChunkLib.translate_chunk
    {original_def=
       compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def,
     start=48,
     count=16,
     name="bounded_case16594_word_ceqs_chunk048_to_064"};

val _ = export_theory ();
