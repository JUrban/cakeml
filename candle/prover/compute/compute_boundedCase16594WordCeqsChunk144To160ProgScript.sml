(*****************************************************************************
 * Exact case-16594 CEQ translation chunk 144--160.
 *****************************************************************************)
Theory compute_boundedCase16594WordCeqsChunk144To160Prog
Ancestors
  compute_boundedCase16594WordCeqsChunk128To144Prog
  compute_boundedCase16594ObjectDispatchCell0Data
Libs
  preamble ml_translatorLib ml_progLib basis
  compute_boundedCase16594WordCeqsChunkLib

val _ = translation_extends "compute_boundedCase16594WordCeqsChunk128To144Prog";

val bounded_case16594_word_ceqs_chunk144_to_160_def =
  compute_boundedCase16594WordCeqsChunkLib.translate_chunk
    {original_def=
       compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def,
     start=144,
     count=16,
     name="bounded_case16594_word_ceqs_chunk144_to_160"};

val _ = export_theory ();
