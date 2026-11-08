(*****************************************************************************
 * Exact case-16594 CEQ translation chunk 080--096.
 *****************************************************************************)
Theory compute_boundedCase16594WordCeqsChunk080To096Prog
Ancestors
  compute_boundedCase16594WordCeqsChunk064To080Prog
  compute_boundedCase16594ObjectDispatchCell0Data
Libs
  preamble ml_translatorLib ml_progLib basis
  compute_boundedCase16594WordCeqsChunkLib

val _ = translation_extends "compute_boundedCase16594WordCeqsChunk064To080Prog";

val bounded_case16594_word_ceqs_chunk080_to_096_def =
  compute_boundedCase16594WordCeqsChunkLib.translate_chunk
    {original_def=
       compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def,
     start=80,
     count=16,
     name="bounded_case16594_word_ceqs_chunk080_to_096"};

val _ = export_theory ();
