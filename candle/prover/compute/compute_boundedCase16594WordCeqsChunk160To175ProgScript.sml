(*****************************************************************************
 * Exact case-16594 CEQ translation chunk 160--175.
 *****************************************************************************)
Theory compute_boundedCase16594WordCeqsChunk160To175Prog
Ancestors
  compute_boundedCase16594WordCeqsChunk144To160Prog
  compute_boundedCase16594ObjectDispatchCell0Data
Libs
  preamble ml_translatorLib ml_progLib basis
  compute_boundedCase16594WordCeqsChunkLib

val _ = translation_extends "compute_boundedCase16594WordCeqsChunk144To160Prog";

val bounded_case16594_word_ceqs_chunk160_to_175_def =
  compute_boundedCase16594WordCeqsChunkLib.translate_chunk
    {original_def=
       compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def,
     start=160,
     count=15,
     name="bounded_case16594_word_ceqs_chunk160_to_175"};

val _ = export_theory ();
