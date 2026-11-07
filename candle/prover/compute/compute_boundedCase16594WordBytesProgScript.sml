(*****************************************************************************
 * Authenticated balanced byte-tree decoder for the exact certificate.      *
 *****************************************************************************)
Theory compute_boundedCase16594WordBytesProg
Ancestors
  compute_boundedCase16594WordTraceProg
  compute_cvPackedBytes
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_boundedCase16594WordTraceProg";

val _ = translate compute_cvPackedBytesTheory.cv_packed_bytes_chunk_limit_def;
val _ = translate compute_cvPackedBytesTheory.cv_unpack_byte_chunk_def;
val _ = translate compute_cvPackedBytesTheory.cv_unpack_byte_tree_append_def;
val _ = translate compute_cvPackedBytesTheory.cv_unpack_byte_tree_def;

val _ = export_theory ();
