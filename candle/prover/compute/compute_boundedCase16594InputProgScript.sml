(*
  CakeML translation of the complete authenticated case16594 input fixture.
  This is reusable DEVELOPMENT data only; it contains no numerical verdict.
*)
Theory compute_boundedCase16594InputProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedProg compute_boundedCase16594InputData

val _ = translation_extends "compute_boundedProg";

val _ = register_type ``:bounded_case16594_input``;

val bounded_case16594_inputs_v =
  translate compute_boundedCase16594InputDataTheory.bounded_case16594_inputs_def;

val _ = export_theory ();
