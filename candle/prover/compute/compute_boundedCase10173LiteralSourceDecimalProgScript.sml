(* CakeML translation of the source-shaped decimal case-10173 checker. *)
Theory compute_boundedCase10173LiteralSourceDecimalProg
Ancestors
  compute_boundedCase10173PackedDecimalBatchProg
  compute_boundedCase10173LiteralSourceDecimal
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends
  "compute_boundedCase10173PackedDecimalBatchProg";

val _ = translate bounded_case10173_literal_term0_decimal_def;
val _ = translate bounded_case10173_literal_term1_decimal_def;
val _ = translate bounded_case10173_literal_term23_decimal_def;
val _ = translate bounded_case10173_literal_term4_decimal_def;
val _ = translate bounded_case10173_literal_term56_decimal_def;
val _ = translate bounded_case10173_literal_negative_one_decimal_def;

val _ = translate
  compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_variable_decimal_def;
val _ = translate bounded_case10173_literal_products_decimal_def;
val _ = translate bounded_case10173_literal_constants_decimal_def;
val _ = translate bounded_case10173_literal_summands_decimal_def;
val _ = translate bounded_case10173_literal_add_decimal_def;
val _ = translate bounded_case10173_literal_add_stack_decimal_def;
val _ = translate bounded_case10173_literal_historical_item_decimal_def;
val _ = translate bounded_case10173_literal_source_decimal_def;
val _ = translate bounded_case10173_literal_source_accepts_decimal_def;

val _ = export_theory ();
