(*****************************************************************************
 * Generic outward rounding of source rational constants at scale 2^40.
 *
 * This arithmetic boundary is independent of source-program syntax and of
 * every case-specific Flyspeck plan.  Keeping it below the plan compiler lets
 * object-q soundness depend only on the executable rounding operation it
 * actually reasons about.
 *****************************************************************************)
Theory compute_boundedAnalyticRationalConstant
Ancestors
  compute_boundedInterval
Libs
  bossLib preamble wordsLib

Definition bounded_analytic_scale40_def:
  bounded_analytic_scale40 : num = 1099511627776
End

Definition bounded_analytic_nat_ceil_div_def:
  bounded_analytic_nat_ceil_div numerator denominator =
    if denominator = 0 then 0
    else if numerator MOD denominator = 0 then numerator DIV denominator
    else SUC (numerator DIV denominator)
End

Definition bounded_analytic_rational_constant64_def:
  bounded_analytic_rational_constant64 (positive:num) (negative:num)
      (denominator_predecessor:num) =
    let denominator = SUC denominator_predecessor;
        negative_result = (positive < negative);
        magnitude = if negative_result then negative - positive
                    else positive - negative;
        scaled = magnitude * bounded_analytic_scale40;
        floor_magnitude = scaled DIV denominator;
        ceiling_magnitude =
          bounded_analytic_nat_ceil_div scaled denominator
    in
      if ceiling_magnitude < 18446744073709551616 then
        if negative_result then
          SOME (BoundedInterval64
            (bounded_signed64_make T (n2w ceiling_magnitude))
            (bounded_signed64_make T (n2w floor_magnitude)))
        else
          SOME (BoundedInterval64
            (bounded_signed64_make F (n2w floor_magnitude))
            (bounded_signed64_make F (n2w ceiling_magnitude)))
      else NONE
End

val _ = export_theory ();
