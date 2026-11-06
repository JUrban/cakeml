(*****************************************************************************
 * One-cell gate for mechanically recovering clock-parametric entry facts    *
 * from an already completed authentication theory.                           *
 *****************************************************************************)
Theory compute_boundedCase16594Cell94WordEntryClockRetrofitProbe
Ancestors
  compute_boundedCase16594Cells0093To0108WordAuth
Libs
  bossLib preamble
  compute_boundedCase16594WordClockRetrofitLib

val bounded_case16594_cell0094_word_clock_retrofit =
  compute_boundedCase16594WordClockRetrofitLib.retrofit_cells
    {auth_theory="compute_boundedCase16594Cells0093To0108WordAuth",
     cell_indices=[94],
     chunk_prefix="bounded_case16594_cell0094_clock_retrofit"};

val _ = export_theory ();
