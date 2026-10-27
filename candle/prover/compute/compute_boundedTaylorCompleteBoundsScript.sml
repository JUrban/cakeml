(*****************************************************************************
 * Directed-rounding bound for completed Taylor value intervals.
 *
 * This proof-only sidecar preserves the executable Taylor theory identity.
 *****************************************************************************)
Theory compute_boundedTaylorCompleteBounds
Ancestors
  compute_boundedTaylorComplete compute_boundedWideSignedBounds
Libs
  bossLib preamble intLib

Theorem bounded_taylor_value_complete_bounds:
  bounded_taylor_value_complete radii
      (BoundedInterval64 center_lower center_upper)
      center_gradient hessian =
    SOME (BoundedInterval64 result_lower result_upper) ==>
  ?error.
    bounded_taylor_error radii center_gradient hessian = SOME error /\
    (&2417851639229258349412352:int) *
        bounded_signed64_to_int result_lower <=
      (&2417851639229258349412352:int) *
        bounded_signed64_to_int center_lower -
      &(bounded192_to_num error) /\
    (&2417851639229258349412352:int) *
        bounded_signed64_to_int center_upper +
      &(bounded192_to_num error) <=
    (&2417851639229258349412352:int) *
        bounded_signed64_to_int result_upper
Proof
  rw [bounded_taylor_value_complete_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedWideSignedTheory.bounded_signed192_add_value
  >> imp_res_tac
       compute_boundedWideSignedBoundsTheory.bounded_signed192_shift_floor81_64_lower_bound
  >> imp_res_tac
       compute_boundedWideSignedBoundsTheory.bounded_signed192_shift_ceil81_64_upper_bound
  >> fs [compute_boundedWideSignedBoundsTheory.bounded_signed64_scale81_value,
         compute_boundedWideSignedTheory.bounded_signed192_make_value]
  >> intLib.ARITH_TAC
QED


val _ = export_theory ();
