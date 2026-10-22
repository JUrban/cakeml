(*****************************************************************************
 * Pure object calculation for the exact rational center environment.
 *
 * Keep this source-independent data transformation below the registered
 * evaluator layer so authenticated packet binding can reuse it without a
 * dependency on the checked-job evaluator stack.
 *****************************************************************************)
Theory compute_registeredCase10173CenterEnvironmentObject
Ancestors
  compute_exec
Libs
  bossLib preamble

Definition registered_case10173_q_midpoint_positive_cv_def:
  registered_case10173_q_midpoint_positive_cv
      lower_value lower_denominator_minus_one
      upper_value upper_denominator_minus_one =
    let lower_denominator = lower_denominator_minus_one + 1 in
    let upper_denominator = upper_denominator_minus_one + 1 in
    let numerator =
      upper_denominator * lower_value +
      lower_denominator * upper_value in
    let sum_denominator_minus_one =
      lower_denominator_minus_one + upper_denominator_minus_one +
      lower_denominator_minus_one * upper_denominator_minus_one in
    Pair (Pair (Num numerator) (Num 0))
      (Num (1 + sum_denominator_minus_one +
            sum_denominator_minus_one))
End

Definition registered_case10173_q_center_environment_positive_def:
  registered_case10173_q_center_environment_positive (Num 0 : cv) =
      SOME (Num 0) /\
  registered_case10173_q_center_environment_positive
      (Pair
        (Pair
          (Pair (Pair (Num lower_value) (Num 0))
            (Num lower_denominator_minus_one))
          (Pair (Pair (Num upper_value) (Num 0))
            (Num upper_denominator_minus_one)))
        boxes) =
      (case registered_case10173_q_center_environment_positive boxes of
       | NONE => NONE
       | SOME centers =>
           let midpoint =
             registered_case10173_q_midpoint_positive_cv
               lower_value lower_denominator_minus_one
               upper_value upper_denominator_minus_one in
           SOME (Pair (Pair midpoint midpoint) centers)) /\
  registered_case10173_q_center_environment_positive _ = NONE
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

val _ = export_theory ();
