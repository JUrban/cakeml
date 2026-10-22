(*****************************************************************************
 * Checked structural preparation of the pinned case16594 cell inputs.
 *
 * The original fixture supplies whole-box endpoints and square-root value
 * certificates.  A separately generated fixture supplies exact source
 * midpoints and upward-rounded radii.  This theory zips the two authenticated
 * 875-row identities and converts their positive raw endpoint pairs into the
 * general signed interval representation.  It does not decide a cell.
 *****************************************************************************)
Theory compute_boundedCase16594PreparedInput
Ancestors
  compute_boundedAnalyticProgram compute_boundedCase16594InputData
  compute_boundedCase16594CenterRadiusData
Libs
  bossLib preamble

Datatype:
  bounded_case16594_prepared_input =
    BoundedCase16594PreparedInput
      (bounded_interval64 list)
      (bounded_interval64 list)
      (word64 list)
      (bounded_interval64 list)
      (bounded_interval64 list)
End

Definition bounded_case16594_positive_intervals_def:
  bounded_case16594_positive_intervals [] = [] ∧
  bounded_case16594_positive_intervals ((lower,upper)::rest) =
    BoundedInterval64 (BoundedSigned64 F lower) (BoundedSigned64 F upper)::
      bounded_case16594_positive_intervals rest
End

Definition bounded_case16594_prepare_input_def:
  bounded_case16594_prepare_input
      (BoundedCase16594Input box box_sqrt center_sqrt)
      (BoundedCase16594CenterRadiusInput centers radii) =
    if LENGTH box = 6 ∧ LENGTH box_sqrt = 10 ∧
       LENGTH center_sqrt = 10 ∧ LENGTH centers = 6 ∧ LENGTH radii = 6
    then SOME
      (BoundedCase16594PreparedInput
        (bounded_case16594_positive_intervals centers)
        (bounded_case16594_positive_intervals box)
        radii
        (bounded_case16594_positive_intervals center_sqrt)
        (bounded_case16594_positive_intervals box_sqrt))
    else NONE
End

Definition bounded_case16594_prepare_inputs_def:
  bounded_case16594_prepare_inputs [] [] = SOME [] ∧
  bounded_case16594_prepare_inputs (input::inputs)
      (center_radius::center_radii) =
    (case bounded_case16594_prepare_input input center_radius of
     | NONE => NONE
     | SOME prepared =>
       case bounded_case16594_prepare_inputs inputs center_radii of
       | NONE => NONE
       | SOME rest => SOME (prepared::rest)) ∧
  bounded_case16594_prepare_inputs _ _ = NONE
End

Definition bounded_case16594_prepared_inputs_def:
  bounded_case16594_prepared_inputs =
    case bounded_case16594_prepare_inputs bounded_case16594_inputs
      bounded_case16594_center_radius_inputs of
    | NONE => []
    | SOME prepared => prepared
End

Definition bounded_case16594_prepared_inputs_ok_def:
  bounded_case16594_prepared_inputs_ok ⇔
    bounded_case16594_prepare_inputs bounded_case16594_inputs
      bounded_case16594_center_radius_inputs =
        SOME bounded_case16594_prepared_inputs ∧
    LENGTH bounded_case16594_prepared_inputs = 875
End

Theorem bounded_case16594_prepared_inputs_ok_value:
  bounded_case16594_prepared_inputs_ok
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_prepare_input_rejects_width_drift:
  bounded_case16594_prepare_input
    (BoundedCase16594Input [] [] [])
    (BoundedCase16594CenterRadiusInput [] []) = NONE ∧
  bounded_case16594_prepare_inputs []
    [BoundedCase16594CenterRadiusInput [] []] = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
