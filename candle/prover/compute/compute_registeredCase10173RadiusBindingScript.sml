(*****************************************************************************
 * Exact source-radius binding for a genuine case-10173 packet.
 *
 * The registered source computes each radius as half the width of one exact
 * positive rational source interval and then rounds upward at scale 10^12.
 * This file states that calculation directly on the authenticated cv source
 * data.  It is deliberately independent of the packet center/box geometry:
 * a merely sufficient or enlarged radius is not the literal source radius.
 *****************************************************************************)
Theory compute_registeredCase10173RadiusBinding
Ancestors
  compute_registeredCase10173RootInputsBinding
Libs
  bossLib preamble

Definition bounded_case10173_packet_radii_def:
  bounded_case10173_packet_radii
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) =
    radii
End

(* For [lower = l/ld] and [upper = u/ud], the registered calculation is
 *
 *   ceil (10^12 * (upper - lower) / 2).
 *
 * Keeping the cross-multiplied numerator here avoids accepting an
 * independently rounded decimal width as authority. *)
Definition bounded_case10173_source_radius64_positive_q_def:
  bounded_case10173_source_radius64_positive_q
      (Pair
        (Pair (Pair (Num lower_value) (Num 0))
          (Num lower_denominator_minus_one))
        (Pair (Pair (Num upper_value) (Num 0))
          (Num upper_denominator_minus_one)) : cv) =
    (let lower_denominator = SUC lower_denominator_minus_one in
     let upper_denominator = SUC upper_denominator_minus_one in
     let lower_cross = lower_value * upper_denominator in
     let upper_cross = upper_value * lower_denominator in
     if lower_cross <= upper_cross then
       bounded_decimal_natural_ceil64
         (upper_cross - lower_cross)
         (2 * lower_denominator * upper_denominator)
     else NONE) /\
  bounded_case10173_source_radius64_positive_q _ = NONE
End

Definition bounded_case10173_source_radii64_positive_q_def:
  bounded_case10173_source_radii64_positive_q (Num 0 : cv) = SOME [] /\
  bounded_case10173_source_radii64_positive_q
      (Pair interval intervals) =
    (case bounded_case10173_source_radius64_positive_q interval of
     | NONE => NONE
     | SOME radius =>
       case bounded_case10173_source_radii64_positive_q intervals of
       | NONE => NONE
       | SOME radii => SOME (radius::radii)) /\
  bounded_case10173_source_radii64_positive_q _ = NONE
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Definition bounded_case10173_decimal_packet_source_radii_exact_def:
  bounded_case10173_decimal_packet_source_radii_exact packet object_job <=>
    case
      bounded_case10173_object_job_boxes object_job
    of
    | NONE => F
    | SOME source_boxes =>
        bounded_case10173_source_radii64_positive_q source_boxes =
          SOME (bounded_case10173_packet_radii packet)
End

Theorem bounded_case10173_decimal_packet_source_radii_exact_components:
  bounded_case10173_decimal_packet_source_radii_exact packet object_job ==>
  ?source_boxes.
    bounded_case10173_object_job_boxes object_job = SOME source_boxes /\
    bounded_case10173_source_radii64_positive_q source_boxes =
      SOME (bounded_case10173_packet_radii packet)
Proof
  rw [bounded_case10173_decimal_packet_source_radii_exact_def]
  >> every_case_tac
  >> gvs []
QED

val _ = export_theory ();
