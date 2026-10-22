(*****************************************************************************
 * Executable presentations of authenticated decimal input relations.
 *
 * The logical contracts deliberately use LIST_REL and existential trailing
 * witnesses.  CakeML's translator does not execute those higher-order forms
 * directly.  The first-order recursive relations below are proved equivalent
 * once, then used by the translated authenticated checker.
 *****************************************************************************)
Theory compute_boundedCase10173PackedDecimalAuthenticatedExecutable
Ancestors
  compute_boundedCase10173PackedDecimalAuthenticated
Libs
  bossLib preamble

Definition bounded_interval64_list_covers_q_pairs_decimal_def:
  (bounded_interval64_list_covers_q_pairs_decimal [] [] <=> T) /\
  (bounded_interval64_list_covers_q_pairs_decimal
      (interval::intervals) (object_interval::object_intervals) <=>
     bounded_interval64_covers_object_q_ints_decimal
       interval object_interval /\
     bounded_interval64_list_covers_q_pairs_decimal
       intervals object_intervals) /\
  (bounded_interval64_list_covers_q_pairs_decimal _ _ <=> F)
End

Theorem bounded_interval64_list_covers_q_pairs_decimal_eq_list_rel:
  !intervals object_intervals.
    bounded_interval64_list_covers_q_pairs_decimal
      intervals object_intervals <=>
    LIST_REL bounded_interval64_covers_object_q_ints_decimal
      intervals object_intervals
Proof
  Induct
  >> Cases_on `object_intervals`
  >> simp [bounded_interval64_list_covers_q_pairs_decimal_def]
QED

Theorem bounded_interval64_list_covers_object_q_decimal_executable_def:
  bounded_interval64_list_covers_object_q_decimal intervals encoded <=>
    case bounded_object_q_interval_list encoded of
    | NONE => F
    | SOME object_intervals =>
        bounded_interval64_list_covers_q_pairs_decimal
          intervals object_intervals
Proof
  rw [compute_boundedObjectDecimalQTheory.bounded_interval64_list_covers_object_q_decimal_def,
      bounded_interval64_list_covers_q_pairs_decimal_eq_list_rel]
QED

Definition bounded_interval64_list_prefix_one_extra_def:
  (bounded_interval64_list_prefix_one_extra [] [extra] <=> T) /\
  (bounded_interval64_list_prefix_one_extra
      (expected::expecteds) (actual::actuals) <=>
     expected = actual /\
     bounded_interval64_list_prefix_one_extra expecteds actuals) /\
  (bounded_interval64_list_prefix_one_extra _ _ <=> F)
End

Theorem bounded_interval64_list_prefix_one_extra_eq:
  !expected actual.
    bounded_interval64_list_prefix_one_extra expected actual <=>
    ?extra. actual = expected ++ [extra]
Proof
  Induct
  >- (Cases_on `actual`
      >> simp [bounded_interval64_list_prefix_one_extra_def]
      >> Cases_on `t`
      >> simp [bounded_interval64_list_prefix_one_extra_def])
  >> Cases_on `actual`
  >> simp [bounded_interval64_list_prefix_one_extra_def]
  >> metis_tac []
QED

Theorem bounded_case10173_decimal_packet_sqrt_roots_bind_object_job_executable_def:
  bounded_case10173_decimal_packet_sqrt_roots_bind_object_job packet
      object_job <=>
    case object_job of
    | Pair box_sqrt_data (Pair center_sqrt_data source_boxes) =>
        (case bounded_case10173_decimal_packet_sqrt_roots packet of
         | (center_roots,box_roots) =>
             case bounded_object_positive_q_interval64_decimal_list
               center_sqrt_data of
             | NONE => F
             | SOME decoded_center_roots =>
                 case bounded_object_positive_q_interval64_decimal_list
                   box_sqrt_data of
                 | NONE => F
                 | SOME decoded_box_roots =>
                     bounded_interval64_list_prefix_one_extra
                       center_roots decoded_center_roots /\
                     bounded_interval64_list_prefix_one_extra
                       box_roots decoded_box_roots)
    | _ => F
Proof
  Cases_on `object_job`
  >- simp
       [compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_sqrt_roots_bind_object_job_def]
  >> Cases_on `c0`
  >- simp
       [compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_sqrt_roots_bind_object_job_def]
  >> Cases_on `bounded_case10173_decimal_packet_sqrt_roots packet`
  >> simp
       [compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_sqrt_roots_bind_object_job_def]
  >> every_case_tac
  >> gvs [bounded_interval64_list_prefix_one_extra_eq]
  >> metis_tac []
QED

val _ = export_theory ();
