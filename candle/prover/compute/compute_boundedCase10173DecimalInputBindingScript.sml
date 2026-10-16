(*****************************************************************************
 * Exact authenticated-input binding for the strengthened decimal packet.
 *
 * The old dyadic packet could only be related to the object's decimal root
 * records by overlap.  The strengthened packet uses the object's actual
 * scale 10^12.  Its six source-square-root intervals must be the canonical
 * outward decimal conversion of the authenticated rational source records,
 * and its four historical root intervals must decode byte-for-value exactly.
 * This is a fail-closed positional relation: malformed shapes, missing
 * fields, reordered fields, or independently widened intervals are rejected.
 *****************************************************************************)
Theory compute_boundedCase10173DecimalInputBinding
Ancestors
  compute_boundedCase10173HistoricalCellDecimalBoundary
  compute_boundedCase10173RootBinding
Libs
  bossLib preamble wordsLib

Definition bounded_case10173_sqrt64_center_intervals_def:
  bounded_case10173_sqrt64_center_intervals [] = [] /\
  bounded_case10173_sqrt64_center_intervals
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
        center_derivative box_derivative box_second_reciprocal::rest) =
    center_sqrt::bounded_case10173_sqrt64_center_intervals rest
End

Definition bounded_case10173_sqrt64_box_intervals_def:
  bounded_case10173_sqrt64_box_intervals [] = [] /\
  bounded_case10173_sqrt64_box_intervals
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
        center_derivative box_derivative box_second_reciprocal::rest) =
    box_sqrt::bounded_case10173_sqrt64_box_intervals rest
End

Definition bounded_case10173_decimal_packet_sqrt_roots_def:
  bounded_case10173_decimal_packet_sqrt_roots
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) =
    (bounded_case10173_sqrt64_center_intervals
       coordinate_sqrt_certificates,
     bounded_case10173_sqrt64_box_intervals
       coordinate_sqrt_certificates)
End

Definition bounded_case10173_decimal_packet_sqrt_roots_bind_object_job_def:
  bounded_case10173_decimal_packet_sqrt_roots_bind_object_job packet
      (Pair box_sqrt_data (Pair center_sqrt_data source_boxes) : cv) =
    (?center_extra box_extra.
       bounded_object_positive_q_interval64_decimal_list center_sqrt_data =
         SOME (FST (bounded_case10173_decimal_packet_sqrt_roots packet) ++
               [center_extra]) /\
       bounded_object_positive_q_interval64_decimal_list box_sqrt_data =
         SOME (SND (bounded_case10173_decimal_packet_sqrt_roots packet) ++
               [box_extra])) /\
  bounded_case10173_decimal_packet_sqrt_roots_bind_object_job packet _ = F
End

Definition bounded_case10173_decimal_packet_roots_bind_object_record_def:
  bounded_case10173_decimal_packet_roots_bind_object_record packet
      root_record <=>
    bounded_object_decimal_interval64_list root_record =
      SOME (bounded_case10173_packet_root_intervals packet)
End

Definition bounded_case10173_decimal_packet_exact_auxiliary_binding_def:
  bounded_case10173_decimal_packet_exact_auxiliary_binding packet object_job
      root_record <=>
    bounded_case10173_decimal_packet_sqrt_roots_bind_object_job
      packet object_job /\
    bounded_case10173_decimal_packet_roots_bind_object_record
      packet root_record
End

Definition bounded_case10173_decimal_packet_box_exact_object_job_def:
  bounded_case10173_decimal_packet_box_exact_object_job packet
      (Pair box_sqrt_data (Pair center_sqrt_data source_boxes) : cv) =
    (bounded_object_positive_q_interval64_decimal_list source_boxes =
       SOME (bounded_case10173_packet_box_environment packet)) /\
  bounded_case10173_decimal_packet_box_exact_object_job packet _ = F
End

Definition bounded_case10173_decimal_packet_exact_input_binding_def:
  bounded_case10173_decimal_packet_exact_input_binding packet object_job
      root_record <=>
    bounded_case10173_decimal_packet_box_exact_object_job
      packet object_job /\
    bounded_case10173_decimal_packet_exact_auxiliary_binding
      packet object_job root_record
End

Theorem bounded_case10173_decimal_packet_sqrt_roots_binding_components:
  bounded_case10173_decimal_packet_sqrt_roots_bind_object_job packet
    object_job ==>
  ?box_sqrt_data center_sqrt_data source_boxes center_roots box_roots
     center_extra box_extra.
    object_job = Pair box_sqrt_data (Pair center_sqrt_data source_boxes) /\
    bounded_case10173_decimal_packet_sqrt_roots packet =
      (center_roots,box_roots) /\
    bounded_object_positive_q_interval64_decimal_list center_sqrt_data =
      SOME (center_roots ++ [center_extra]) /\
    bounded_object_positive_q_interval64_decimal_list box_sqrt_data =
      SOME (box_roots ++ [box_extra])
Proof
  Cases_on `object_job`
  >> rw
       [bounded_case10173_decimal_packet_sqrt_roots_bind_object_job_def]
  >> Cases_on `c0`
  >> gvs
       [bounded_case10173_decimal_packet_sqrt_roots_bind_object_job_def]
  >> PairCases_on `bounded_case10173_decimal_packet_sqrt_roots packet`
  >> gvs []
QED

Theorem bounded_case10173_decimal_packet_box_exact_components:
  bounded_case10173_decimal_packet_box_exact_object_job packet object_job ==>
  ?box_sqrt_data center_sqrt_data source_boxes.
    object_job = Pair box_sqrt_data (Pair center_sqrt_data source_boxes) /\
    bounded_object_positive_q_interval64_decimal_list source_boxes =
      SOME (bounded_case10173_packet_box_environment packet)
Proof
  Cases_on `object_job`
  >> rw [bounded_case10173_decimal_packet_box_exact_object_job_def]
  >> Cases_on `c0`
  >> gvs [bounded_case10173_decimal_packet_box_exact_object_job_def]
QED

Theorem bounded_case10173_decimal_packet_root_binding_exact_cv:
  bounded_case10173_decimal_packet_roots_bind_object_record packet
      root_record ==>
  bounded_interval64_object_cv_list
      (bounded_case10173_packet_root_intervals packet) = root_record
Proof
  rw
    [bounded_case10173_decimal_packet_roots_bind_object_record_def]
  >> imp_res_tac
       compute_boundedObjectDecimalDecodeTheory.bounded_object_decimal_interval64_list_exact
QED

Theorem bounded_case10173_decimal_packet_sqrt_binding_canonical:
  bounded_case10173_decimal_packet_sqrt_roots_bind_object_job packet
      object_job ==>
  ?box_sqrt_data center_sqrt_data source_boxes center_roots box_roots
     center_extra box_extra.
    object_job = Pair box_sqrt_data (Pair center_sqrt_data source_boxes) /\
    bounded_case10173_decimal_packet_sqrt_roots packet =
      (center_roots,box_roots) /\
    bounded_object_positive_q_interval64_decimal_list center_sqrt_data =
      SOME (center_roots ++ [center_extra]) /\
    bounded_object_positive_q_interval64_decimal_list box_sqrt_data =
      SOME (box_roots ++ [box_extra])
Proof
  strip_tac
  >> imp_res_tac
       bounded_case10173_decimal_packet_sqrt_roots_binding_components
  >> metis_tac []
QED

Definition bounded_case10173_decimal_packet0_source_sqrt_certificates_def:
  bounded_case10173_decimal_packet0_source_sqrt_certificates =
    [BoundedCase10173Sqrt64Certificate
       (BoundedInterval64 (BoundedSigned64 F 2191400000000w)
         (BoundedSigned64 F 2191450000000w))
       (BoundedInterval64 (BoundedSigned64 F 2179996000000w)
         (BoundedSigned64 F 2202793000000w))
       (BoundedInterval64 (BoundedSigned64 F 228159437815w)
         (BoundedSigned64 F 228164643607w))
       (BoundedInterval64 (BoundedSigned64 F 226984560056w)
         (BoundedSigned64 F 229358219006w))
       (BoundedInterval64 (BoundedSigned64 F 23389498746w)
         (BoundedSigned64 F 24130778029w));
     BoundedCase10173Sqrt64Certificate
       (BoundedInterval64 (BoundedSigned64 F 2011700000000w)
         (BoundedSigned64 F 2011750000000w))
       (BoundedInterval64 (BoundedSigned64 F 1999996000000w)
         (BoundedSigned64 F 2023380000000w))
       (BoundedInterval64 (BoundedSigned64 F 248539828507w)
         (BoundedSigned64 F 248546005866w))
       (BoundedInterval64 (BoundedSigned64 F 247111269262w)
         (BoundedSigned64 F 250000500002w))
       (BoundedInterval64 (BoundedSigned64 F 30179317456w)
         (BoundedSigned64 F 31250062501w));
     BoundedCase10173Sqrt64Certificate
       (BoundedInterval64 (BoundedSigned64 F 2011700000000w)
         (BoundedSigned64 F 2011750000000w))
       (BoundedInterval64 (BoundedSigned64 F 1999996000000w)
         (BoundedSigned64 F 2023380000000w))
       (BoundedInterval64 (BoundedSigned64 F 248539828507w)
         (BoundedSigned64 F 248546005866w))
       (BoundedInterval64 (BoundedSigned64 F 247111269262w)
         (BoundedSigned64 F 250000500002w))
       (BoundedInterval64 (BoundedSigned64 F 30179317456w)
         (BoundedSigned64 F 31250062501w));
     BoundedCase10173Sqrt64Certificate
       (BoundedInterval64 (BoundedSigned64 F 2008260000000w)
         (BoundedSigned64 F 2008310000000w))
       (BoundedInterval64 (BoundedSigned64 F 1999996000000w)
         (BoundedSigned64 F 2016538000000w))
       (BoundedInterval64 (BoundedSigned64 F 248965548147w)
         (BoundedSigned64 F 248971746687w))
       (BoundedInterval64 (BoundedSigned64 F 247949703898w)
         (BoundedSigned64 F 250000500002w))
       (BoundedInterval64 (BoundedSigned64 F 30487571660w)
         (BoundedSigned64 F 31250062501w));
     BoundedCase10173Sqrt64Certificate
       (BoundedInterval64 (BoundedSigned64 F 2008260000000w)
         (BoundedSigned64 F 2008310000000w))
       (BoundedInterval64 (BoundedSigned64 F 1999996000000w)
         (BoundedSigned64 F 2016538000000w))
       (BoundedInterval64 (BoundedSigned64 F 248965548147w)
         (BoundedSigned64 F 248971746687w))
       (BoundedInterval64 (BoundedSigned64 F 247949703898w)
         (BoundedSigned64 F 250000500002w))
       (BoundedInterval64 (BoundedSigned64 F 30487571660w)
         (BoundedSigned64 F 31250062501w));
     BoundedCase10173Sqrt64Certificate
       (BoundedInterval64 (BoundedSigned64 F 2016510000000w)
         (BoundedSigned64 F 2016560000000w))
       (BoundedInterval64 (BoundedSigned64 F 1999996000000w)
         (BoundedSigned64 F 2032936000000w))
       (BoundedInterval64 (BoundedSigned64 F 247946998849w)
         (BoundedSigned64 F 247953146774w))
       (BoundedInterval64 (BoundedSigned64 F 245949700334w)
         (BoundedSigned64 F 250000500002w))
       (BoundedInterval64 (BoundedSigned64 F 29755729341w)
         (BoundedSigned64 F 31250062501w))]
End

Definition bounded_case10173_decimal_packet0_source_aligned_def:
  bounded_case10173_decimal_packet0_source_aligned =
    case bounded_case10173_decimal_packet0 of
    | BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals =>
      BoundedCase10173Packet radii center_environment box_environment
        bounded_case10173_decimal_packet0_source_sqrt_certificates
        center_root_delta center_root_four_x0 center_reciprocals
        box_root_delta box_root_four_x0 box_reciprocals
End

Theorem bounded_case10173_decimal_packet0_source_aligned_accepts:
  bounded_case10173_decimal_packet_accepts
    bounded_case10173_decimal_packet0_source_aligned
Proof
  rw [bounded_case10173_decimal_packet0_source_aligned_def,
      bounded_case10173_decimal_packet0_source_sqrt_certificates_def,
      bounded_case10173_decimal_packet_accepts_def,
      compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case10173_decimal_packet0_source_aligned_sqrt_binding:
  ?object_job root_record.
    bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp =
        SOME (Pair object_job root_record) /\
    bounded_case10173_decimal_packet_sqrt_roots_bind_object_job
      bounded_case10173_decimal_packet0_source_aligned object_job
Proof
  simp
    [compute_boundedCase10173RootBindingTheory.bounded_case10173_checked_call_first_job_root_def,
     bounded_case10173_decimal_packet_sqrt_roots_bind_object_job_def,
     bounded_case10173_decimal_packet_sqrt_roots_def,
     bounded_case10173_sqrt64_center_intervals_def,
     bounded_case10173_sqrt64_box_intervals_def,
     bounded_case10173_decimal_packet0_source_aligned_def,
     bounded_case10173_decimal_packet0_source_sqrt_certificates_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_decimal_natural_floor64_def,
     compute_boundedObjectDecimalQTheory.bounded_decimal_natural_ceil64_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def,
     compute_pureFastTheory.compute_exp_to_cv_def,
     compute_boundedIntervalTheory.bounded_interval64_valid_def]
  >> EVAL_TAC
  >> qexists_tac
       `BoundedInterval64
          (BoundedSigned64 F 52322170000000w)
          (BoundedSigned64 F 52322220000000w)`
  >> qexists_tac
       `BoundedInterval64
          (BoundedSigned64 F 45543675000000w)
          (BoundedSigned64 F 58520311000000w)`
  >> simp
       [compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def]
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case10173_decimal_packet0_source_aligned_root_binding:
  ?object_job root_record.
    bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp =
        SOME (Pair object_job root_record) /\
    bounded_case10173_decimal_packet_roots_bind_object_record
      bounded_case10173_decimal_packet0_source_aligned root_record
Proof
  simp
    [compute_boundedCase10173RootBindingTheory.bounded_case10173_checked_call_first_job_root_def,
     bounded_case10173_decimal_packet_roots_bind_object_record_def,
     compute_boundedCase10173RootBindingTheory.bounded_case10173_packet_root_intervals_def,
     bounded_case10173_decimal_packet0_source_aligned_def,
     bounded_case10173_decimal_packet0_source_sqrt_certificates_def,
     compute_boundedObjectDecimalDecodeTheory.bounded_object_decimal_interval64_list_def,
     compute_boundedObjectDecimalDecodeTheory.bounded_object_decimal_interval64_def,
     compute_boundedObjectDecimalDecodeTheory.bounded_object_decimal_signed64_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def,
     compute_pureFastTheory.compute_exp_to_cv_def,
     compute_boundedIntervalTheory.bounded_interval64_valid_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case10173_decimal_packet0_source_aligned_box_exact_binding:
  ?object_job root_record.
    bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp =
        SOME (Pair object_job root_record) /\
    bounded_case10173_decimal_packet_box_exact_object_job
      bounded_case10173_decimal_packet0_source_aligned object_job
Proof
  simp
    [compute_boundedCase10173RootBindingTheory.bounded_case10173_checked_call_first_job_root_def,
     bounded_case10173_decimal_packet_box_exact_object_job_def,
     compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
     bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_decimal_natural_floor64_def,
     compute_boundedObjectDecimalQTheory.bounded_decimal_natural_ceil64_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def,
     compute_pureFastTheory.compute_exp_to_cv_def,
     compute_boundedIntervalTheory.bounded_interval64_valid_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case10173_decimal_packet0_source_aligned_exact_auxiliary_binding:
  ?object_job root_record.
    bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp =
        SOME (Pair object_job root_record) /\
    bounded_case10173_decimal_packet_exact_auxiliary_binding
      bounded_case10173_decimal_packet0_source_aligned object_job root_record
Proof
  qx_choose_then `sqrt_job`
    (qx_choose_then `sqrt_root` strip_assume_tac)
    bounded_case10173_decimal_packet0_source_aligned_sqrt_binding
  >> qx_choose_then `root_job`
       (qx_choose_then `root_root` strip_assume_tac)
       bounded_case10173_decimal_packet0_source_aligned_root_binding
  >> `sqrt_job = root_job /\ sqrt_root = root_root` by gvs []
  >> qexists_tac `sqrt_job`
  >> qexists_tac `sqrt_root`
  >> simp [bounded_case10173_decimal_packet_exact_auxiliary_binding_def]
  >> metis_tac []
QED

Theorem bounded_case10173_decimal_packet0_source_aligned_exact_input_binding:
  ?object_job root_record.
    bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp =
        SOME (Pair object_job root_record) /\
    bounded_case10173_decimal_packet_exact_input_binding
      bounded_case10173_decimal_packet0_source_aligned object_job root_record
Proof
  qx_choose_then `box_job`
    (qx_choose_then `box_root` strip_assume_tac)
    bounded_case10173_decimal_packet0_source_aligned_box_exact_binding
  >> qx_choose_then `aux_job`
       (qx_choose_then `aux_root` strip_assume_tac)
       bounded_case10173_decimal_packet0_source_aligned_exact_auxiliary_binding
  >> `box_job = aux_job /\ box_root = aux_root` by gvs []
  >> qexists_tac `box_job`
  >> qexists_tac `box_root`
  >> simp [bounded_case10173_decimal_packet_exact_input_binding_def]
  >> metis_tac []
QED

val _ = export_theory ();
