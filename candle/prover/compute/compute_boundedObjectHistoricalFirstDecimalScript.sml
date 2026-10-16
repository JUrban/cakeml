(*****************************************************************************
 * Exact object traces for the historical decimal center calculation.
 *****************************************************************************)
Theory compute_boundedObjectHistoricalFirstDecimal
Ancestors
  compute_boundedObjectHistoricalListDecimal
Libs
  bossLib preamble intLib

Theorem bounded_raw128_interval_mul64_corner_members:
  bounded_raw128_interval_mul64_unchecked
      (left_lower,left_upper)
      (BoundedInterval64 right_lower right_upper) = SOME (lower,upper) ==>
  (bounded_signed192_to_int lower =
       bounded_signed128_to_int left_lower *
         bounded_signed64_to_int right_lower \/
   bounded_signed192_to_int lower =
       bounded_signed128_to_int left_lower *
         bounded_signed64_to_int right_upper \/
   bounded_signed192_to_int lower =
       bounded_signed128_to_int left_upper *
         bounded_signed64_to_int right_lower \/
   bounded_signed192_to_int lower =
       bounded_signed128_to_int left_upper *
         bounded_signed64_to_int right_upper) /\
  (bounded_signed192_to_int upper =
       bounded_signed128_to_int left_lower *
         bounded_signed64_to_int right_lower \/
   bounded_signed192_to_int upper =
       bounded_signed128_to_int left_lower *
         bounded_signed64_to_int right_upper \/
   bounded_signed192_to_int upper =
       bounded_signed128_to_int left_upper *
         bounded_signed64_to_int right_lower \/
   bounded_signed192_to_int upper =
       bounded_signed128_to_int left_upper *
         bounded_signed64_to_int right_upper)
Proof
  Cases_on `bounded_signed128_nonnegative left_lower`
  >> Cases_on `bounded_signed128_nonpositive left_upper`
  >> Cases_on `bounded_signed64_nonnegative right_lower`
  >> Cases_on `bounded_signed64_nonpositive right_upper`
  >> rw
       [compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_mul64_unchecked_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_product_from_pairs_value
  >> imp_res_tac
       compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_product_mixed_value
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_raw128_interval_mul64_object_extrema:
  bounded_signed128_normalized left_lower /\
  bounded_signed128_normalized left_upper /\
  bounded_signed128_to_int left_lower <=
    bounded_signed128_to_int left_upper /\
  bounded_interval64_valid
    (BoundedInterval64 right_lower right_upper) /\
  bounded_raw128_interval_mul64_unchecked
      (left_lower,left_upper)
      (BoundedInterval64 right_lower right_upper) = SOME (lower,upper) ==>
  bounded_signed192_to_int lower =
    bounded_object_int_min4
      (bounded_signed128_to_int left_lower *
        bounded_signed64_to_int right_lower)
      (bounded_signed128_to_int left_lower *
        bounded_signed64_to_int right_upper)
      (bounded_signed128_to_int left_upper *
        bounded_signed64_to_int right_lower)
      (bounded_signed128_to_int left_upper *
        bounded_signed64_to_int right_upper) /\
  bounded_signed192_to_int upper =
    bounded_object_int_max4
      (bounded_signed128_to_int left_lower *
        bounded_signed64_to_int right_lower)
      (bounded_signed128_to_int left_lower *
        bounded_signed64_to_int right_upper)
      (bounded_signed128_to_int left_upper *
        bounded_signed64_to_int right_lower)
      (bounded_signed128_to_int left_upper *
        bounded_signed64_to_int right_upper)
Proof
  strip_tac
  >> mp_tac
       (INST
         [``(left_lower:int)`` |->
            ``bounded_signed128_to_int
                (left_lower:bounded_signed128)``,
          ``(left_upper:int)`` |->
            ``bounded_signed128_to_int
                (left_upper:bounded_signed128)``,
          ``(right_lower:int)`` |->
            ``bounded_signed64_to_int
                (right_lower:bounded_signed64)``,
          ``(right_upper:int)`` |->
            ``bounded_signed64_to_int
                (right_upper:bounded_signed64)``,
          ``(lower:int)`` |->
            ``bounded_signed192_to_int
                (lower:bounded_signed192)``,
          ``(upper:int)`` |->
            ``bounded_signed192_to_int
                (upper:bounded_signed192)``]
         compute_boundedObjectDecimalIntervalTheory.bounded_object_int_product_extrema_from_bounds)
  >> impl_tac
  >- (fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
      >> conj_tac
      >- (drule bounded_raw128_interval_mul64_corner_members
          >> simp [])
      >> conj_tac
      >- (drule bounded_raw128_interval_mul64_corner_members
          >> simp [])
      >> rpt gen_tac
      >> strip_tac
      >> mp_tac
           (Q.INST
             [`left_lower` |-> `left_lower`,
              `left_upper` |-> `left_upper`,
              `right` |->
                `BoundedInterval64 right_lower right_upper`,
              `left_value` |-> `left_value`,
              `right_value` |-> `right_value`,
              `lower` |-> `lower`, `upper` |-> `upper`]
             compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_mul64_contains_product)
      >> simp
           [compute_boundedIntervalTheory.bounded_interval64_contains_int_def,
            compute_boundedIntervalTheory.bounded_interval64_lower_def,
            compute_boundedIntervalTheory.bounded_interval64_upper_def,
            compute_boundedIntervalTheory.bounded_interval64_valid_def,
            compute_boundedSignedEndpointTheory.bounded_signed64_le_correct])
  >> simp []
QED

Theorem bounded_interval64_raw_mul_bounds_normalized_ordered:
  bounded_interval64_valid left /\
  bounded_interval64_valid right ==>
  let bounds = bounded_interval64_raw_mul_bounds_unchecked left right in
  bounded_signed128_normalized (FST bounds) /\
  bounded_signed128_normalized (SND bounds) /\
  bounded_signed128_to_int (FST bounds) <=
    bounded_signed128_to_int (SND bounds)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`left` |-> `BoundedInterval64 b b0`,
          `right` |-> `BoundedInterval64 b' b0'`,
          `left_value` |-> `bounded_signed64_to_int b`,
          `right_value` |-> `bounded_signed64_to_int b'`]
         compute_boundedTaylorMulTheory.bounded_interval64_raw_mul_bounds_contains_product)
  >> impl_tac
  >- fs
       [compute_boundedIntervalTheory.bounded_interval64_contains_int_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
  >> strip_tac
  >> fs [LET_THM]
  >> intLib.ARITH_TAC
QED

Definition bounded_object_fs_historical_raw_cubic_def:
  bounded_object_fs_historical_raw_cubic first second third =
    if ~bounded_interval64_valid first \/
       ~bounded_interval64_valid second \/
       ~bounded_interval64_valid third
    then NONE
    else
      case bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv first)
        (bounded_interval64_object_cv second) of
      | NONE => NONE
      | SOME raw_product =>
          bounded_object_fs_raw_interval_mul raw_product
            (bounded_interval64_object_cv third)
End

Theorem bounded_object_fs_historical_raw_cubic_exact:
  bounded_historical_raw_cubic first_interval second_interval third_interval =
    SOME (lower,upper) ==>
  ?object_lower object_upper.
    bounded_object_fs_historical_raw_cubic
      first_interval second_interval third_interval =
      SOME (Pair object_lower object_upper) /\
    bounded_object_signed_int object_lower =
      SOME (bounded_signed192_to_int lower) /\
    bounded_object_signed_int object_upper =
      SOME (bounded_signed192_to_int upper)
Proof
  Cases_on `third_interval`
  >> rw
       [compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubic_def]
  >> every_case_tac
  >> gvs []
  >> mp_tac
       (Q.INST
         [`left` |-> `first_interval`, `right` |-> `second_interval`]
         compute_boundedObjectDecimalFusedTheory.bounded_interval64_raw_mul_bounds_object_values)
  >> impl_tac
  >- simp []
  >> simp [LET_THM]
  >> disch_then
       (qx_choose_then `object_first_lower`
         (qx_choose_then `object_first_upper` strip_assume_tac))
  >> mp_tac
       (Q.INST
         [`left` |-> `first_interval`, `right` |-> `second_interval`]
         bounded_interval64_raw_mul_bounds_normalized_ordered)
  >> impl_tac
  >- simp []
  >> simp [LET_THM]
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`left_lower` |-> `object_first_lower`,
          `left_upper` |-> `object_first_upper`,
          `right_lower` |-> `bounded_signed64_object_cv b`,
          `right_upper` |-> `bounded_signed64_object_cv b0`,
          `left_lower_value` |->
            `bounded_signed128_to_int
              (FST (bounded_interval64_raw_mul_bounds_unchecked
                first_interval second_interval))`,
          `left_upper_value` |->
            `bounded_signed128_to_int
              (SND (bounded_interval64_raw_mul_bounds_unchecked
                first_interval second_interval))`,
          `right_lower_value` |-> `bounded_signed64_to_int b`,
          `right_upper_value` |-> `bounded_signed64_to_int b0`]
         compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_mul_general_exists)
  >> impl_tac
  >- simp []
  >> disch_then
       (qx_choose_then `object_lower`
         (qx_choose_then `object_upper` assume_tac))
  >> mp_tac
       (Q.INST
         [`left_lower` |-> `object_first_lower`,
          `left_upper` |-> `object_first_upper`,
          `right_lower` |-> `bounded_signed64_object_cv b`,
          `right_upper` |-> `bounded_signed64_object_cv b0`,
          `left_lower_value` |->
            `bounded_signed128_to_int
              (FST (bounded_interval64_raw_mul_bounds_unchecked
                first_interval second_interval))`,
          `left_upper_value` |->
            `bounded_signed128_to_int
              (SND (bounded_interval64_raw_mul_bounds_unchecked
                first_interval second_interval))`,
          `right_lower_value` |-> `bounded_signed64_to_int b`,
          `right_upper_value` |-> `bounded_signed64_to_int b0`,
          `lower` |-> `object_lower`, `upper` |-> `object_upper`]
         compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_mul_general_signed_values)
  >> impl_tac
  >- simp []
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`left_lower` |->
            `FST (bounded_interval64_raw_mul_bounds_unchecked
              first_interval second_interval)`,
          `left_upper` |->
            `SND (bounded_interval64_raw_mul_bounds_unchecked
              first_interval second_interval)`,
          `right_lower` |-> `b`, `right_upper` |-> `b0`,
          `lower` |-> `lower`, `upper` |-> `upper`]
         bounded_raw128_interval_mul64_object_extrema)
  >> impl_tac
  >- simp []
  >> strip_tac
  >> qexists_tac `object_lower`
  >> qexists_tac `object_upper`
  >> gvs
       [bounded_object_fs_historical_raw_cubic_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def]
QED

Definition bounded_object_fs_raw_interval_neg_def:
  bounded_object_fs_raw_interval_neg (Pair lower upper : cv) =
    (case bounded_object_fs_raw_neg upper of
     | NONE => NONE
     | SOME negative_upper =>
       case bounded_object_fs_raw_neg lower of
       | NONE => NONE
       | SOME negative_lower => SOME (Pair negative_upper negative_lower)) /\
  bounded_object_fs_raw_interval_neg _ = NONE
End

Theorem bounded_object_fs_raw_interval_neg_signed_exact:
  bounded_object_signed_int object_lower = SOME lower_value /\
  bounded_object_signed_int object_upper = SOME upper_value ==>
  ?negative_upper negative_lower.
    bounded_object_fs_raw_interval_neg
      (Pair object_lower object_upper) =
      SOME (Pair negative_upper negative_lower) /\
    bounded_object_signed_int negative_upper = SOME (-upper_value) /\
    bounded_object_signed_int negative_lower = SOME (-lower_value)
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`source` |-> `object_upper`, `value` |-> `upper_value`]
         compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_neg_signed_exists)
  >> impl_tac
  >- simp []
  >> disch_then (qx_choose_then `negative_upper` strip_assume_tac)
  >> mp_tac
       (Q.INST [`source` |-> `object_lower`, `value` |-> `lower_value`]
         compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_neg_signed_exists)
  >> impl_tac
  >- simp []
  >> disch_then (qx_choose_then `negative_lower` strip_assume_tac)
  >> qexists_tac `negative_upper`
  >> qexists_tac `negative_lower`
  >> simp [bounded_object_fs_raw_interval_neg_def]
QED

Definition bounded_object_fs_historical_raw_cubic_signed_def:
  bounded_object_fs_historical_raw_cubic_signed
      first_interval second_interval third_interval negative =
    case bounded_object_fs_historical_raw_cubic
      first_interval second_interval third_interval of
    | NONE => NONE
    | SOME raw =>
        if negative then bounded_object_fs_raw_interval_neg raw
        else SOME raw
End

Theorem bounded_object_fs_historical_raw_cubic_signed_exact:
  bounded_historical_raw_cubic_signed
      first_interval second_interval third_interval negative =
    SOME (lower,upper) ==>
  ?object_lower object_upper.
    bounded_object_fs_historical_raw_cubic_signed
      first_interval second_interval third_interval negative =
      SOME (Pair object_lower object_upper) /\
    bounded_object_signed_int object_lower =
      SOME (bounded_signed192_to_int lower) /\
    bounded_object_signed_int object_upper =
      SOME (bounded_signed192_to_int upper)
Proof
  rw
    [compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubic_signed_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_fs_historical_raw_cubic_exact
  >> imp_res_tac bounded_object_fs_raw_interval_neg_signed_exact
  >> gvs
       [bounded_object_fs_historical_raw_cubic_signed_def,
        compute_boundedHistoricalDeltaTheory.bounded_signed192_neg_value]
  >> metis_tac []
QED

Definition bounded_object_raw_interval_cv_list_rel_def:
  (bounded_object_raw_interval_cv_list_rel (Num 0) [] <=> T) /\
  (bounded_object_raw_interval_cv_list_rel
      (Pair (Pair object_lower object_upper) object_rest)
      ((source_lower,source_upper)::source_rest) <=>
    bounded_object_signed_int object_lower =
      SOME (bounded_signed192_to_int source_lower) /\
    bounded_object_signed_int object_upper =
      SOME (bounded_signed192_to_int source_upper) /\
    bounded_object_raw_interval_cv_list_rel object_rest source_rest) /\
  (bounded_object_raw_interval_cv_list_rel _ _ <=> F)
End

Definition bounded_object_fs_historical_raw_cubics_def:
  bounded_object_fs_historical_raw_cubics [] = SOME (Num 0 : cv) /\
  bounded_object_fs_historical_raw_cubics
      ((first_interval,second_interval,third_interval,negative)::rest) =
    case bounded_object_fs_historical_raw_cubic_signed
      first_interval second_interval third_interval negative of
    | NONE => NONE
    | SOME raw =>
      case bounded_object_fs_historical_raw_cubics rest of
      | NONE => NONE
      | SOME raw_rest => SOME (Pair raw raw_rest)
End

Theorem bounded_object_fs_historical_raw_cubics_exact:
  !results.
    bounded_historical_raw_cubics terms = SOME results ==>
    ?object_results.
      bounded_object_fs_historical_raw_cubics terms =
        SOME object_results /\
      bounded_object_raw_interval_cv_list_rel object_results results
Proof
  Induct_on `terms`
  >- simp
       [compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubics_def,
        bounded_object_fs_historical_raw_cubics_def,
        bounded_object_raw_interval_cv_list_rel_def]
  >> rpt gen_tac
  >> PairCases_on `h`
  >> rw
       [compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubics_def]
  >> every_case_tac
  >> gvs []
  >> PairCases_on `x'`
  >> imp_res_tac bounded_object_fs_historical_raw_cubic_signed_exact
  >> res_tac
  >> qexists_tac `Pair (Pair object_lower object_upper) object_results`
  >> gvs
       [bounded_object_fs_historical_raw_cubics_def,
        bounded_object_raw_interval_cv_list_rel_def]
QED

(* The preceding helpers are convenient for source constants.  The complete
   checker also needs the third cubic factor to be an interval produced by an
   earlier encoded calculation.  These variants therefore consume encoded
   intervals directly and expose the compositional refinement needed by the
   historical delta calculation. *)
Definition bounded_object_fs_historical_raw_cubic_encoded_def:
  bounded_object_fs_historical_raw_cubic_encoded first second third =
    case bounded_object_fs_raw_interval_mul first second of
    | NONE => NONE
    | SOME raw_product =>
        bounded_object_fs_raw_interval_mul raw_product third
End

Theorem bounded_object_fs_historical_raw_cubic_encoded_exact:
  bounded_historical_raw_cubic
      first_interval second_interval third_interval = SOME (lower,upper) ==>
  ?object_lower object_upper.
    bounded_object_fs_historical_raw_cubic_encoded
      (bounded_interval64_object_cv first_interval)
      (bounded_interval64_object_cv second_interval)
      (bounded_interval64_object_cv third_interval) =
      SOME (Pair object_lower object_upper) /\
    bounded_object_signed_int object_lower =
      SOME (bounded_signed192_to_int lower) /\
    bounded_object_signed_int object_upper =
      SOME (bounded_signed192_to_int upper)
Proof
  strip_tac
  >> imp_res_tac bounded_object_fs_historical_raw_cubic_exact
  >> Cases_on
       `~bounded_interval64_valid first_interval \/
        ~bounded_interval64_valid second_interval \/
        ~bounded_interval64_valid third_interval`
  >> gvs
       [compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubic_def,
        bounded_object_fs_historical_raw_cubic_def,
        bounded_object_fs_historical_raw_cubic_encoded_def]
  >> metis_tac []
QED

Definition bounded_object_fs_historical_raw_cubic_signed_encoded_def:
  bounded_object_fs_historical_raw_cubic_signed_encoded
      first second third negative =
    case bounded_object_fs_historical_raw_cubic_encoded
      first second third of
    | NONE => NONE
    | SOME raw =>
        if negative then bounded_object_fs_raw_interval_neg raw
        else SOME raw
End

Theorem bounded_object_fs_historical_raw_cubic_signed_encoded_exact:
  bounded_historical_raw_cubic_signed
      first_interval second_interval third_interval negative =
      SOME (lower,upper) ==>
  ?object_lower object_upper.
    bounded_object_fs_historical_raw_cubic_signed_encoded
      (bounded_interval64_object_cv first_interval)
      (bounded_interval64_object_cv second_interval)
      (bounded_interval64_object_cv third_interval) negative =
      SOME (Pair object_lower object_upper) /\
    bounded_object_signed_int object_lower =
      SOME (bounded_signed192_to_int lower) /\
    bounded_object_signed_int object_upper =
      SOME (bounded_signed192_to_int upper)
Proof
  rw
    [compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubic_signed_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_fs_historical_raw_cubic_encoded_exact
  >> imp_res_tac bounded_object_fs_raw_interval_neg_signed_exact
  >> gvs
       [bounded_object_fs_historical_raw_cubic_signed_encoded_def,
        compute_boundedHistoricalDeltaTheory.bounded_signed192_neg_value]
  >> metis_tac []
QED

Definition bounded_object_raw_cubic_input_cv_rel_def:
  bounded_object_raw_cubic_input_cv_rel
      (object_first,object_second,object_third,object_negative)
      (source_first,source_second,source_third,source_negative) <=>
    object_first = bounded_interval64_object_cv source_first /\
    object_second = bounded_interval64_object_cv source_second /\
    object_third = bounded_interval64_object_cv source_third /\
    object_negative = source_negative
End

Definition bounded_object_fs_historical_raw_cubics_encoded_def:
  bounded_object_fs_historical_raw_cubics_encoded [] =
      SOME (Num 0 : cv) /\
  bounded_object_fs_historical_raw_cubics_encoded
      ((first,second,third,negative)::rest) =
    case bounded_object_fs_historical_raw_cubic_signed_encoded
      first second third negative of
    | NONE => NONE
    | SOME raw =>
      case bounded_object_fs_historical_raw_cubics_encoded rest of
      | NONE => NONE
      | SOME raw_rest => SOME (Pair raw raw_rest)
End

Theorem bounded_object_fs_historical_raw_cubics_encoded_exact:
  !object_terms source_terms results.
    LIST_REL bounded_object_raw_cubic_input_cv_rel
      object_terms source_terms /\
    bounded_historical_raw_cubics source_terms = SOME results ==>
    ?object_results.
      bounded_object_fs_historical_raw_cubics_encoded object_terms =
        SOME object_results /\
      bounded_object_raw_interval_cv_list_rel object_results results
Proof
  Induct_on `source_terms`
  >- (rpt gen_tac
      >> Cases_on `object_terms`
      >> simp
           [compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubics_def,
            bounded_object_fs_historical_raw_cubics_encoded_def,
            bounded_object_raw_interval_cv_list_rel_def])
  >> rpt gen_tac
  >> Cases_on `object_terms`
  >- simp [LIST_REL_def]
  >> rename1 `object_head::object_rest`
  >> PairCases_on `h`
  >> PairCases_on `object_head`
  >> rw
       [LIST_REL_def, bounded_object_raw_cubic_input_cv_rel_def,
        compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubics_def]
  >> every_case_tac
  >> gvs []
  >> PairCases_on `x'`
  >> imp_res_tac
       bounded_object_fs_historical_raw_cubic_signed_encoded_exact
  >> res_tac
  >> qexists_tac `Pair (Pair object_lower object_upper) object_results`
  >> gvs
       [bounded_object_fs_historical_raw_cubics_encoded_def,
        bounded_object_raw_interval_cv_list_rel_def]
QED

Definition bounded_object_fs_raw_interval_sum_aux_def:
  bounded_object_fs_raw_interval_sum_aux (Num 0) accumulator =
    SOME accumulator /\
  bounded_object_fs_raw_interval_sum_aux (Num (SUC malformed)) accumulator =
    NONE /\
  bounded_object_fs_raw_interval_sum_aux (Pair entry rest) accumulator =
    case bounded_object_fs_raw_interval_add accumulator entry of
    | NONE => NONE
    | SOME next => bounded_object_fs_raw_interval_sum_aux rest next
End

Definition bounded_object_fs_raw_interval_sum_def:
  bounded_object_fs_raw_interval_sum values =
    bounded_object_fs_raw_interval_sum_aux values
      (Pair (Pair (Num 0) (Num 0)) (Pair (Num 0) (Num 0)))
End

Theorem bounded_object_fs_raw_interval_sum_aux_exact:
  !source_values object_values source_lower source_upper
   object_lower object_upper result_lower result_upper.
    bounded_object_raw_interval_cv_list_rel object_values source_values /\
    bounded_object_signed_int object_lower =
      SOME (bounded_signed192_to_int source_lower) /\
    bounded_object_signed_int object_upper =
      SOME (bounded_signed192_to_int source_upper) /\
    bounded_signed192_interval_sum_aux
      source_values source_lower source_upper =
        SOME (result_lower,result_upper) ==>
    ?object_result_lower object_result_upper.
      bounded_object_fs_raw_interval_sum_aux object_values
        (Pair object_lower object_upper) =
          SOME (Pair object_result_lower object_result_upper) /\
      bounded_object_signed_int object_result_lower =
        SOME (bounded_signed192_to_int result_lower) /\
      bounded_object_signed_int object_result_upper =
        SOME (bounded_signed192_to_int result_upper)
Proof
  Induct_on `source_values`
  >- (rpt gen_tac
      >> Cases_on `object_values`
      >- (Cases_on `n`
          >> gvs
               [bounded_object_raw_interval_cv_list_rel_def,
                compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_sum_aux_def,
                bounded_object_fs_raw_interval_sum_aux_def])
      >> Cases_on `c`
      >> gvs
           [bounded_object_raw_interval_cv_list_rel_def,
            compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_sum_aux_def])
  >> rpt gen_tac
  >> PairCases_on `h`
  >> Cases_on `object_values`
  >- (Cases_on `n`
      >> gvs [bounded_object_raw_interval_cv_list_rel_def])
  >> Cases_on `c`
  >- gvs [bounded_object_raw_interval_cv_list_rel_def]
  >> rw [bounded_object_raw_interval_cv_list_rel_def]
  >> fs
       [compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_sum_aux_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac compute_boundedWideSignedTheory.bounded_signed192_add_value
  >> mp_tac
       (Q.INST
         [`left_lower` |-> `object_lower`,
          `left_upper` |-> `object_upper`,
          `right_lower` |-> `c'`, `right_upper` |-> `c0'`,
          `left_lower_value` |-> `bounded_signed192_to_int source_lower`,
          `left_upper_value` |-> `bounded_signed192_to_int source_upper`,
          `right_lower_value` |-> `bounded_signed192_to_int h0`,
          `right_upper_value` |-> `bounded_signed192_to_int h1`]
         compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_interval_add_signed_values)
  >> simp []
  >> disch_then
       (qx_choose_then `next_object_lower`
         (qx_choose_then `next_object_upper` strip_assume_tac))
  >> qpat_x_assum
       `!object_values source_lower source_upper object_lower object_upper
          result_lower result_upper. _`
       (mp_tac o
        Q.SPECL
          [`c0`, `x'`, `x`, `next_object_lower`, `next_object_upper`,
           `result_lower`, `result_upper`])
  >> simp []
  >> disch_then
       (qx_choose_then `object_result_lower`
         (qx_choose_then `object_result_upper` strip_assume_tac))
  >> qexists_tac `object_result_lower`
  >> qexists_tac `object_result_upper`
  >> gvs [bounded_object_fs_raw_interval_sum_aux_def]
QED

Theorem bounded_object_fs_raw_interval_sum_exact:
  bounded_signed192_interval_sum source_values =
    SOME (result_lower,result_upper) /\
  bounded_object_raw_interval_cv_list_rel object_values source_values ==>
  ?object_result_lower object_result_upper.
    bounded_object_fs_raw_interval_sum object_values =
      SOME (Pair object_result_lower object_result_upper) /\
    bounded_object_signed_int object_result_lower =
      SOME (bounded_signed192_to_int result_lower) /\
    bounded_object_signed_int object_result_upper =
      SOME (bounded_signed192_to_int result_upper)
Proof
  rw
    [compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_sum_def,
     bounded_object_fs_raw_interval_sum_def]
  >> mp_tac
       (Q.SPECL
         [`source_values`, `object_values`,
          `bounded_signed192_make F bounded192_zero`,
          `bounded_signed192_make F bounded192_zero`,
          `Pair (Num 0) (Num 0)`, `Pair (Num 0) (Num 0)`,
          `result_lower`, `result_upper`]
         bounded_object_fs_raw_interval_sum_aux_exact)
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        compute_boundedWideSignedTheory.bounded_signed192_make_value,
        compute_boundedWideTheory.bounded192_zero_def,
        compute_boundedTheory.bounded192_to_num_def]
QED

Theorem bounded_object_q_ceil_div_decimal_squared:
  bounded_object_q_ceil_div numerator 1000000000000000000000000 =
    (numerator + 999999999999999999999999) DIV
      1000000000000000000000000
Proof
  simp
    [compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_def]
  >> rpt strip_tac
  >> mp_tac (Q.SPEC `1000000000000000000000000`
       arithmeticTheory.CEILING_DIV)
  >> simp [arithmeticTheory.CEILING_DIV_def, MIN_DEF]
QED

Theorem bounded_signed192_floor64_decimal_squared_object_exact:
  bounded_signed192_floor64_decimal_squared source = SOME result ==>
  bounded_object_fs_floor_div
      (bounded_signed192_object_cv source)
      1000000000000000000000000 =
    SOME (bounded_signed64_object_cv result)
Proof
  Cases_on `source`
  >> Cases_on `b`
  >> rw
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_signed192_floor64_decimal_squared_def]
  >> every_case_tac
  >> gvs
       [compute_boundedObjectDecimalFusedTheory.bounded_signed192_object_cv_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def,
        bounded_object_q_ceil_div_decimal_squared,
        compute_boundedHistoricalDeltaDecimalTheory.bounded192_floor64_decimal_squared_def,
        compute_boundedHistoricalDeltaDecimalTheory.bounded192_ceil64_decimal_squared_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_make_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        LET_THM]
  >> fs [compute_boundedTheory.bounded_word_base_eq, LESS_MOD,
         GSYM arithmeticTheory.NOT_ZERO_LT_ZERO]
  >> Cases_on `bounded192_to_num b0 = 0`
  >> simp [arithmeticTheory.DIV_EQ_0]
QED

Theorem bounded_signed192_ceil64_decimal_squared_object_exact:
  bounded_signed192_ceil64_decimal_squared source = SOME result ==>
  bounded_object_fs_ceil_div
      (bounded_signed192_object_cv source)
      1000000000000000000000000 =
    SOME (bounded_signed64_object_cv result)
Proof
  Cases_on `source`
  >> Cases_on `b`
  >> rw
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_signed192_ceil64_decimal_squared_def]
  >> every_case_tac
  >> gvs
       [compute_boundedObjectDecimalFusedTheory.bounded_signed192_object_cv_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def,
        bounded_object_q_ceil_div_decimal_squared,
        compute_boundedHistoricalDeltaDecimalTheory.bounded192_floor64_decimal_squared_def,
        compute_boundedHistoricalDeltaDecimalTheory.bounded192_ceil64_decimal_squared_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_make_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        LET_THM]
  >> fs [compute_boundedTheory.bounded_word_base_eq, LESS_MOD,
         GSYM arithmeticTheory.NOT_ZERO_LT_ZERO]
  >> Cases_on `bounded192_to_num b0 = 0`
  >> Cases_on
       `bounded192_to_num b0 DIV 1000000000000000000000000 = 0`
  >> simp []
QED

Theorem bounded_object_fs_raw_interval_round_signed192_decimal_squared_exact:
  bounded_object_signed_int object_lower =
      SOME (bounded_signed192_to_int word_lower) /\
  bounded_object_signed_int object_upper =
      SOME (bounded_signed192_to_int word_upper) /\
  bounded_signed192_floor64_decimal_squared word_lower =
      SOME result_lower /\
  bounded_signed192_ceil64_decimal_squared word_upper =
      SOME result_upper ==>
  bounded_object_fs_raw_interval_round 1000000000000000000000000
      (Pair object_lower object_upper) =
    SOME
      (bounded_interval64_object_cv
        (BoundedInterval64 result_lower result_upper))
Proof
  strip_tac
  >> `bounded_object_fs_raw_interval_round 1000000000000000000000000
        (Pair object_lower object_upper) =
      bounded_object_fs_raw_interval_round 1000000000000000000000000
        (Pair
          (bounded_signed192_object_cv word_lower)
          (bounded_signed192_object_cv word_upper))` by
       (irule
          compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_extensional
        >> simp [])
  >> pop_assum SUBST1_TAC
  >> irule
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_exact
  >> simp
       [bounded_signed192_floor64_decimal_squared_object_exact,
        bounded_signed192_ceil64_decimal_squared_object_exact]
QED

Definition bounded_object_fs_historical_raw_round_decimal_def:
  bounded_object_fs_historical_raw_round_decimal raw =
    bounded_object_fs_raw_interval_round
      1000000000000000000000000 raw
End

Theorem bounded_object_fs_historical_raw_round_decimal_exact:
  bounded_historical_raw_round_decimal (word_lower,word_upper) =
      SOME result /\
  bounded_object_signed_int object_lower =
      SOME (bounded_signed192_to_int word_lower) /\
  bounded_object_signed_int object_upper =
      SOME (bounded_signed192_to_int word_upper) ==>
  bounded_object_fs_historical_raw_round_decimal
      (Pair object_lower object_upper) =
    SOME (bounded_interval64_object_cv result)
Proof
  Cases_on `result`
  >> rw
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_raw_round_decimal_def]
  >> every_case_tac
  >> gvs [bounded_object_fs_historical_raw_round_decimal_def]
  >> irule
       bounded_object_fs_raw_interval_round_signed192_decimal_squared_exact
  >> conj_tac
  >- (qexists_tac `word_lower` >> simp [])
  >> qexists_tac `word_upper`
  >> simp []
QED

Theorem bounded_object_fs_raw_interval_sum_round_decimal_exact:
  bounded_signed192_interval_sum source_values = SOME source_raw /\
  bounded_object_raw_interval_cv_list_rel object_values source_values /\
  bounded_historical_raw_round_decimal source_raw = SOME result ==>
  (case bounded_object_fs_raw_interval_sum object_values of
   | NONE => NONE
   | SOME object_raw =>
       bounded_object_fs_historical_raw_round_decimal object_raw) =
    SOME (bounded_interval64_object_cv result)
Proof
  PairCases_on `source_raw`
  >> rw []
  >> imp_res_tac bounded_object_fs_raw_interval_sum_exact
  >> imp_res_tac bounded_object_fs_historical_raw_round_decimal_exact
  >> gvs []
QED

Definition bounded_object_fs_historical_delta_x4_value_decimal_def:
  bounded_object_fs_historical_delta_x4_value_decimal environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      case bounded_object_fs_interval_neg
        (bounded_interval64_object_cv x0) of
      | NONE => NONE
      | SOME negative_x0 =>
        case bounded_object_fs_interval_neg
          (bounded_interval64_object_cv x3) of
        | NONE => NONE
        | SOME negative_x3 =>
          case bounded_object_fs_interval_sum
            (Pair negative_x0
              (Pair (bounded_interval64_object_cv x1)
                (Pair (bounded_interval64_object_cv x2)
                  (Pair negative_x3
                    (Pair (bounded_interval64_object_cv x4)
                      (Pair (bounded_interval64_object_cv x5)
                        (Num 0))))))) of
          | NONE => NONE
          | SOME linear =>
            case bounded_object_fs_interval_mul_decimal
              (bounded_interval64_object_cv x1)
              (bounded_interval64_object_cv x2) of
            | NONE => NONE
            | SOME p12 =>
              case bounded_object_fs_interval_mul_decimal
                (bounded_interval64_object_cv x0)
                (bounded_interval64_object_cv x3) of
              | NONE => NONE
              | SOME p03 =>
                case bounded_object_fs_interval_mul_decimal
                  (bounded_interval64_object_cv x1)
                  (bounded_interval64_object_cv x4) of
                | NONE => NONE
                | SOME p14 =>
                  case bounded_object_fs_interval_mul_decimal
                    (bounded_interval64_object_cv x2)
                    (bounded_interval64_object_cv x5) of
                  | NONE => NONE
                  | SOME p25 =>
                    case bounded_object_fs_interval_mul_decimal
                      (bounded_interval64_object_cv x4)
                      (bounded_interval64_object_cv x5) of
                    | NONE => NONE
                    | SOME p45 =>
                      case bounded_object_fs_interval_mul_decimal
                        (bounded_interval64_object_cv x0) linear of
                      | NONE => NONE
                      | SOME p0l =>
                        case bounded_object_fs_interval_neg p12 of
                        | NONE => NONE
                        | SOME negative_p12 =>
                          case bounded_object_fs_interval_neg p03 of
                          | NONE => NONE
                          | SOME negative_p03 =>
                            case bounded_object_fs_interval_neg p45 of
                            | NONE => NONE
                            | SOME negative_p45 =>
                              bounded_object_fs_interval_sum
                                (Pair negative_p12
                                  (Pair negative_p03
                                    (Pair p14
                                      (Pair p25
                                        (Pair negative_p45
                                          (Pair p0l (Num 0)))))))
    | _ => NONE
End

Theorem bounded_object_fs_historical_delta_x4_value_decimal_exact:
  bounded_historical_delta_x4_value_decimal environment = SOME result ==>
  bounded_object_fs_historical_delta_x4_value_decimal environment =
    SOME (bounded_interval64_object_cv result)
Proof
  rw [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_delta_x4_value_decimal_def,
      bounded_object_fs_historical_delta_x4_value_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_sum_exact
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> gvs
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_historical_delta_x4_gradient_def:
  bounded_object_fs_historical_delta_x4_gradient environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      case bounded_object_fs_interval_neg
        (bounded_interval64_object_cv x0) of
      | NONE => NONE
      | SOME negative_x0 =>
        case bounded_object_fs_interval_neg
          (bounded_interval64_object_cv x1) of
        | NONE => NONE
        | SOME negative_x1 =>
          case bounded_object_fs_interval_neg
            (bounded_interval64_object_cv x2) of
          | NONE => NONE
          | SOME negative_x2 =>
            case bounded_object_fs_interval_neg
              (bounded_interval64_object_cv x3) of
            | NONE => NONE
            | SOME negative_x3 =>
              case bounded_object_fs_interval_neg
                (bounded_interval64_object_cv x4) of
              | NONE => NONE
              | SOME negative_x4 =>
                case bounded_object_fs_interval_neg
                  (bounded_interval64_object_cv x5) of
                | NONE => NONE
                | SOME negative_x5 =>
                  case bounded_object_fs_interval_sum
                    (Pair negative_x0
                      (Pair negative_x0
                        (Pair (bounded_interval64_object_cv x1)
                          (Pair (bounded_interval64_object_cv x2)
                            (Pair negative_x3
                              (Pair negative_x3
                                (Pair (bounded_interval64_object_cv x4)
                                  (Pair (bounded_interval64_object_cv x5)
                                    (Num 0))))))))) of
                  | NONE => NONE
                  | SOME g0 =>
                    case bounded_object_fs_interval_sum
                      (Pair (bounded_interval64_object_cv x0)
                        (Pair negative_x2
                          (Pair (bounded_interval64_object_cv x4)
                            (Num 0)))) of
                    | NONE => NONE
                    | SOME g1 =>
                      case bounded_object_fs_interval_sum
                        (Pair (bounded_interval64_object_cv x0)
                          (Pair negative_x1
                            (Pair (bounded_interval64_object_cv x5)
                              (Num 0)))) of
                      | NONE => NONE
                      | SOME g2 =>
                        case bounded_object_fs_interval_scale2 negative_x0 of
                        | NONE => NONE
                        | SOME g3 =>
                          case bounded_object_fs_interval_sum
                            (Pair (bounded_interval64_object_cv x0)
                              (Pair (bounded_interval64_object_cv x1)
                                (Pair negative_x5 (Num 0)))) of
                          | NONE => NONE
                          | SOME g4 =>
                            case bounded_object_fs_interval_sum
                              (Pair (bounded_interval64_object_cv x0)
                                (Pair (bounded_interval64_object_cv x2)
                                  (Pair negative_x4 (Num 0)))) of
                            | NONE => NONE
                            | SOME g5 =>
                              SOME
                                (Pair g0
                                  (Pair g1
                                    (Pair g2
                                      (Pair g3
                                        (Pair g4
                                          (Pair g5 (Num 0)))))))
    | _ => NONE
End

Theorem bounded_object_fs_historical_delta_x4_gradient_exact:
  bounded_historical_delta_x4_gradient environment = SOME result ==>
  bounded_object_fs_historical_delta_x4_gradient environment =
    SOME (bounded_interval64_object_cv_list result)
Proof
  rw [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_delta_x4_gradient_def,
      bounded_object_fs_historical_delta_x4_gradient_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_sum_exact
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_scale2_exact
  >> gvs
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_signed_interval_list_def:
  bounded_object_fs_signed_interval_list [] = SOME (Num 0 : cv) /\
  bounded_object_fs_signed_interval_list ((negative,value)::rest) =
    case (if negative then
            bounded_object_fs_interval_neg
              (bounded_interval64_object_cv value)
          else SOME (bounded_interval64_object_cv value)) of
    | NONE => NONE
    | SOME signed_value =>
      case bounded_object_fs_signed_interval_list rest of
      | NONE => NONE
      | SOME signed_rest => SOME (Pair signed_value signed_rest)
End

Theorem bounded_object_fs_signed_interval_list_exact:
  !entries.
    bounded_object_fs_signed_interval_list entries =
      SOME
        (bounded_interval64_object_cv_list
          (MAP (\(negative,value).
             if negative then bounded_interval64_neg value else value)
           entries))
Proof
  Induct
  >- simp [bounded_object_fs_signed_interval_list_def,
           compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> gen_tac
  >> PairCases_on `h`
  >> Cases_on `h0`
  >> simp [bounded_object_fs_signed_interval_list_def,
           compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
           compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_interval_sum_signed_def:
  bounded_object_fs_interval_sum_signed entries =
    case bounded_object_fs_signed_interval_list entries of
    | NONE => NONE
    | SOME values => bounded_object_fs_interval_sum values
End

Theorem bounded_object_fs_interval_sum_signed_exact:
  !entries result.
  bounded_interval64_sum
      (MAP (\(negative,value).
         if negative then bounded_interval64_neg value else value) entries) =
    SOME result ==>
  bounded_object_fs_interval_sum_signed entries =
    SOME (bounded_interval64_object_cv result)
Proof
  rpt gen_tac
  >> rw [bounded_object_fs_interval_sum_signed_def,
      bounded_object_fs_signed_interval_list_exact]
  >> metis_tac
       [compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_sum_exact]
QED

Theorem bounded_object_fs_interval_sum_signed_three_exact:
  !negative0 x0 negative1 x1 negative2 x2 result.
  bounded_interval64_sum
      [if negative0 then bounded_interval64_neg x0 else x0;
       if negative1 then bounded_interval64_neg x1 else x1;
       if negative2 then bounded_interval64_neg x2 else x2] = SOME result ==>
  bounded_object_fs_interval_sum_signed
      [(negative0,x0);(negative1,x1);(negative2,x2)] =
    SOME (bounded_interval64_object_cv result)
Proof
  rpt gen_tac
  >> strip_tac
  >> irule bounded_object_fs_interval_sum_signed_exact
  >> gvs []
QED

Theorem bounded_object_fs_interval_sum_negative_first_exact:
  bounded_interval64_sum [bounded_interval64_neg x0;x1;x2] = SOME result ==>
  bounded_object_fs_interval_sum_signed [(T,x0);(F,x1);(F,x2)] =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> irule bounded_object_fs_interval_sum_signed_three_exact
  >> gvs []
QED

Theorem bounded_object_fs_interval_sum_negative_second_exact:
  bounded_interval64_sum [x0;bounded_interval64_neg x1;x2] = SOME result ==>
  bounded_object_fs_interval_sum_signed [(F,x0);(T,x1);(F,x2)] =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> irule bounded_object_fs_interval_sum_signed_three_exact
  >> gvs []
QED

Theorem bounded_object_fs_interval_sum_negative_third_exact:
  bounded_interval64_sum [x0;x1;bounded_interval64_neg x2] = SOME result ==>
  bounded_object_fs_interval_sum_signed [(F,x0);(F,x1);(T,x2)] =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> irule bounded_object_fs_interval_sum_signed_three_exact
  >> gvs []
QED

Theorem bounded_object_fs_interval_sum_signed_six_exact:
  !negative0 x0 negative1 x1 negative2 x2
   negative3 x3 negative4 x4 negative5 x5 result.
  bounded_interval64_sum
      [if negative0 then bounded_interval64_neg x0 else x0;
       if negative1 then bounded_interval64_neg x1 else x1;
       if negative2 then bounded_interval64_neg x2 else x2;
       if negative3 then bounded_interval64_neg x3 else x3;
       if negative4 then bounded_interval64_neg x4 else x4;
       if negative5 then bounded_interval64_neg x5 else x5] = SOME result ==>
  bounded_object_fs_interval_sum_signed
      [(negative0,x0);(negative1,x1);(negative2,x2);
       (negative3,x3);(negative4,x4);(negative5,x5)] =
    SOME (bounded_interval64_object_cv result)
Proof
  rpt gen_tac
  >> strip_tac
  >> irule bounded_object_fs_interval_sum_signed_exact
  >> gvs []
QED

Theorem bounded_object_fs_interval_sum_negative_zero_three_exact:
  bounded_interval64_sum
      [bounded_interval64_neg x0;x1;x2;
       bounded_interval64_neg x3;x4;x5] = SOME result ==>
  bounded_object_fs_interval_sum_signed
      [(T,x0);(F,x1);(F,x2);(T,x3);(F,x4);(F,x5)] =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> irule bounded_object_fs_interval_sum_signed_six_exact
  >> gvs []
QED

Theorem bounded_object_fs_interval_sum_negative_one_four_exact:
  bounded_interval64_sum
      [x0;bounded_interval64_neg x1;x2;x3;
       bounded_interval64_neg x4;x5] = SOME result ==>
  bounded_object_fs_interval_sum_signed
      [(F,x0);(T,x1);(F,x2);(F,x3);(T,x4);(F,x5)] =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> irule bounded_object_fs_interval_sum_signed_six_exact
  >> gvs []
QED

Theorem bounded_object_fs_interval_sum_negative_two_five_exact:
  bounded_interval64_sum
      [x0;x1;bounded_interval64_neg x2;x3;x4;
       bounded_interval64_neg x5] = SOME result ==>
  bounded_object_fs_interval_sum_signed
      [(F,x0);(F,x1);(T,x2);(F,x3);(F,x4);(T,x5)] =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> irule bounded_object_fs_interval_sum_signed_six_exact
  >> gvs []
QED

Theorem bounded_object_fs_historical_delta_raw_cubics_encoded_exact:
  bounded_historical_raw_cubics
      [(x0,x3,first_linear,F);
       (x1,x4,second_linear,F);
       (x2,x5,third_linear,F);
       (x1,x2,x3,T);
       (x0,x2,x4,T);
       (x0,x1,x5,T);
       (x3,x4,x5,T)] = SOME results ==>
  ?object_results.
    bounded_object_fs_historical_raw_cubics_encoded
      [(bounded_interval64_object_cv x0,
        bounded_interval64_object_cv x3,
        bounded_interval64_object_cv first_linear,F);
       (bounded_interval64_object_cv x1,
        bounded_interval64_object_cv x4,
        bounded_interval64_object_cv second_linear,F);
       (bounded_interval64_object_cv x2,
        bounded_interval64_object_cv x5,
        bounded_interval64_object_cv third_linear,F);
       (bounded_interval64_object_cv x1,
        bounded_interval64_object_cv x2,
        bounded_interval64_object_cv x3,T);
       (bounded_interval64_object_cv x0,
        bounded_interval64_object_cv x2,
        bounded_interval64_object_cv x4,T);
       (bounded_interval64_object_cv x0,
        bounded_interval64_object_cv x1,
        bounded_interval64_object_cv x5,T);
       (bounded_interval64_object_cv x3,
        bounded_interval64_object_cv x4,
        bounded_interval64_object_cv x5,T)] =
      SOME object_results /\
    bounded_object_raw_interval_cv_list_rel object_results results
Proof
  strip_tac
  >> mp_tac
       (Q.SPECL
         [`[(bounded_interval64_object_cv x0,
             bounded_interval64_object_cv x3,
             bounded_interval64_object_cv first_linear,F);
            (bounded_interval64_object_cv x1,
             bounded_interval64_object_cv x4,
             bounded_interval64_object_cv second_linear,F);
            (bounded_interval64_object_cv x2,
             bounded_interval64_object_cv x5,
             bounded_interval64_object_cv third_linear,F);
            (bounded_interval64_object_cv x1,
             bounded_interval64_object_cv x2,
             bounded_interval64_object_cv x3,T);
            (bounded_interval64_object_cv x0,
             bounded_interval64_object_cv x2,
             bounded_interval64_object_cv x4,T);
            (bounded_interval64_object_cv x0,
             bounded_interval64_object_cv x1,
             bounded_interval64_object_cv x5,T);
            (bounded_interval64_object_cv x3,
             bounded_interval64_object_cv x4,
             bounded_interval64_object_cv x5,T)]`,
          `[(x0,x3,first_linear,F);
            (x1,x4,second_linear,F);
            (x2,x5,third_linear,F);
            (x1,x2,x3,T);
            (x0,x2,x4,T);
            (x0,x1,x5,T);
            (x3,x4,x5,T)]`,
          `results`]
         bounded_object_fs_historical_raw_cubics_encoded_exact)
  >> simp [bounded_object_raw_cubic_input_cv_rel_def]
QED

Definition bounded_object_fs_historical_delta64_value_six_decimal_def:
  bounded_object_fs_historical_delta64_value_six_decimal
      x0 x1 x2 x3 x4 x5 =
    case bounded_object_fs_interval_sum_signed
      [(T,x0);(F,x1);(F,x2);(T,x3);(F,x4);(F,x5)] of
    | NONE => NONE
    | SOME first_linear =>
      case bounded_object_fs_interval_sum_signed
        [(F,x0);(T,x1);(F,x2);(F,x3);(T,x4);(F,x5)] of
      | NONE => NONE
      | SOME second_linear =>
        case bounded_object_fs_interval_sum_signed
          [(F,x0);(F,x1);(T,x2);(F,x3);(F,x4);(T,x5)] of
        | NONE => NONE
        | SOME third_linear =>
          case bounded_object_fs_historical_raw_cubics_encoded
            [(bounded_interval64_object_cv x0,
              bounded_interval64_object_cv x3,first_linear,F);
             (bounded_interval64_object_cv x1,
              bounded_interval64_object_cv x4,second_linear,F);
             (bounded_interval64_object_cv x2,
              bounded_interval64_object_cv x5,third_linear,F);
             (bounded_interval64_object_cv x1,
              bounded_interval64_object_cv x2,
              bounded_interval64_object_cv x3,T);
             (bounded_interval64_object_cv x0,
              bounded_interval64_object_cv x2,
              bounded_interval64_object_cv x4,T);
             (bounded_interval64_object_cv x0,
              bounded_interval64_object_cv x1,
              bounded_interval64_object_cv x5,T);
             (bounded_interval64_object_cv x3,
              bounded_interval64_object_cv x4,
              bounded_interval64_object_cv x5,T)] of
          | NONE => NONE
          | SOME raw_terms =>
            case bounded_object_fs_raw_interval_sum raw_terms of
            | NONE => NONE
            | SOME raw =>
                bounded_object_fs_historical_raw_round_decimal raw
End

Theorem bounded_object_fs_historical_delta64_value_six_decimal_exact:
  bounded_historical_delta64_value_six_decimal x0 x1 x2 x3 x4 x5 =
      SOME result ==>
  bounded_object_fs_historical_delta64_value_six_decimal
      x0 x1 x2 x3 x4 x5 =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_delta64_value_six_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       bounded_object_fs_interval_sum_negative_zero_three_exact
  >> imp_res_tac
       bounded_object_fs_interval_sum_negative_one_four_exact
  >> imp_res_tac
       bounded_object_fs_interval_sum_negative_two_five_exact
  >> imp_res_tac
       bounded_object_fs_historical_delta_raw_cubics_encoded_exact
  >> imp_res_tac bounded_object_fs_raw_interval_sum_round_decimal_exact
  >> gvs [bounded_object_fs_historical_delta64_value_six_decimal_def]
QED

Definition bounded_object_fs_historical_delta64_value_decimal_def:
  bounded_object_fs_historical_delta64_value_decimal environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
        bounded_object_fs_historical_delta64_value_six_decimal
          x0 x1 x2 x3 x4 x5
    | _ => NONE
End

Theorem bounded_object_fs_historical_delta64_value_decimal_exact:
  bounded_historical_delta64_value_decimal environment = SOME result ==>
  bounded_object_fs_historical_delta64_value_decimal environment =
    SOME (bounded_interval64_object_cv result)
Proof
  Cases_on `environment`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_delta64_value_decimal_def,
        bounded_object_fs_historical_delta64_value_decimal_def]
  >> Cases_on `t`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_delta64_value_decimal_def,
        bounded_object_fs_historical_delta64_value_decimal_def]
  >> Cases_on `t'`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_delta64_value_decimal_def,
        bounded_object_fs_historical_delta64_value_decimal_def]
  >> Cases_on `t`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_delta64_value_decimal_def,
        bounded_object_fs_historical_delta64_value_decimal_def]
  >> Cases_on `t'`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_delta64_value_decimal_def,
        bounded_object_fs_historical_delta64_value_decimal_def]
  >> Cases_on `t`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_delta64_value_decimal_def,
        bounded_object_fs_historical_delta64_value_decimal_def]
  >> Cases_on `t'`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_delta64_value_decimal_def,
        bounded_object_fs_historical_delta64_value_decimal_def,
        bounded_object_fs_historical_delta64_value_six_decimal_exact]
QED

Definition bounded_object_fs_delta64_pair_products_decimal_def:
  bounded_object_fs_delta64_pair_products_decimal environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      bounded_object_fs_interval_list_pairwise_mul_decimal
        (bounded_interval64_object_cv_list
          [x0;x0;x0;x0;x0;x0;
           x1;x1;x1;x1;x1;
           x2;x2;x2;x2;
           x3;x3;x3;
           x4;x4;
           x5])
        (bounded_interval64_object_cv_list
          [x0;x1;x2;x3;x4;x5;
           x1;x2;x3;x4;x5;
           x2;x3;x4;x5;
           x3;x4;x5;
           x4;x5;
           x5])
    | _ => NONE
End

Theorem bounded_object_fs_delta64_pair_products_decimal_exact:
  bounded_delta64_pair_products_decimal environment = SOME result ==>
  bounded_object_fs_delta64_pair_products_decimal environment =
    SOME (bounded_interval64_object_cv_list result)
Proof
  rw [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_delta64_pair_products_decimal_def,
      bounded_object_fs_delta64_pair_products_decimal_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac
       [compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_list_pairwise_mul_decimal_exact]
QED

Definition bounded_object_fs_historical_u_block_decimal_def:
  bounded_object_fs_historical_u_block_decimal n0 n1 n2 p0 p1 p2 =
    bounded_object_fs_fused_products_decimal
      [(bounded_interval64_neg n0,n0);
       (bounded_interval64_neg n1,n1);
       (bounded_interval64_neg n2,n2);
       (p0,p1);(p0,p1);
       (p1,p2);(p1,p2);
       (p2,p0);(p2,p0)]
End

Theorem bounded_object_fs_historical_u_block_decimal_exact:
  bounded_historical_u_block_decimal n0 n1 n2 p0 p1 p2 = SOME result ==>
  bounded_object_fs_historical_u_block_decimal n0 n1 n2 p0 p1 p2 =
    SOME (bounded_interval64_object_cv result)
Proof
  rw [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u_block_decimal_def,
      bounded_object_fs_historical_u_block_decimal_def]
  >> metis_tac
       [compute_boundedObjectDecimalFusedTheory.bounded_object_fs_fused_products_decimal_exact]
QED

Definition bounded_object_fs_interval_endpoints_def:
  bounded_object_fs_interval_endpoints (Pair lower upper : cv) =
    SOME (lower,upper) /\
  bounded_object_fs_interval_endpoints _ = NONE
End

Theorem bounded_object_fs_interval_endpoints_exact[simp]:
  bounded_object_fs_interval_endpoints
      (bounded_interval64_object_cv interval) =
    SOME
      (bounded_signed64_object_cv (bounded_interval64_lower interval),
       bounded_signed64_object_cv (bounded_interval64_upper interval))
Proof
  Cases_on `interval`
  >> simp [bounded_object_fs_interval_endpoints_def,
           compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
           compute_boundedIntervalTheory.bounded_interval64_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Definition bounded_object_fs_historical_u_three_decimal_def:
  bounded_object_fs_historical_u_three_decimal x0 x1 x2 =
    case bounded_interval64_sum [bounded_interval64_neg x0;x1;x2] of
    | NONE => NONE
    | SOME g0_half =>
      case bounded_object_fs_interval_sum_signed [(T,x0);(F,x1);(F,x2)] of
      | NONE => NONE
      | SOME object_g0_half =>
        case bounded_historical_scale2 g0_half of
        | NONE => NONE
        | SOME g0 =>
          case bounded_object_fs_interval_scale2 object_g0_half of
          | NONE => NONE
          | SOME object_g0 =>
            case bounded_interval64_sum [x0;bounded_interval64_neg x1;x2] of
            | NONE => NONE
            | SOME g1_half =>
              case bounded_object_fs_interval_sum_signed
                [(F,x0);(T,x1);(F,x2)] of
              | NONE => NONE
              | SOME object_g1_half =>
                case bounded_historical_scale2 g1_half of
                | NONE => NONE
                | SOME g1 =>
                  case bounded_object_fs_interval_scale2 object_g1_half of
                  | NONE => NONE
                  | SOME object_g1 =>
                    case bounded_interval64_sum
                      [x0;x1;bounded_interval64_neg x2] of
                    | NONE => NONE
                    | SOME g2_half =>
                      case bounded_object_fs_interval_sum_signed
                        [(F,x0);(F,x1);(T,x2)] of
                      | NONE => NONE
                      | SOME object_g2_half =>
                        case bounded_historical_scale2 g2_half of
                        | NONE => NONE
                        | SOME g2 =>
                          case bounded_object_fs_interval_scale2
                            object_g2_half of
                          | NONE => NONE
                          | SOME object_g2 =>
                            case bounded_historical_u_block_decimal
                              (bounded_historical_u_lower_negative x0 g0)
                              (bounded_historical_u_lower_negative x1 g1)
                              (bounded_historical_u_lower_negative x2 g2)
                              (bounded_historical_u_lower_positive x0 g0)
                              (bounded_historical_u_lower_positive x1 g1)
                              (bounded_historical_u_lower_positive x2 g2) of
                            | NONE => NONE
                            | SOME lower_value =>
                              case bounded_object_fs_historical_u_block_decimal
                                (bounded_historical_u_lower_negative x0 g0)
                                (bounded_historical_u_lower_negative x1 g1)
                                (bounded_historical_u_lower_negative x2 g2)
                                (bounded_historical_u_lower_positive x0 g0)
                                (bounded_historical_u_lower_positive x1 g1)
                                (bounded_historical_u_lower_positive x2 g2) of
                              | NONE => NONE
                              | SOME object_lower =>
                                case bounded_historical_u_block_decimal
                                  (bounded_historical_u_upper_negative x0 g0)
                                  (bounded_historical_u_upper_negative x1 g1)
                                  (bounded_historical_u_upper_negative x2 g2)
                                  (bounded_historical_u_upper_positive x0 g0)
                                  (bounded_historical_u_upper_positive x1 g1)
                                  (bounded_historical_u_upper_positive x2 g2) of
                                | NONE => NONE
                                | SOME upper_value =>
                                  case bounded_object_fs_historical_u_block_decimal
                                    (bounded_historical_u_upper_negative x0 g0)
                                    (bounded_historical_u_upper_negative x1 g1)
                                    (bounded_historical_u_upper_negative x2 g2)
                                    (bounded_historical_u_upper_positive x0 g0)
                                    (bounded_historical_u_upper_positive x1 g1)
                                    (bounded_historical_u_upper_positive x2 g2) of
                                  | NONE => NONE
                                  | SOME object_upper =>
                                    case bounded_object_fs_interval_endpoints
                                      object_lower of
                                    | NONE => NONE
                                    | SOME (object_lower_endpoint,_) =>
                                      case bounded_object_fs_interval_endpoints
                                        object_upper of
                                      | NONE => NONE
                                      | SOME (_,object_upper_endpoint) =>
                                        SOME
                                          (Pair
                                            (Pair object_lower_endpoint
                                              object_upper_endpoint)
                                            (Pair object_g0
                                              (Pair object_g1
                                                (Pair object_g2 (Num 0)))))
End

Theorem bounded_object_fs_historical_u_three_decimal_exact:
  bounded_historical_u_three_decimal x0 x1 x2 = SOME (value,gradient) ==>
  bounded_object_fs_historical_u_three_decimal x0 x1 x2 =
    SOME
      (Pair (bounded_interval64_object_cv value)
        (bounded_interval64_object_cv_list gradient))
Proof
  rw [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u_three_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_fs_interval_sum_negative_first_exact
  >> imp_res_tac bounded_object_fs_interval_sum_negative_second_exact
  >> imp_res_tac bounded_object_fs_interval_sum_negative_third_exact
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_scale2_exact
  >> imp_res_tac bounded_object_fs_historical_u_block_decimal_exact
  >> gvs
       [bounded_object_fs_historical_u_three_decimal_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Definition bounded_object_fs_historical_u126_decimal_def:
  bounded_object_fs_historical_u126_decimal environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      (case bounded_object_fs_historical_u_three_decimal x0 x1 x5 of
      | SOME (Pair value (Pair g0 (Pair g1 (Pair g2 (Num 0))))) =>
          SOME
            (Pair value
              (Pair g0
                (Pair g1
                  (Pair (bounded_interval64_object_cv bounded_interval64_zero)
                    (Pair
                      (bounded_interval64_object_cv bounded_interval64_zero)
                      (Pair
                        (bounded_interval64_object_cv bounded_interval64_zero)
                        (Pair g2 (Num 0))))))))
      | _ => NONE)
    | _ => NONE
End

Theorem bounded_object_fs_historical_u126_decimal_exact:
  bounded_historical_u126_decimal environment = SOME (value,gradient) ==>
  bounded_object_fs_historical_u126_decimal environment =
    SOME
      (Pair (bounded_interval64_object_cv value)
        (bounded_interval64_object_cv_list gradient))
Proof
  rw [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u126_decimal_def,
      bounded_object_fs_historical_u126_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_fs_historical_u_three_decimal_exact
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_historical_u135_decimal_def:
  bounded_object_fs_historical_u135_decimal environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      (case bounded_object_fs_historical_u_three_decimal x0 x2 x4 of
      | SOME (Pair value (Pair g0 (Pair g1 (Pair g2 (Num 0))))) =>
          SOME
            (Pair value
              (Pair g0
                (Pair (bounded_interval64_object_cv bounded_interval64_zero)
                  (Pair g1
                    (Pair
                      (bounded_interval64_object_cv bounded_interval64_zero)
                      (Pair g2
                        (Pair
                          (bounded_interval64_object_cv bounded_interval64_zero)
                          (Num 0))))))))
      | _ => NONE)
    | _ => NONE
End

Theorem bounded_object_fs_historical_u135_decimal_exact:
  bounded_historical_u135_decimal environment = SOME (value,gradient) ==>
  bounded_object_fs_historical_u135_decimal environment =
    SOME
      (Pair (bounded_interval64_object_cv value)
        (bounded_interval64_object_cv_list gradient))
Proof
  rw [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u135_decimal_def,
      bounded_object_fs_historical_u135_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_fs_historical_u_three_decimal_exact
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_delta64_gradient_component_from_products_def:
  bounded_object_fs_delta64_gradient_component_from_products (coordinate:num)
      products =
    case bounded_delta64_gradient_signed_terms coordinate products of
    | NONE => NONE
    | SOME terms => bounded_object_fs_interval_sum_signed terms
End

val bounded_delta_gradient_component_defs =
  [compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_component_from_products_def,
   compute_boundedDeltaTaylorTheory.bounded_delta64_apply_signed_terms_def,
   bounded_object_fs_delta64_gradient_component_from_products_def];

Theorem bounded_object_fs_delta64_gradient_component_from_products_exact:
  bounded_delta64_gradient_component_from_products coordinate products =
    SOME result ==>
  bounded_object_fs_delta64_gradient_component_from_products coordinate
    products = SOME (bounded_interval64_object_cv result)
Proof
  rw bounded_delta_gradient_component_defs
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_object_fs_interval_sum_signed_exact]
QED

Definition bounded_object_fs_delta64_gradient_components_def:
  bounded_object_fs_delta64_gradient_components [] products =
    SOME (Num 0 : cv) /\
  bounded_object_fs_delta64_gradient_components
      (coordinate::coordinates) products =
    case bounded_object_fs_delta64_gradient_component_from_products
      coordinate products of
    | NONE => NONE
    | SOME entry =>
      case bounded_object_fs_delta64_gradient_components coordinates products of
      | NONE => NONE
      | SOME rest => SOME (Pair entry rest)
End

Theorem bounded_object_fs_delta64_gradient_components_exact:
  !products result.
    bounded_delta64_gradient_components coordinates products = SOME result ==>
    bounded_object_fs_delta64_gradient_components coordinates products =
      SOME (bounded_interval64_object_cv_list result)
Proof
  Induct_on `coordinates`
  >> rw [compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_components_def,
         bounded_object_fs_delta64_gradient_components_def,
         compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       bounded_object_fs_delta64_gradient_component_from_products_exact
  >> res_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_delta64_gradient_from_products_def:
  bounded_object_fs_delta64_gradient_from_products products =
    bounded_object_fs_delta64_gradient_components [0;1;2;3;4;5] products
End

Theorem bounded_object_fs_delta64_gradient_from_products_exact:
  bounded_delta64_gradient_from_products products = SOME result ==>
  bounded_object_fs_delta64_gradient_from_products products =
    SOME (bounded_interval64_object_cv_list result)
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_from_products_def,
      bounded_object_fs_delta64_gradient_from_products_def]
  >> metis_tac [bounded_object_fs_delta64_gradient_components_exact]
QED

Definition bounded_object_fs_interval_mul_add_decimal_def:
  bounded_object_fs_interval_mul_add_decimal scalar accumulator addend =
    case bounded_object_fs_interval_mul_decimal scalar accumulator of
    | NONE => NONE
    | SOME product => bounded_object_fs_interval_add addend product
End

Theorem bounded_object_fs_interval_mul_add_decimal_exact:
  bounded_interval64_mul_add_decimal scalar accumulator addend = SOME result ==>
  bounded_object_fs_interval_mul_add_decimal
      (bounded_interval64_object_cv scalar)
      (bounded_interval64_object_cv accumulator)
      (bounded_interval64_object_cv addend) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw [compute_boundedAtanDecimalTheory.bounded_interval64_mul_add_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
  >> gvs [bounded_object_fs_interval_mul_add_decimal_def]
QED

Definition bounded_object_fs_interval64_atan_pos_lower_decimal_def:
  bounded_object_fs_interval64_atan_pos_lower_decimal magnitude =
    let point = BoundedInterval64
      (BoundedSigned64 F magnitude) (BoundedSigned64 F magnitude) in
    case bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv point)
      (bounded_interval64_object_cv point) of
    | NONE => NONE
    | SOME square =>
      case bounded_object_fs_interval_mul_add_decimal square
        (bounded_interval64_object_cv bounded_atan_neg_eleventh_decimal)
        (bounded_interval64_object_cv bounded_atan_pos_ninth_decimal) of
      | NONE => NONE
      | SOME step9 =>
        case bounded_object_fs_interval_mul_add_decimal square step9
          (bounded_interval64_object_cv bounded_atan_neg_seventh_decimal) of
        | NONE => NONE
        | SOME step7 =>
          case bounded_object_fs_interval_mul_add_decimal square step7
            (bounded_interval64_object_cv bounded_atan_pos_fifth_decimal) of
          | NONE => NONE
          | SOME step5 =>
            case bounded_object_fs_interval_mul_add_decimal square step5
              (bounded_interval64_object_cv bounded_atan_neg_third_decimal) of
            | NONE => NONE
            | SOME step3 =>
              case bounded_object_fs_interval_mul_add_decimal square step3
                (bounded_interval64_object_cv bounded_atan_one_decimal) of
              | NONE => NONE
              | SOME body =>
                  bounded_object_fs_interval_mul_decimal
                    (bounded_interval64_object_cv point) body
End

Theorem bounded_object_fs_interval64_atan_pos_lower_decimal_exact:
  bounded_interval64_atan_pos_lower_decimal magnitude = SOME result ==>
  bounded_object_fs_interval64_atan_pos_lower_decimal magnitude =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedAtanDecimalTheory.bounded_interval64_atan_pos_lower_decimal_def,
     LET_THM]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> imp_res_tac bounded_object_fs_interval_mul_add_decimal_exact
  >> gvs
       [bounded_object_fs_interval64_atan_pos_lower_decimal_def,
        LET_THM]
QED

Definition bounded_object_fs_interval64_atan_pos_upper_decimal_def:
  bounded_object_fs_interval64_atan_pos_upper_decimal magnitude =
    let point = BoundedInterval64
      (BoundedSigned64 F magnitude) (BoundedSigned64 F magnitude) in
    case bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv point)
      (bounded_interval64_object_cv point) of
    | NONE => NONE
    | SOME square =>
      case bounded_object_fs_interval_mul_add_decimal square
        (bounded_interval64_object_cv bounded_atan_pos_thirteenth_decimal)
        (bounded_interval64_object_cv bounded_atan_neg_eleventh_decimal) of
      | NONE => NONE
      | SOME step11 =>
        case bounded_object_fs_interval_mul_add_decimal square step11
          (bounded_interval64_object_cv bounded_atan_pos_ninth_decimal) of
        | NONE => NONE
        | SOME step9 =>
          case bounded_object_fs_interval_mul_add_decimal square step9
            (bounded_interval64_object_cv bounded_atan_neg_seventh_decimal) of
          | NONE => NONE
          | SOME step7 =>
            case bounded_object_fs_interval_mul_add_decimal square step7
              (bounded_interval64_object_cv bounded_atan_pos_fifth_decimal) of
            | NONE => NONE
            | SOME step5 =>
              case bounded_object_fs_interval_mul_add_decimal square step5
                (bounded_interval64_object_cv bounded_atan_neg_third_decimal) of
              | NONE => NONE
              | SOME step3 =>
                case bounded_object_fs_interval_mul_add_decimal square step3
                  (bounded_interval64_object_cv bounded_atan_one_decimal) of
                | NONE => NONE
                | SOME body =>
                    bounded_object_fs_interval_mul_decimal
                      (bounded_interval64_object_cv point) body
End

Theorem bounded_object_fs_interval64_atan_pos_upper_decimal_exact:
  bounded_interval64_atan_pos_upper_decimal magnitude = SOME result ==>
  bounded_object_fs_interval64_atan_pos_upper_decimal magnitude =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedAtanDecimalTheory.bounded_interval64_atan_pos_upper_decimal_def,
     LET_THM]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> imp_res_tac bounded_object_fs_interval_mul_add_decimal_exact
  >> gvs
       [bounded_object_fs_interval64_atan_pos_upper_decimal_def,
        LET_THM]
QED

val _ = export_theory ();
