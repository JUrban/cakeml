(*****************************************************************************
 * Encoded-list object refinement used by the historical decimal checker.
 *
 * These functions recurse over the authenticated cv list representation,
 * rather than calling the bounded implementation in their definitions.  The
 * exactness theorems therefore compose into a genuine word/object simulation.
 *****************************************************************************)
Theory compute_boundedObjectHistoricalListDecimal
Ancestors
  compute_boundedObjectTaylorSqrtDecimal
  compute_boundedHistoricalDihedralFirstDecimal
Libs
  bossLib preamble

Definition bounded_object_fs_interval_sum_aux_def:
  bounded_object_fs_interval_sum_aux (Num 0) accumulator = SOME accumulator /\
  bounded_object_fs_interval_sum_aux (Num (SUC malformed)) accumulator = NONE /\
  bounded_object_fs_interval_sum_aux (Pair value rest) accumulator =
    case bounded_object_fs_interval_add accumulator value of
    | NONE => NONE
    | SOME next => bounded_object_fs_interval_sum_aux rest next
End

Definition bounded_object_fs_interval_sum_def:
  bounded_object_fs_interval_sum values =
    bounded_object_fs_interval_sum_aux values
      (bounded_interval64_object_cv bounded_interval64_zero)
End

Theorem bounded_object_fs_interval_sum_aux_exact:
  !accumulator result.
    bounded_interval64_sum_aux values accumulator = SOME result ==>
    bounded_object_fs_interval_sum_aux
      (bounded_interval64_object_cv_list values)
      (bounded_interval64_object_cv accumulator) =
      SOME (bounded_interval64_object_cv result)
Proof
  Induct_on `values`
  >> rw
       [compute_boundedDeltaTaylorTheory.bounded_interval64_sum_aux_def,
        bounded_object_fs_interval_sum_aux_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
  >> res_tac
  >> gvs []
QED

Theorem bounded_object_fs_interval_sum_exact:
  bounded_interval64_sum values = SOME result ==>
  bounded_object_fs_interval_sum
    (bounded_interval64_object_cv_list values) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_interval64_sum_def,
      bounded_object_fs_interval_sum_def]
  >> metis_tac [bounded_object_fs_interval_sum_aux_exact]
QED

Definition bounded_object_fs_interval_scale2_def:
  bounded_object_fs_interval_scale2 value =
    bounded_object_fs_interval_add value value
End

Theorem bounded_object_fs_interval_scale2_exact:
  bounded_historical_scale2 value = SOME result ==>
  bounded_object_fs_interval_scale2
    (bounded_interval64_object_cv value) =
    SOME (bounded_interval64_object_cv result)
Proof
  simp [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_scale2_def,
        bounded_object_fs_interval_scale2_def]
  >> metis_tac
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact]
QED

Definition bounded_object_fs_interval_scale4_def:
  bounded_object_fs_interval_scale4 value =
    case bounded_object_fs_interval_add value value of
    | NONE => NONE
    | SOME twice => bounded_object_fs_interval_add twice twice
End

Theorem bounded_object_fs_interval_scale4_exact:
  bounded_interval64_scale4 value = SOME result ==>
  bounded_object_fs_interval_scale4
    (bounded_interval64_object_cv value) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_interval64_scale4_def,
      bounded_object_fs_interval_scale4_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
  >> gvs []
QED

Definition bounded_object_fs_interval_list_pairwise_mul_decimal_def:
  bounded_object_fs_interval_list_pairwise_mul_decimal
      (Num 0) (Num 0) = SOME (Num 0 : cv) /\
  bounded_object_fs_interval_list_pairwise_mul_decimal
      (Num 0) (Pair right right_rest) = NONE /\
  bounded_object_fs_interval_list_pairwise_mul_decimal
      (Pair left left_rest) (Num right) = NONE /\
  bounded_object_fs_interval_list_pairwise_mul_decimal
      (Num (SUC malformed)) right = NONE /\
  bounded_object_fs_interval_list_pairwise_mul_decimal
      (Pair left left_rest) (Pair right right_rest) =
    case bounded_object_fs_interval_mul_decimal left right of
    | NONE => NONE
    | SOME value =>
      case bounded_object_fs_interval_list_pairwise_mul_decimal
        left_rest right_rest of
      | NONE => NONE
      | SOME rest => SOME (Pair value rest)
End

Theorem bounded_object_fs_interval_list_pairwise_mul_decimal_exact:
  !right result.
    bounded_interval64_list_pairwise_mul_decimal left right = SOME result ==>
    bounded_object_fs_interval_list_pairwise_mul_decimal
      (bounded_interval64_object_cv_list left)
      (bounded_interval64_object_cv_list right) =
    SOME (bounded_interval64_object_cv_list result)
Proof
  Induct_on `left`
  >> Cases_on `right`
  >> rw
       [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_interval64_list_pairwise_mul_decimal_def,
        bounded_object_fs_interval_list_pairwise_mul_decimal_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> res_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_interval_list_add_at_def:
  bounded_object_fs_interval_list_add_at value index (Num malformed) = NONE /\
  bounded_object_fs_interval_list_add_at value 0 (Pair entry rest) =
    (case bounded_object_fs_interval_add entry value of
     | NONE => NONE
     | SOME updated => SOME (Pair updated rest)) /\
  bounded_object_fs_interval_list_add_at value (SUC index)
      (Pair entry rest) =
    (case bounded_object_fs_interval_list_add_at value index rest of
     | NONE => NONE
     | SOME updated => SOME (Pair entry updated))
End

Theorem bounded_object_fs_interval_list_add_at_exact:
  !value index result.
    bounded_interval64_list_add_at value index values = SOME result ==>
    bounded_object_fs_interval_list_add_at
      (bounded_interval64_object_cv value) index
      (bounded_interval64_object_cv_list values) =
    SOME (bounded_interval64_object_cv_list result)
Proof
  Induct_on `values`
  >> Cases_on `index`
  >> rw
       [compute_boundedDeltaTaylorTheory.bounded_interval64_list_add_at_def,
        bounded_object_fs_interval_list_add_at_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
  >> res_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_historical_c_vector_decimal_def:
  bounded_object_fs_historical_c_vector_decimal delta_x4 b
      (Num 0) (Num 0) = SOME (Num 0 : cv) /\
  bounded_object_fs_historical_c_vector_decimal delta_x4 b
      (Num 0) (Pair right right_rest) = NONE /\
  bounded_object_fs_historical_c_vector_decimal delta_x4 b
      (Pair left left_rest) (Num right) = NONE /\
  bounded_object_fs_historical_c_vector_decimal delta_x4 b
      (Num (SUC malformed)) right = NONE /\
  bounded_object_fs_historical_c_vector_decimal delta_x4 b
      (Pair delta_gradient delta_rest) (Pair b_gradient b_rest) =
    case bounded_object_fs_interval_mul_decimal delta_gradient b of
    | NONE => NONE
    | SOME first_product =>
      case bounded_object_fs_interval_mul_decimal delta_x4 b_gradient of
      | NONE => NONE
      | SOME second_product =>
        case bounded_object_fs_interval_neg first_product of
        | NONE => NONE
        | SOME negative_first =>
          case bounded_object_fs_interval_add negative_first second_product of
          | NONE => NONE
          | SOME value =>
            case bounded_object_fs_historical_c_vector_decimal delta_x4 b
              delta_rest b_rest of
            | NONE => NONE
            | SOME rest => SOME (Pair value rest)
End

Theorem bounded_object_fs_historical_c_vector_decimal_exact:
  !b_gradient result.
    bounded_historical_c_vector_decimal delta_x4 b delta_gradient b_gradient =
      SOME result ==>
    bounded_object_fs_historical_c_vector_decimal
      (bounded_interval64_object_cv delta_x4)
      (bounded_interval64_object_cv b)
      (bounded_interval64_object_cv_list delta_gradient)
      (bounded_interval64_object_cv_list b_gradient) =
    SOME (bounded_interval64_object_cv_list result)
Proof
  Induct_on `delta_gradient`
  >> Cases_on `b_gradient`
  >> rw
       [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_c_vector_decimal_def,
        bounded_object_fs_historical_c_vector_decimal_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
  >> res_tac
  >> gvs
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

val _ = export_theory ();
