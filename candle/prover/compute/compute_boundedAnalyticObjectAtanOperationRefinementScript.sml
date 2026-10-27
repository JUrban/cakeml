(*****************************************************************************
 * Operation-level object-q refinement for the scale-2^40 arctangent lift.
 *
 * The first theorem exposes the complete successful executable trace.  The
 * remaining refinement deliberately depends on a separate proof that the
 * dependency-aware interval square covers the corresponding source-rational
 * square; that obligation must not be hidden by treating square as ordinary
 * independent interval multiplication.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectAtanOperationRefinement
Ancestors
  compute_boundedAnalyticObjectInverseOperationRefinement
Libs
  bossLib preamble intLib

Theorem bounded_interval64_square_contains_scaled_square:
  bounded_interval64_contains_int source value /\
  bounded_interval64_square source = SOME result ==>
  bounded_interval64_contains_scaled_int result
    (&1099511627776:int) (value * value)
Proof
  Cases_on `source`
  >> rename1 `BoundedInterval64 lower upper`
  >> strip_tac
  >> `bounded_interval64_valid (BoundedInterval64 lower upper)` by
       fs [compute_boundedIntervalSquareTheory.bounded_interval64_square_def]
  >> Cases_on `bounded_signed64_nonnegative lower`
  >- (`bounded_interval64_mul_unchecked
          (BoundedInterval64 lower upper)
          (BoundedInterval64 lower upper) = SOME result` by
        fs [compute_boundedIntervalSquareTheory.bounded_interval64_square_def,
            compute_boundedIntervalSquareTheory.bounded_interval64_square_unchecked_def]
      >> Cases_on `result`
      >> fs [compute_boundedIntervalTheory.bounded_interval64_contains_scaled_int_def]
      >> metis_tac
           [compute_boundedIntervalTheory.bounded_interval64_mul_unchecked_contains_product])
  >> Cases_on `bounded_signed64_nonpositive upper`
  >- (`bounded_interval64_mul_unchecked
          (BoundedInterval64 lower upper)
          (BoundedInterval64 lower upper) = SOME result` by
        fs [compute_boundedIntervalSquareTheory.bounded_interval64_square_def,
            compute_boundedIntervalSquareTheory.bounded_interval64_square_unchecked_def]
      >> Cases_on `result`
      >> fs [compute_boundedIntervalTheory.bounded_interval64_contains_scaled_int_def]
      >> metis_tac
           [compute_boundedIntervalTheory.bounded_interval64_mul_unchecked_contains_product])
  >> Cases_on `bounded_scaled_mul_ceil64 lower lower`
  >> Cases_on `bounded_scaled_mul_ceil64 upper upper`
  >> fs [compute_boundedIntervalSquareTheory.bounded_interval64_square_def,
         compute_boundedIntervalSquareTheory.bounded_interval64_square_unchecked_def]
  >> gvs [compute_boundedIntervalTheory.bounded_interval64_contains_int_def,
          compute_boundedIntervalTheory.bounded_interval64_contains_scaled_int_def,
          compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
          compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct,
          compute_boundedSignedEndpointTheory.bounded_signed64_max_correct]
  >> imp_res_tac
       compute_boundedIntervalTheory.bounded_scaled_mul_ceil64_upper_bound_general
  >> conj_tac
  >- simp
       [compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
        integerTheory.INT_LE_SQUARE]
  >> Cases_on `0 <= value`
  >- (`value * value <=
        bounded_signed64_to_int upper * bounded_signed64_to_int upper` by
        (mp_tac
           (Q.INST
             [`left_lower` |-> `0:int`,
              `left_value` |-> `value:int`,
              `left_upper` |-> `bounded_signed64_to_int upper`,
              `right_lower` |-> `0:int`,
              `right_value` |-> `value:int`,
              `right_upper` |-> `bounded_signed64_to_int upper`]
             compute_boundedIntervalTheory.bounded_int_product_bounds_nonnegative_nonnegative)
         >> impl_tac >- intLib.ARITH_TAC
         >> simp [])
      >> Cases_on
           `bounded_signed64_to_int x <= bounded_signed64_to_int x'`
      >> fs []
      >> intLib.ARITH_TAC)
  >> `value * value <=
        bounded_signed64_to_int lower * bounded_signed64_to_int lower` by
       (mp_tac
          (Q.INST
            [`left_lower` |-> `bounded_signed64_to_int lower`,
             `left_value` |-> `value:int`,
             `left_upper` |-> `0:int`,
             `right_lower` |-> `bounded_signed64_to_int lower`,
             `right_value` |-> `value:int`,
             `right_upper` |-> `0:int`]
            compute_boundedIntervalTheory.bounded_int_product_bounds_nonpositive_nonpositive)
        >> impl_tac >- intLib.ARITH_TAC
        >> simp [])
  >> Cases_on `bounded_signed64_to_int x <= bounded_signed64_to_int x'`
  >> fs []
  >> intLib.ARITH_TAC
QED

Definition bounded_object_q_interval_encloses_def:
  bounded_object_q_interval_encloses outer inner <=>
    case bounded_object_q_interval_ints outer of
    | NONE => F
    | SOME ((outer_lower,outer_lower_denominator),
            (outer_upper,outer_upper_denominator)) =>
      case bounded_object_q_interval_ints inner of
      | NONE => F
      | SOME ((inner_lower,inner_lower_denominator),
              (inner_upper,inner_upper_denominator)) =>
        0 < outer_lower_denominator /\
        0 < outer_upper_denominator /\
        0 < inner_lower_denominator /\
        0 < inner_upper_denominator /\
        outer_lower * outer_upper_denominator <=
          outer_upper * outer_lower_denominator /\
        inner_lower * inner_upper_denominator <=
          inner_upper * inner_lower_denominator /\
        outer_lower * inner_lower_denominator <=
          inner_lower * outer_lower_denominator /\
        inner_upper * outer_upper_denominator <=
          outer_upper * inner_upper_denominator
End

Theorem bounded_interval64_covers_object_q_encloses:
  bounded_interval64_valid interval /\
  bounded_interval64_covers_object_q interval object_interval ==>
  bounded_object_q_interval_encloses
    (bounded_interval64_object_q_cv interval) object_interval
Proof
  Cases_on `interval`
  >> rename1 `BoundedInterval64 lower upper`
  >> strip_tac
  >> Cases_on `bounded_object_q_interval_ints object_interval`
  >- gvs
       [bounded_object_q_interval_encloses_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
        compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def]
  >> PairCases_on `x`
  >> gvs
       [bounded_object_q_interval_encloses_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
        compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def]
  >> conj_tac
  >- (irule
        (Q.INST
          [`left` |-> `bounded_signed64_to_int lower`,
           `right` |-> `bounded_signed64_to_int upper`,
           `multiplier` |-> `1099511627776:int`]
          compute_boundedIntervalTheory.bounded_int_mul_right_mono_nonnegative)
      >> simp [])
  >> conj_tac
  >- (`bounded_signed64_to_int lower * x1 =
        x1 * bounded_signed64_to_int lower` by INT_RING_TAC
      >> `x0 * 1099511627776 = (1099511627776:int) * x0` by
           INT_RING_TAC
      >> asm_rewrite_tac [])
  >> `x2 * 1099511627776 = (1099511627776:int) * x2` by
       INT_RING_TAC
  >> `bounded_signed64_to_int upper * x3 =
        x3 * bounded_signed64_to_int upper` by INT_RING_TAC
  >> asm_rewrite_tac []
QED

Definition bounded_object_q_square_certificate_exact_def:
  bounded_object_q_square_certificate_exact source_input word_input output <=>
    bounded_object_q_interval_encloses word_input source_input /\
    case bounded_object_q_interval_ints word_input of
    | NONE => F
    | SOME ((input_lower,input_lower_denominator),
            (input_upper,input_upper_denominator)) =>
      case bounded_object_q_interval_ints output of
      | NONE => F
      | SOME ((output_lower,output_lower_denominator),
              (output_upper,output_upper_denominator)) =>
        0 < input_lower_denominator /\
        0 < input_upper_denominator /\
        0 < output_lower_denominator /\
        0 < output_upper_denominator /\
        input_lower * input_upper_denominator <=
          input_upper * input_lower_denominator /\
        output_lower * output_upper_denominator <=
          output_upper * output_lower_denominator /\
        (if 0 <= input_lower then
           output_lower * input_lower_denominator *
               input_lower_denominator <=
             input_lower * input_lower * output_lower_denominator
         else if input_upper <= 0 then
           output_lower * input_upper_denominator *
               input_upper_denominator <=
             input_upper * input_upper * output_lower_denominator
         else output_lower <= 0) /\
        input_lower * input_lower * output_upper_denominator <=
          output_upper * input_lower_denominator *
            input_lower_denominator /\
        input_upper * input_upper * output_upper_denominator <=
          output_upper * input_upper_denominator *
            input_upper_denominator
End

Theorem bounded_interval64_square_own_object_q_exact:
  bounded_interval64_covers_object_q input object_input /\
  bounded_interval64_square input = SOME output ==>
  bounded_object_q_square_certificate_exact object_input
    (bounded_interval64_object_q_cv input)
    (bounded_interval64_object_q_cv output)
Proof
  strip_tac
  >> `bounded_interval64_valid input` by
       fs [compute_boundedIntervalSquareTheory.bounded_interval64_square_def]
  >> `bounded_object_q_interval_encloses
        (bounded_interval64_object_q_cv input) object_input` by
       metis_tac [bounded_interval64_covers_object_q_encloses]
  >> Cases_on `input`
  >> Cases_on `output`
  >> rename1
       `bounded_interval64_square (BoundedInterval64 input_lower input_upper) =
          SOME (BoundedInterval64 output_lower output_upper)`
  >> `bounded_interval64_contains_int
        (BoundedInterval64 input_lower input_upper)
        (bounded_signed64_to_int input_lower) /\
      bounded_interval64_contains_int
        (BoundedInterval64 input_lower input_upper)
        (bounded_signed64_to_int input_upper)` by
       fs
         [compute_boundedIntervalTheory.bounded_interval64_valid_def,
          compute_boundedIntervalTheory.bounded_interval64_contains_int_def,
          compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
  >> `bounded_interval64_contains_scaled_int
        (BoundedInterval64 output_lower output_upper)
        (&1099511627776:int)
        (bounded_signed64_to_int input_lower *
          bounded_signed64_to_int input_lower) /\
      bounded_interval64_contains_scaled_int
        (BoundedInterval64 output_lower output_upper)
        (&1099511627776:int)
        (bounded_signed64_to_int input_upper *
          bounded_signed64_to_int input_upper)` by
       metis_tac [bounded_interval64_square_contains_scaled_square]
  >> fs
       [bounded_object_q_square_certificate_exact_def,
        compute_boundedIntervalTheory.bounded_interval64_contains_scaled_int_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def]
  >> rpt conj_tac
  >- (irule
        (Q.INST
          [`left` |-> `bounded_signed64_to_int input_lower`,
           `right` |-> `bounded_signed64_to_int input_upper`,
           `multiplier` |-> `1099511627776:int`]
          compute_boundedIntervalTheory.bounded_int_mul_right_mono_nonnegative)
      >> fs
           [compute_boundedIntervalTheory.bounded_interval64_valid_def,
            compute_boundedSignedEndpointTheory.bounded_signed64_le_correct])
  >- (`(1099511627776:int) * bounded_signed64_to_int output_lower <=
        1099511627776 * bounded_signed64_to_int output_upper` by
        intLib.ARITH_TAC
      >> `bounded_signed64_to_int output_lower * 1099511627776 =
          (1099511627776:int) * bounded_signed64_to_int output_lower` by
           INT_RING_TAC
      >> `bounded_signed64_to_int output_upper * 1099511627776 =
          (1099511627776:int) * bounded_signed64_to_int output_upper` by
           INT_RING_TAC
      >> asm_rewrite_tac [])
  >- (Cases_on `0 <= bounded_signed64_to_int input_lower`
      >- (fs [] >> intLib.ARITH_TAC)
      >> fs []
      >> Cases_on `bounded_signed64_to_int input_upper <= 0`
      >- (fs [] >> intLib.ARITH_TAC)
      >> fs []
      >> imp_res_tac
           compute_boundedIntervalSquareTheory.bounded_interval64_square_crossing_shape
      >> fs
           [compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct,
            compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def])
  >- intLib.ARITH_TAC
  >> intLib.ARITH_TAC
QED

Theorem bounded_taylor64_atan_refinement_trace:
  bounded_taylor64_atan radii center_lower_reciprocal
      center_upper_reciprocal center_derivative box_derivative source =
      SOME result ==>
  ?source_domain center_value center_gradient value_bound gradient_bounds
      hessian center_result center_square center_denominator box_square
      box_denominator box_derivative_square box_twice box_second_magnitude.
    source =
      BoundedTaylor64 source_domain center_value center_gradient value_bound
        gradient_bounds hessian /\
    bounded_interval64_atan_range center_value center_lower_reciprocal
      center_upper_reciprocal = SOME center_result /\
    bounded_interval64_square center_value = SOME center_square /\
    bounded_interval64_add bounded_atan_one center_square =
      SOME center_denominator /\
    bounded_interval64_square value_bound = SOME box_square /\
    bounded_interval64_add bounded_atan_one box_square =
      SOME box_denominator /\
    bounded_interval64_inv_certificate center_denominator
      center_derivative /\
    bounded_interval64_inv_certificate box_denominator box_derivative /\
    bounded_interval64_square box_derivative =
      SOME box_derivative_square /\
    bounded_interval64_add value_bound value_bound = SOME box_twice /\
    bounded_interval64_mul box_twice box_derivative_square =
      SOME box_second_magnitude /\
    bounded_taylor64_unary_complete radii T center_result
      center_derivative box_derivative
      (bounded_interval64_neg box_second_magnitude) source = SOME result
Proof
  Cases_on `source`
  >> rw [compute_boundedTaylorAtanTheory.bounded_taylor64_atan_def]
  >> every_case_tac
  >> gvs []
  >> rpt (first_assum (irule_at Any))
QED

val _ = export_theory ();
