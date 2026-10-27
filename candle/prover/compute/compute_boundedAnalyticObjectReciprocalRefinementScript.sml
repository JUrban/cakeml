(*****************************************************************************
 * Exact object-q soundness for positive scale-2^40 reciprocal certificates.
 *
 * The executable certificate authenticates reciprocal endpoints with exact
 * products at scale 2^80.  This proof-only layer transports those products
 * across an enclosing word input to the original source-rational interval.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectReciprocalRefinement
Ancestors
  compute_boundedAnalyticObjectSqrtRefinement
Libs
  bossLib preamble intLib

Definition bounded_object_q_positive_inv_certificate_exact_def:
  bounded_object_q_positive_inv_certificate_exact input output <=>
    case bounded_object_q_interval_ints input of
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
        0 < input_lower /\
        0 < input_upper /\
        0 < output_lower /\
        0 < output_upper /\
        input_lower * input_upper_denominator <=
          input_upper * input_lower_denominator /\
        output_lower * output_upper_denominator <=
          output_upper * output_lower_denominator /\
        output_lower * input_upper <=
          input_upper_denominator * output_lower_denominator /\
        input_lower_denominator * output_upper_denominator <=
          output_upper * input_lower
End

Theorem bounded_interval64_inv_certificate_valid_components:
  bounded_interval64_inv_certificate input output ==>
  bounded_interval64_valid input /\ bounded_interval64_valid output
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> rw
       [compute_boundedReciprocalCertificateTheory.bounded_interval64_inv_certificate_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_interval64_inv_certificate_positive_components:
  bounded_interval64_inv_certificate input output /\
  bounded_signed64_strict_positive (bounded_interval64_lower input) ==>
  0 < bounded_signed64_to_int (bounded_interval64_lower input) /\
  0 < bounded_signed64_to_int (bounded_interval64_upper input) /\
  0 < bounded_signed64_to_int (bounded_interval64_lower output) /\
  0 < bounded_signed64_to_int (bounded_interval64_upper output) /\
  bounded_signed64_to_int (bounded_interval64_lower input) <=
    bounded_signed64_to_int (bounded_interval64_upper input) /\
  bounded_signed64_to_int (bounded_interval64_lower output) <=
    bounded_signed64_to_int (bounded_interval64_upper output) /\
  bounded_signed64_to_int (bounded_interval64_lower output) *
      bounded_signed64_to_int (bounded_interval64_upper input) <=
    (&1208925819614629174706176:int) /\
  (&1208925819614629174706176:int) <=
    bounded_signed64_to_int (bounded_interval64_upper output) *
      bounded_signed64_to_int (bounded_interval64_lower input)
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> strip_tac
  >> imp_res_tac
       compute_boundedReciprocalCertificateTheory.bounded_interval64_inv_certificate_positive_int_bounds
  >> imp_res_tac
       compute_boundedReciprocalCertificateTheory.bounded_interval64_inv_certificate_positive_signs
  >> imp_res_tac bounded_interval64_inv_certificate_valid_components
  >> fs
       [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_correct,
        compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
QED

Theorem bounded_int_positive_from_positive_left_product:
  0 < (multiplier:int) /\ 0 < multiplier * value ==>
  0 < value
Proof
  strip_tac
  >> mp_tac
       (Q.SPECL [`multiplier`, `0:int`, `value`]
         integerTheory.INT_LT_MONO)
  >> asm_rewrite_tac [integerTheory.INT_MUL_RZERO]
QED

Theorem bounded_int_le_cancel_positive_left:
  0 < (multiplier:int) /\ multiplier * left <= multiplier * right ==>
  left <= right
Proof
  strip_tac
  >> qpat_x_assum `0 < multiplier`
       (fn positive =>
          irule
            (iffLR
              (MP
                (Q.SPECL [`multiplier`, `left`, `right`]
                  integerTheory.INT_LE_MONO)
                positive)))
  >> asm_rewrite_tac []
QED

Theorem bounded_object_q_covered_positive_lower:
  0 < (scale:int) /\
  0 < input_lower_denominator /\
  input_lower_denominator * input_word_lower <= scale * input_lower /\
  0 < input_word_lower ==>
  0 < input_lower
Proof
  strip_tac
  >> `0 < input_lower_denominator * input_word_lower` by
       (irule
          (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
        >> asm_rewrite_tac [])
  >> `0 < scale * input_lower` by
       (irule integerTheory.INT_LTE_TRANS
        >> qexists_tac `input_lower_denominator * input_word_lower`
        >> asm_rewrite_tac [])
  >> match_mp_tac
       (Q.INST [`multiplier` |-> `scale`, `value` |-> `input_lower`]
         bounded_int_positive_from_positive_left_product)
  >> asm_rewrite_tac []
QED

Theorem bounded_object_q_ordered_positive_upper:
  0 < (input_lower_denominator:int) /\
  0 < input_upper_denominator /\
  0 < input_lower /\
  input_lower * input_upper_denominator <=
    input_upper * input_lower_denominator ==>
  0 < input_upper
Proof
  strip_tac
  >> `0 < input_lower * input_upper_denominator` by
       (irule
          (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
        >> asm_rewrite_tac [])
  >> `0 < input_upper * input_lower_denominator` by
       (irule integerTheory.INT_LTE_TRANS
        >> qexists_tac `input_lower * input_upper_denominator`
        >> asm_rewrite_tac [])
  >> `input_lower_denominator * input_upper =
        input_upper * input_lower_denominator` by INT_RING_TAC
  >> `0 < input_lower_denominator * input_upper` by
       asm_rewrite_tac []
  >> match_mp_tac
       (Q.INST
         [`multiplier` |-> `input_lower_denominator`,
          `value` |-> `input_upper`]
         bounded_int_positive_from_positive_left_product)
  >> asm_rewrite_tac []
QED

Theorem bounded_object_q_covered_positive_interval:
  0 < (scale:int) /\
  0 < input_lower_denominator /\
  0 < input_upper_denominator /\
  input_lower * input_upper_denominator <=
    input_upper * input_lower_denominator /\
  input_lower_denominator * input_word_lower <= scale * input_lower /\
  0 < input_word_lower ==>
  0 < input_lower /\
  0 < input_upper
Proof
  strip_tac
  >> `0 < input_lower` by
       (match_mp_tac
          (Q.INST
            [`scale` |-> `scale`,
             `input_lower_denominator` |-> `input_lower_denominator`,
             `input_word_lower` |-> `input_word_lower`,
             `input_lower` |-> `input_lower`]
            bounded_object_q_covered_positive_lower)
        >> asm_rewrite_tac [])
  >> `0 < input_upper` by
       (match_mp_tac
          (Q.INST
            [`input_lower_denominator` |-> `input_lower_denominator`,
             `input_upper_denominator` |-> `input_upper_denominator`,
             `input_lower` |-> `input_lower`,
             `input_upper` |-> `input_upper`]
            bounded_object_q_ordered_positive_upper)
        >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem bounded_object_q_positive_inv_lower_transfer:
  0 < (scale:int) /\
  0 < input_upper_denominator /\
  scale * input_upper <=
    input_upper_denominator * input_word_upper /\
  0 <= output_lower /\
  output_lower * input_word_upper <= scale * scale ==>
  output_lower * input_upper <= input_upper_denominator * scale
Proof
  strip_tac
  >> `0 <= input_upper_denominator` by
       (irule integerTheory.INT_LT_IMP_LE >> asm_rewrite_tac [])
  >> `output_lower * (scale * input_upper) <=
      output_lower * (input_upper_denominator * input_word_upper)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> asm_rewrite_tac [])
  >> `input_upper_denominator *
        (output_lower * input_word_upper) <=
      input_upper_denominator * (scale * scale)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> asm_rewrite_tac [])
  >> `output_lower * (scale * input_upper) =
        scale * (output_lower * input_upper)` by INT_RING_TAC
  >> `output_lower *
        (input_upper_denominator * input_word_upper) =
      input_upper_denominator *
        (output_lower * input_word_upper)` by INT_RING_TAC
  >> `input_upper_denominator * (scale * scale) =
        scale * (input_upper_denominator * scale)` by INT_RING_TAC
  >> `scale * (output_lower * input_upper) <=
        input_upper_denominator *
          (output_lower * input_word_upper)` by
       (qpat_x_assum
          `output_lower * (scale * input_upper) <=
             output_lower *
               (input_upper_denominator * input_word_upper)` mp_tac
        >> asm_rewrite_tac [])
  >> `input_upper_denominator *
        (output_lower * input_word_upper) <=
      scale * (input_upper_denominator * scale)` by
       (qpat_x_assum
          `input_upper_denominator *
             (output_lower * input_word_upper) <=
           input_upper_denominator * (scale * scale)` mp_tac
        >> asm_rewrite_tac [])
  >> match_mp_tac
       (Q.INST
         [`multiplier` |-> `scale`,
          `left` |-> `output_lower * input_upper`,
          `right` |-> `input_upper_denominator * scale`]
         bounded_int_le_cancel_positive_left)
  >> asm_rewrite_tac []
  >> irule integerTheory.INT_LE_TRANS
  >> qexists_tac
       `input_upper_denominator *
          (output_lower * input_word_upper)`
  >> asm_rewrite_tac []
QED

Theorem bounded_object_q_positive_inv_upper_transfer:
  0 < (scale:int) /\
  0 < input_lower_denominator /\
  input_lower_denominator * input_word_lower <= scale * input_lower /\
  0 <= output_upper /\
  scale * scale <= output_upper * input_word_lower ==>
  input_lower_denominator * scale <= output_upper * input_lower
Proof
  strip_tac
  >> `0 <= input_lower_denominator` by
       (irule integerTheory.INT_LT_IMP_LE >> asm_rewrite_tac [])
  >> `input_lower_denominator * (scale * scale) <=
      input_lower_denominator *
        (output_upper * input_word_lower)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> asm_rewrite_tac [])
  >> `output_upper *
        (input_lower_denominator * input_word_lower) <=
      output_upper * (scale * input_lower)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> asm_rewrite_tac [])
  >> `input_lower_denominator *
        (output_upper * input_word_lower) =
      output_upper *
        (input_lower_denominator * input_word_lower)` by INT_RING_TAC
  >> `output_upper * (scale * input_lower) =
        scale * (output_upper * input_lower)` by INT_RING_TAC
  >> `input_lower_denominator * (scale * scale) =
        scale * (input_lower_denominator * scale)` by INT_RING_TAC
  >> `scale * (input_lower_denominator * scale) <=
        output_upper *
          (input_lower_denominator * input_word_lower)` by
       (qpat_x_assum
          `input_lower_denominator * (scale * scale) <=
           input_lower_denominator *
             (output_upper * input_word_lower)` mp_tac
        >> asm_rewrite_tac [])
  >> `output_upper *
        (input_lower_denominator * input_word_lower) <=
      scale * (output_upper * input_lower)` by
       (qpat_x_assum
          `output_upper *
             (input_lower_denominator * input_word_lower) <=
           output_upper * (scale * input_lower)` mp_tac
        >> asm_rewrite_tac [])
  >> match_mp_tac
       (Q.INST
         [`multiplier` |-> `scale`,
          `left` |-> `input_lower_denominator * scale`,
          `right` |-> `output_upper * input_lower`]
         bounded_int_le_cancel_positive_left)
  >> asm_rewrite_tac []
  >> irule integerTheory.INT_LE_TRANS
  >> qexists_tac
       `output_upper *
          (input_lower_denominator * input_word_lower)`
  >> asm_rewrite_tac []
QED

Theorem bounded_object_q_positive_inv_cross_product_transfer:
  0 < (scale:int) /\
  0 < input_lower_denominator /\
  0 < input_upper_denominator /\
  input_lower * input_upper_denominator <=
    input_upper * input_lower_denominator /\
  input_lower_denominator * input_word_lower <= scale * input_lower /\
  scale * input_upper <=
    input_upper_denominator * input_word_upper /\
  0 < input_word_lower /\
  0 < input_word_upper /\
  0 < output_lower /\
  0 < output_upper /\
  output_lower <= output_upper /\
  output_lower * input_word_upper <= scale * scale /\
  scale * scale <= output_upper * input_word_lower ==>
  0 < input_lower /\
  0 < input_upper /\
  output_lower * scale <= output_upper * scale /\
  output_lower * input_upper <= input_upper_denominator * scale /\
  input_lower_denominator * scale <= output_upper * input_lower
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`scale` |-> `scale`,
          `input_lower_denominator` |-> `input_lower_denominator`,
          `input_upper_denominator` |-> `input_upper_denominator`,
          `input_lower` |-> `input_lower`,
          `input_upper` |-> `input_upper`,
          `input_word_lower` |-> `input_word_lower`]
         bounded_object_q_covered_positive_interval)
  >> impl_tac
  >- asm_rewrite_tac []
  >> strip_tac
  >> `0 <= output_lower` by
       (irule integerTheory.INT_LT_IMP_LE >> asm_rewrite_tac [])
  >> `0 <= output_upper` by
       (irule integerTheory.INT_LT_IMP_LE >> asm_rewrite_tac [])
  >> `output_lower * input_upper <=
        input_upper_denominator * scale` by
       (match_mp_tac
          (Q.INST
            [`scale` |-> `scale`,
             `input_upper_denominator` |-> `input_upper_denominator`,
             `input_upper` |-> `input_upper`,
             `input_word_upper` |-> `input_word_upper`,
             `output_lower` |-> `output_lower`]
            bounded_object_q_positive_inv_lower_transfer)
        >> asm_rewrite_tac [])
  >> `input_lower_denominator * scale <=
        output_upper * input_lower` by
       (match_mp_tac
          (Q.INST
            [`scale` |-> `scale`,
             `input_lower_denominator` |-> `input_lower_denominator`,
             `input_word_lower` |-> `input_word_lower`,
             `input_lower` |-> `input_lower`,
             `output_upper` |-> `output_upper`]
            bounded_object_q_positive_inv_upper_transfer)
        >> asm_rewrite_tac [])
  >> rpt conj_tac
  >- asm_rewrite_tac []
  >- asm_rewrite_tac []
  >- (match_mp_tac
        compute_boundedIntervalTheory.bounded_int_mul_right_mono_nonnegative
      >> asm_rewrite_tac []
      >> irule integerTheory.INT_LT_IMP_LE
      >> asm_rewrite_tac [])
  >- asm_rewrite_tac []
  >> asm_rewrite_tac []
QED

Theorem bounded_interval64_positive_inv_certificate_covers_object_q:
  bounded_interval64_covers_object_q input object_input /\
  bounded_interval64_inv_certificate input output /\
  bounded_signed64_strict_positive (bounded_interval64_lower input) ==>
  bounded_object_q_positive_inv_certificate_exact object_input
    (bounded_interval64_object_q_cv output)
Proof
  strip_tac
  >> Cases_on `bounded_object_q_interval_ints object_input`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
  >> PairCases_on `x`
  >> imp_res_tac bounded_interval64_inv_certificate_positive_components
  >> fs
       [bounded_object_q_positive_inv_certificate_exact_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def]
  >> match_mp_tac
       (Q.INST
         [`input_word_lower` |->
            `bounded_signed64_to_int (bounded_interval64_lower input)`,
          `input_word_upper` |->
            `bounded_signed64_to_int (bounded_interval64_upper input)`]
         bounded_object_q_positive_inv_cross_product_transfer)
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
