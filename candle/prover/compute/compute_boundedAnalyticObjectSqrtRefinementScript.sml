(*****************************************************************************
 * Exact object-q soundness for scale-2^40 square-root certificates.
 *
 * The executable certificate checks word endpoints.  This proof-only layer
 * states the corresponding rational contract and transports it across the
 * generic word-to-source enclosure relation.  It adds no runtime operation.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectSqrtRefinement
Ancestors
  compute_boundedAnalyticObjectCertificateRefinement
Libs
  bossLib preamble intLib

Definition bounded_object_q_sqrt_certificate_exact_def:
  bounded_object_q_sqrt_certificate_exact input output <=>
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
        0 <= input_lower /\
        0 <= output_lower /\
        input_lower * input_upper_denominator <=
          input_upper * input_lower_denominator /\
        output_lower * output_upper_denominator <=
          output_upper * output_lower_denominator /\
        output_lower * output_lower * input_lower_denominator <=
          input_lower * output_lower_denominator *
            output_lower_denominator /\
        input_upper * output_upper_denominator *
            output_upper_denominator <=
          output_upper * output_upper * input_upper_denominator
End

Theorem bounded_interval64_sqrt_certificate_exact_own_q:
  bounded_interval64_sqrt_certificate input output ==>
  bounded_object_q_sqrt_certificate_exact
    (bounded_interval64_object_q_cv input)
    (bounded_interval64_object_q_cv output)
Proof
  `!x y:int. x <= y ==>
      x * 1099511627776 <= y * 1099511627776` by intLib.ARITH_TAC
  >> Cases_on `input`
  >> Cases_on `output`
  >> strip_tac
  >> imp_res_tac
       compute_boundedSqrtCertificateTheory.bounded_interval64_sqrt_certificate_int_bounds
  >> imp_res_tac
       compute_boundedSqrtCertificateTheory.bounded_interval64_sqrt_certificate_nonnegative
  >> fs
       [bounded_object_q_sqrt_certificate_exact_def,
        compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct]
  >> conj_tac
  >- (qpat_x_assum
        `!x y:int. x <= y ==>
           x * 1099511627776 <= y * 1099511627776`
        (mp_tac o Q.SPECL
          [`bounded_signed64_to_int b' * bounded_signed64_to_int b'`,
           `1099511627776 * bounded_signed64_to_int b`])
      >> strip_tac
      >> `1099511627776 * bounded_signed64_to_int b * 1099511627776 =
            bounded_signed64_to_int b * 1099511627776 *
              1099511627776` by INT_RING_TAC
      >> qpat_x_assum
           `(bounded_signed64_to_int b' * bounded_signed64_to_int b' <=
              1099511627776 * bounded_signed64_to_int b) ==> _`
           mp_tac
      >> asm_rewrite_tac [])
  >> qpat_x_assum
       `!x y:int. x <= y ==>
          x * 1099511627776 <= y * 1099511627776`
       (mp_tac o Q.SPECL
         [`1099511627776 * bounded_signed64_to_int b0`,
          `bounded_signed64_to_int b0' * bounded_signed64_to_int b0'`])
  >> strip_tac
  >> `1099511627776 * bounded_signed64_to_int b0 * 1099511627776 =
        bounded_signed64_to_int b0 * 1099511627776 *
          1099511627776` by INT_RING_TAC
  >> qpat_x_assum
       `(1099511627776 * bounded_signed64_to_int b0 <=
          bounded_signed64_to_int b0' * bounded_signed64_to_int b0') ==> _`
       mp_tac
  >> asm_rewrite_tac []
QED

Theorem bounded_interval64_sqrt_certificate_components:
  bounded_interval64_sqrt_certificate input output ==>
  0 <= bounded_signed64_to_int (bounded_interval64_lower input) /\
  0 <= bounded_signed64_to_int (bounded_interval64_lower output) /\
  bounded_signed64_to_int (bounded_interval64_lower output) <=
    bounded_signed64_to_int (bounded_interval64_upper output) /\
  bounded_signed64_to_int (bounded_interval64_lower output) *
      bounded_signed64_to_int (bounded_interval64_lower output) <=
    (&1099511627776:int) *
      bounded_signed64_to_int (bounded_interval64_lower input) /\
  (&1099511627776:int) *
      bounded_signed64_to_int (bounded_interval64_upper input) <=
    bounded_signed64_to_int (bounded_interval64_upper output) *
      bounded_signed64_to_int (bounded_interval64_upper output)
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> strip_tac
  >> imp_res_tac
       compute_boundedSqrtCertificateTheory.bounded_interval64_sqrt_certificate_int_bounds
  >> imp_res_tac
       compute_boundedSqrtCertificateTheory.bounded_interval64_sqrt_certificate_nonnegative
  >> fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct]
QED

Theorem bounded_object_q_sqrt_cross_product_transfer:
  0 < (scale:int) /\
  0 < input_lower_denominator /\
  0 < input_upper_denominator /\
  0 <= input_word_lower /\
  0 <= output_lower /\
  input_lower * input_upper_denominator <=
    input_upper * input_lower_denominator /\
  input_lower_denominator * input_word_lower <= scale * input_lower /\
  scale * input_upper <=
    input_upper_denominator * input_word_upper /\
  output_lower <= output_upper /\
  output_lower * output_lower <= scale * input_word_lower /\
  scale * input_word_upper <= output_upper * output_upper ==>
  0 <= input_lower /\
  output_lower * scale <= output_upper * scale /\
  output_lower * output_lower * input_lower_denominator <=
    input_lower * scale * scale /\
  input_upper * scale * scale <=
    output_upper * output_upper * input_upper_denominator
Proof
  strip_tac
  >> `0 <= input_lower_denominator` by
       (irule integerTheory.INT_LT_IMP_LE >> asm_rewrite_tac [])
  >> `0 <= input_lower_denominator * input_word_lower` by
       (irule integerTheory.INT_LE_MUL >> asm_rewrite_tac [])
  >> `0 <= scale * input_lower` by
       (irule integerTheory.INT_LE_TRANS
        >> qexists_tac `input_lower_denominator * input_word_lower`
        >> asm_rewrite_tac [])
  >> `0 <= input_lower` by
       (mp_tac
          (Q.SPECL [`scale`, `0:int`, `input_lower`]
            integerTheory.INT_LE_MONO)
        >> asm_rewrite_tac [integerTheory.INT_MUL_RZERO])
  >> `scale * output_lower <= scale * output_upper` by
       (mp_tac
          (Q.SPECL [`scale`, `output_lower`, `output_upper`]
            integerTheory.INT_LE_MONO)
        >> asm_rewrite_tac [])
  >> `input_lower_denominator *
        (output_lower * output_lower) <=
      input_lower_denominator * (scale * input_word_lower)` by
       (mp_tac
          (Q.SPECL
            [`input_lower_denominator`, `output_lower * output_lower`,
             `scale * input_word_lower`]
            integerTheory.INT_LE_MONO)
        >> asm_rewrite_tac [])
  >> `scale * (input_lower_denominator * input_word_lower) <=
      scale * (scale * input_lower)` by
       (mp_tac
          (Q.SPECL
            [`scale`, `input_lower_denominator * input_word_lower`,
             `scale * input_lower`]
            integerTheory.INT_LE_MONO)
        >> asm_rewrite_tac [])
  >> `scale * (scale * input_upper) <=
      scale * (input_upper_denominator * input_word_upper)` by
       (mp_tac
          (Q.SPECL
            [`scale`, `scale * input_upper`,
             `input_upper_denominator * input_word_upper`]
            integerTheory.INT_LE_MONO)
        >> asm_rewrite_tac [])
  >> `input_upper_denominator * (scale * input_word_upper) <=
      input_upper_denominator * (output_upper * output_upper)` by
       (mp_tac
          (Q.SPECL
            [`input_upper_denominator`, `scale * input_word_upper`,
             `output_upper * output_upper`]
            integerTheory.INT_LE_MONO)
        >> asm_rewrite_tac [])
  >> `output_lower * scale = scale * output_lower` by INT_RING_TAC
  >> `output_upper * scale = scale * output_upper` by INT_RING_TAC
  >> `output_lower * output_lower * input_lower_denominator =
        input_lower_denominator * (output_lower * output_lower)` by
       INT_RING_TAC
  >> `input_lower * scale * scale =
        scale * (scale * input_lower)` by INT_RING_TAC
  >> `input_lower_denominator * (scale * input_word_lower) =
        scale * (input_lower_denominator * input_word_lower)` by
       INT_RING_TAC
  >> `input_upper * scale * scale =
        scale * (scale * input_upper)` by INT_RING_TAC
  >> `scale * (input_upper_denominator * input_word_upper) =
        input_upper_denominator * (scale * input_word_upper)` by
       INT_RING_TAC
  >> `output_upper * output_upper * input_upper_denominator =
        input_upper_denominator * (output_upper * output_upper)` by
       INT_RING_TAC
  >> rpt conj_tac
  >- asm_rewrite_tac []
  >- asm_rewrite_tac []
  >- (asm_rewrite_tac []
      >> irule integerTheory.INT_LE_TRANS
      >> qexists_tac
           `input_lower_denominator * (scale * input_word_lower)`
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
  >> irule integerTheory.INT_LE_TRANS
  >> qexists_tac
       `scale * (input_upper_denominator * input_word_upper)`
  >> asm_rewrite_tac []
QED

Theorem bounded_interval64_sqrt_certificate_covers_object_q:
  bounded_interval64_covers_object_q input object_input /\
  bounded_interval64_sqrt_certificate input output ==>
  bounded_object_q_sqrt_certificate_exact object_input
    (bounded_interval64_object_q_cv output)
Proof
  strip_tac
  >> Cases_on `bounded_object_q_interval_ints object_input`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
  >> PairCases_on `x`
  >> imp_res_tac
       bounded_interval64_sqrt_certificate_components
  >> fs
       [bounded_object_q_sqrt_certificate_exact_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def]
  >> match_mp_tac
       (Q.INST
         [`input_word_lower` |->
            `bounded_signed64_to_int (bounded_interval64_lower input)`,
          `input_word_upper` |->
            `bounded_signed64_to_int (bounded_interval64_upper input)`]
         bounded_object_q_sqrt_cross_product_transfer)
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
