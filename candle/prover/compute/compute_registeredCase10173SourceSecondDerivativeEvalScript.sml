(*****************************************************************************
 * Registered source-to-decimal refinement for sqrt second derivatives.
 *
 * This closes the local algebraic bridge for the registered generic source
 * operation: exact rational doubling, interval multiplication, normalization,
 * reciprocal, and negation.  Ordered positive endpoints and the authenticated
 * direct-rounding identity connect that result to the packet's fixed-decimal
 * reciprocal without assuming a particular GCD.  Identification of this
 * operand with the Hessian value_bound produced by the Taylor computation is
 * a separate source-contract obligation.
 *****************************************************************************)
Theory compute_registeredCase10173SourceSecondDerivativeEval
Ancestors
  compute_registeredCase10173SqrtSecondDerivativeRelationEval
  compute_registeredCase10173PositiveIntervalOrderEquiv
  compute_registeredCase10173SourceSecondDerivativeConversionEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_source_sqrt_second_derivative_decimal_eval:
  0 < root_lower /\ 0 < root_lower_denominator /\
  0 < root_upper /\ 0 < root_upper_denominator /\
  0 < input_lower /\ 0 < input_lower_denominator /\
  0 < input_upper /\ 0 < input_upper_denominator /\
  root_lower * root_upper_denominator <=
    root_upper * root_lower_denominator /\
  input_lower * input_upper_denominator <=
    input_upper * input_lower_denominator /\
  bounded_case10173_source_sqrt_dd_interval64_exact
    (Pair
      (Pair (Pair (Num root_lower) (Num 0))
        (Num (root_lower_denominator - 1)))
      (Pair (Pair (Num root_upper) (Num 0))
        (Num (root_upper_denominator - 1))))
    (Pair
      (Pair (Pair (Num input_lower) (Num 0))
        (Num (input_lower_denominator - 1)))
      (Pair (Pair (Num input_upper) (Num 0))
        (Num (input_upper_denominator - 1))))
    reciprocal /\
  155 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_of_q»
        [App «candle_cv_q_dim_jet_sqrt_dd»
          [from_cv
            (Pair
              (Pair (Pair (Num root_lower) (Num 0))
                (Num (root_lower_denominator - 1)))
              (Pair (Pair (Num root_upper) (Num 0))
                (Num (root_upper_denominator - 1))));
           from_cv
            (Pair
              (Pair (Pair (Num input_lower) (Num 0))
                (Num (input_lower_denominator - 1)))
              (Pair (Pair (Num input_upper) (Num 0))
                (Num (input_upper_denominator - 1))))]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (bounded_interval64_neg reciprocal))),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`certificate_lower` |-> `root_lower`,
          `certificate_lower_denominator` |-> `root_lower_denominator`,
          `certificate_upper` |-> `root_upper`,
          `certificate_upper_denominator` |-> `root_upper_denominator`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_registeredCase10173SqrtSecondDerivativeRelationEvalTheory.registered_case10173_q_dim_jet_sqrt_dd_positive_relation_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> `(root_lower * root_lower_denominator +
        root_lower * root_lower_denominator) *
        (root_upper_denominator * root_upper_denominator) <=
      (root_upper * root_upper_denominator +
        root_upper * root_upper_denominator) *
        (root_lower_denominator * root_lower_denominator)` by
       (irule
          compute_registeredCase10173PositiveIntervalOrderEquivTheory.registered_case10173_positive_q_self_add_order
        >> asm_rewrite_tac [])
  >> `(input_lower * input_lower_denominator +
        input_lower * input_lower_denominator) *
        (input_upper_denominator * input_upper_denominator) <=
      (input_upper * input_upper_denominator +
        input_upper * input_upper_denominator) *
        (input_lower_denominator * input_lower_denominator)` by
       (irule
          compute_registeredCase10173PositiveIntervalOrderEquivTheory.registered_case10173_positive_q_self_add_order
        >> asm_rewrite_tac [])
  >> `certificate_twice_lower * certificate_twice_upper_denominator <=
      certificate_twice_upper * certificate_twice_lower_denominator` by
       (mp_tac
          (Q.INST
            [`left_lower` |-> `certificate_twice_lower`,
             `left_lower_denominator` |->
               `certificate_twice_lower_denominator`,
             `left_upper` |-> `certificate_twice_upper`,
             `left_upper_denominator` |->
               `certificate_twice_upper_denominator`,
             `right_lower` |->
               `root_lower * root_lower_denominator +
                root_lower * root_lower_denominator`,
             `right_lower_denominator` |->
               `root_lower_denominator * root_lower_denominator`,
             `right_upper` |->
               `root_upper * root_upper_denominator +
                root_upper * root_upper_denominator`,
             `right_upper_denominator` |->
               `root_upper_denominator * root_upper_denominator`]
            compute_registeredCase10173PositiveIntervalOrderEquivTheory.registered_case10173_positive_q_order_equiv)
        >> impl_tac
        >- (conj_tac
            >- (qpat_assum
                  `0 < certificate_twice_lower_denominator`
                  ACCEPT_TAC)
            >> conj_tac
            >- (qpat_assum
                  `0 < certificate_twice_upper_denominator`
                  ACCEPT_TAC)
            >> conj_tac
            >- (irule arithmeticTheory.MULT_POS
                >> conj_tac
                >- (qpat_assum `0 < root_lower_denominator` ACCEPT_TAC)
                >> qpat_assum `0 < root_lower_denominator` ACCEPT_TAC)
            >> conj_tac
            >- (irule arithmeticTheory.MULT_POS
                >> conj_tac
                >- (qpat_assum `0 < root_upper_denominator` ACCEPT_TAC)
                >> qpat_assum `0 < root_upper_denominator` ACCEPT_TAC)
            >> conj_tac
            >- (qpat_assum
                  `bounded_case10173_q_cv_equiv
                    (Pair
                      (Pair (Num certificate_twice_lower) (Num 0)) _) _`
                  ACCEPT_TAC)
            >> conj_tac
            >- (qpat_assum
                  `bounded_case10173_q_cv_equiv
                    (Pair
                      (Pair (Num certificate_twice_upper) (Num 0)) _) _`
                  ACCEPT_TAC)
            >> qpat_assum
                 `(root_lower * root_lower_denominator +
                    root_lower * root_lower_denominator) * _ <= _`
                 ACCEPT_TAC)
        >> strip_tac)
  >> `input_twice_lower * input_twice_upper_denominator <=
      input_twice_upper * input_twice_lower_denominator` by
       (mp_tac
          (Q.INST
            [`left_lower` |-> `input_twice_lower`,
             `left_lower_denominator` |-> `input_twice_lower_denominator`,
             `left_upper` |-> `input_twice_upper`,
             `left_upper_denominator` |-> `input_twice_upper_denominator`,
             `right_lower` |->
               `input_lower * input_lower_denominator +
                input_lower * input_lower_denominator`,
             `right_lower_denominator` |->
               `input_lower_denominator * input_lower_denominator`,
             `right_upper` |->
               `input_upper * input_upper_denominator +
                input_upper * input_upper_denominator`,
             `right_upper_denominator` |->
               `input_upper_denominator * input_upper_denominator`]
            compute_registeredCase10173PositiveIntervalOrderEquivTheory.registered_case10173_positive_q_order_equiv)
        >> impl_tac
        >- (conj_tac
            >- (qpat_assum
                  `0 < input_twice_lower_denominator`
                  ACCEPT_TAC)
            >> conj_tac
            >- (qpat_assum
                  `0 < input_twice_upper_denominator`
                  ACCEPT_TAC)
            >> conj_tac
            >- (irule arithmeticTheory.MULT_POS
                >> conj_tac
                >- (qpat_assum `0 < input_lower_denominator` ACCEPT_TAC)
                >> qpat_assum `0 < input_lower_denominator` ACCEPT_TAC)
            >> conj_tac
            >- (irule arithmeticTheory.MULT_POS
                >> conj_tac
                >- (qpat_assum `0 < input_upper_denominator` ACCEPT_TAC)
                >> qpat_assum `0 < input_upper_denominator` ACCEPT_TAC)
            >> conj_tac
            >- (qpat_assum
                  `bounded_case10173_q_cv_equiv
                    (Pair (Pair (Num input_twice_lower) (Num 0)) _) _`
                  ACCEPT_TAC)
            >> conj_tac
            >- (qpat_assum
                  `bounded_case10173_q_cv_equiv
                    (Pair (Pair (Num input_twice_upper) (Num 0)) _) _`
                  ACCEPT_TAC)
            >> qpat_assum
                 `(input_lower * input_lower_denominator +
                    input_lower * input_lower_denominator) * _ <= _`
                 ACCEPT_TAC)
        >> strip_tac)
  >> mp_tac
       (Q.INST
         [`x_lower` |-> `certificate_twice_lower`,
          `x_lower_denominator` |-> `certificate_twice_lower_denominator`,
          `x_upper` |-> `certificate_twice_upper`,
          `x_upper_denominator` |-> `certificate_twice_upper_denominator`,
          `y_lower` |-> `input_twice_lower`,
          `y_lower_denominator` |-> `input_twice_lower_denominator`,
          `y_upper` |-> `input_twice_upper`,
          `y_upper_denominator` |-> `input_twice_upper_denominator`]
         compute_registeredCase10173PositiveIntervalOrderTheory.registered_case10173_q_minmax4_ordered_positive_products)
  >> impl_tac
  >- (conj_tac
      >- (qpat_assum
            `certificate_twice_lower *
               certificate_twice_upper_denominator <= _`
            ACCEPT_TAC)
      >> qpat_assum
           `input_twice_lower * input_twice_upper_denominator <= _`
           ACCEPT_TAC)
  >> strip_tac
  >> `bounded_case10173_q_cv_equiv
        (Pair (Pair (Num product_lower) (Num 0))
          (Num (product_lower_denominator - 1)))
        (Pair
          (Pair (Num (certificate_twice_lower * input_twice_lower))
            (Num 0))
          (Num
            (certificate_twice_lower_denominator *
               input_twice_lower_denominator - 1)))` by
       (qpat_x_assum
          `bounded_case10173_q_cv_equiv
            (Pair (Pair (Num product_lower) (Num 0)) _) _`
          mp_tac
        >> asm_rewrite_tac [])
  >> `bounded_case10173_q_cv_equiv
        (Pair (Pair (Num product_upper) (Num 0))
          (Num (product_upper_denominator - 1)))
        (Pair
          (Pair (Num (certificate_twice_upper * input_twice_upper))
            (Num 0))
          (Num
            (certificate_twice_upper_denominator *
               input_twice_upper_denominator - 1)))` by
       (qpat_x_assum
          `bounded_case10173_q_cv_equiv
            (Pair (Pair (Num product_upper) (Num 0)) _) _`
          mp_tac
        >> asm_rewrite_tac [])
  >> `bounded_case10173_q_cv_equiv
        (Pair
          (Pair (Num (certificate_twice_lower * input_twice_lower))
            (Num 0))
          (Num
            (certificate_twice_lower_denominator *
               input_twice_lower_denominator - 1)))
        (Pair
          (Pair
            (Num
              ((root_lower * root_lower_denominator +
                 root_lower * root_lower_denominator) *
               (input_lower * input_lower_denominator +
                 input_lower * input_lower_denominator)))
            (Num 0))
          (Num
            ((root_lower_denominator * root_lower_denominator) *
              (input_lower_denominator * input_lower_denominator) - 1)))` by
       (irule
          compute_registeredCase10173PositiveIntervalOrderTheory.registered_case10173_positive_q_mul_cv_equiv
        >> asm_rewrite_tac []
        >> simp [arithmeticTheory.MULT_POS])
  >> `bounded_case10173_q_cv_equiv
        (Pair
          (Pair (Num (certificate_twice_upper * input_twice_upper))
            (Num 0))
          (Num
            (certificate_twice_upper_denominator *
               input_twice_upper_denominator - 1)))
        (Pair
          (Pair
            (Num
              ((root_upper * root_upper_denominator +
                 root_upper * root_upper_denominator) *
               (input_upper * input_upper_denominator +
                 input_upper * input_upper_denominator)))
            (Num 0))
          (Num
            ((root_upper_denominator * root_upper_denominator) *
              (input_upper_denominator * input_upper_denominator) - 1)))` by
       (irule
          compute_registeredCase10173PositiveIntervalOrderTheory.registered_case10173_positive_q_mul_cv_equiv
        >> asm_rewrite_tac []
        >> simp [arithmeticTheory.MULT_POS])
  >> `bounded_case10173_q_cv_equiv
        (Pair (Pair (Num product_lower) (Num 0))
          (Num (product_lower_denominator - 1)))
        (Pair (Pair (Num (4 * root_lower * input_lower)) (Num 0))
          (Num
            (root_lower_denominator * input_lower_denominator - 1)))` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
        >> qexists_tac
             `Pair
                (Pair (Num (certificate_twice_lower * input_twice_lower))
                  (Num 0))
                (Num
                  (certificate_twice_lower_denominator *
                    input_twice_lower_denominator - 1))`
        >> conj_tac >- first_assum ACCEPT_TAC
        >> irule
             compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
        >> qexists_tac
             `Pair
                (Pair
                  (Num
                    ((root_lower * root_lower_denominator +
                       root_lower * root_lower_denominator) *
                     (input_lower * input_lower_denominator +
                       input_lower * input_lower_denominator)))
                  (Num 0))
                (Num
                  ((root_lower_denominator * root_lower_denominator) *
                    (input_lower_denominator * input_lower_denominator) - 1))`
        >> conj_tac >- first_assum ACCEPT_TAC
        >> irule
             compute_registeredCase10173SourceSecondDerivativeConversionEvalTheory.registered_case10173_q_twice_product_source_equiv
        >> asm_rewrite_tac [])
  >> `bounded_case10173_q_cv_equiv
        (Pair (Pair (Num product_upper) (Num 0))
          (Num (product_upper_denominator - 1)))
        (Pair (Pair (Num (4 * root_upper * input_upper)) (Num 0))
          (Num
            (root_upper_denominator * input_upper_denominator - 1)))` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
        >> qexists_tac
             `Pair
                (Pair (Num (certificate_twice_upper * input_twice_upper))
                  (Num 0))
                (Num
                  (certificate_twice_upper_denominator *
                    input_twice_upper_denominator - 1))`
        >> conj_tac >- first_assum ACCEPT_TAC
        >> irule
             compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
        >> qexists_tac
             `Pair
                (Pair
                  (Num
                    ((root_upper * root_upper_denominator +
                       root_upper * root_upper_denominator) *
                     (input_upper * input_upper_denominator +
                       input_upper * input_upper_denominator)))
                  (Num 0))
                (Num
                  ((root_upper_denominator * root_upper_denominator) *
                    (input_upper_denominator * input_upper_denominator) - 1))`
        >> conj_tac >- first_assum ACCEPT_TAC
        >> irule
             compute_registeredCase10173SourceSecondDerivativeConversionEvalTheory.registered_case10173_q_twice_product_source_equiv
        >> asm_rewrite_tac [])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_of_q»
            [from_cv
              (Pair
                (Pair (Pair (Num 0) (Num product_lower_denominator))
                  (Num (product_lower - 1)))
                (Pair (Pair (Num 0) (Num product_upper_denominator))
                  (Num (product_upper - 1))))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> simp [])
  >> irule
       compute_registeredCase10173SourceSecondDerivativeConversionEvalTheory.registered_case10173_source_sqrt_dd_conversion_eval
  >> conj_tac
  >- (qpat_assum `0 < product_lower` ACCEPT_TAC)
  >> conj_tac
  >- (qpat_assum `0 < product_lower_denominator` ACCEPT_TAC)
  >> conj_tac
  >- (qpat_assum `0 < product_upper` ACCEPT_TAC)
  >> conj_tac
  >- (qpat_assum `0 < product_upper_denominator` ACCEPT_TAC)
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexistsl_tac
       [`input_lower`, `input_lower_denominator`,
        `input_upper`, `input_upper_denominator`,
        `root_lower`, `root_lower_denominator`,
        `root_upper`, `root_upper_denominator`]
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
