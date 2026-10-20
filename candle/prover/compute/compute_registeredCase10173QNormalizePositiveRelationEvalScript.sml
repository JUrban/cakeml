(*****************************************************************************
 * Positive-shape refinement for registered rational normalization.
 *
 * The evaluator theorem used by the nonlinear square-root path previously
 * exposed either the positive result shape or preservation of the represented
 * rational, but not both in one result.  This small bridge combines those two
 * independently proved views using determinism of [compute_eval].
 *****************************************************************************)
Theory compute_registeredCase10173QNormalizePositiveRelationEval
Ancestors
  compute_registeredCase10173QNormalizeRelationEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_q_normalize_positive_relation_eval:
  0 < positive /\ 0 < denominator /\ 140 < clock ==>
  ?normalized_positive normalized_denominator.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_normalize»
          [from_cv
            (Pair (Pair (Num positive) (Num 0))
              (Num (denominator - 1)))]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair
            (Pair (Num normalized_positive) (Num 0))
            (Num (normalized_denominator - 1)))),refs) /\
    0 < normalized_positive /\
    0 < normalized_denominator /\
    bounded_case10173_q_cv_equiv
      (Pair
        (Pair (Num normalized_positive) (Num 0))
        (Num (normalized_denominator - 1)))
      (Pair (Pair (Num positive) (Num 0))
        (Num (denominator - 1)))
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`positive` |-> `positive`,
          `denominator` |-> `denominator`,
          `clock` |-> `clock`,
          `refs` |-> `refs`]
         compute_registeredCase10173QNormalizeRelationEvalTheory.registered_case10173_q_normalize_positive_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`positive` |-> `positive`,
          `negative` |-> `0`,
          `denominator` |-> `denominator`,
          `clock` |-> `clock`,
          `refs` |-> `refs`]
         compute_registeredCase10173QNormalizeRelationEvalTheory.registered_case10173_q_normalize_relation_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> qpat_x_assum
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_normalize»
            [from_cv
              (Pair (Pair (Num positive) (Num 0))
                (Num (denominator - 1)))]) refs =
        (M_success (from_cv normalized),refs)`
       (fn relation_eval =>
         qpat_x_assum
           `compute_eval clock registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_q_normalize»
                [from_cv
                  (Pair (Pair (Num positive) (Num 0))
                    (Num (denominator - 1)))]) refs =
            (M_success
              (from_cv
                (Pair
                  (Pair (Num normalized_positive) (Num 0))
                  (Num (normalized_denominator - 1)))),refs)`
           (fn shape_eval =>
             assume_tac shape_eval
             >> mp_tac (TRANS (SYM relation_eval) shape_eval)))
  >> strip_tac
  >> fs [compute_execProofTheory.from_cv_11]
  >> qexists_tac `normalized_denominator`
  >> simp []
QED

val _ = export_theory ();
