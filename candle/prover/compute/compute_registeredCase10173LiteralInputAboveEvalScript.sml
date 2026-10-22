(*****************************************************************************
 * Uniform evaluator bounds for the two literal-source input conversions.
 *****************************************************************************)
Theory compute_registeredCase10173LiteralInputAboveEval
Ancestors
  compute_registeredCase10173ResultAddAboveEval
  compute_registeredCase10173QConversionEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fs_interval_list_of_q_object_eval_above:
  LENGTH intervals = 6 /\
  bounded_object_positive_q_interval64_decimal_list encoded = SOME intervals ==>
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_interval_list_of_q» [from_cv encoded])
    (bounded_interval64_object_cv_list intervals)
Proof
  strip_tac
  >> rw
       [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
  >> irule
       compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_interval_list_of_q_object_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_decimal_radii_numerators:
  registered_case10173_q_numerator_cv_list
    (MAP
      (\value.
        (bounded_word64_object_cv value,Num 999999999999))
      radii) =
  registered_case10173_word64_object_cv_list radii
Proof
  Induct_on `radii`
  >- (PURE_REWRITE_TAC
        [listTheory.MAP,
         compute_registeredCase10173RadiiEvalTheory.registered_case10173_q_numerator_cv_list_def,
         compute_registeredCase10173TaylorDotEvalTheory.registered_case10173_word64_object_cv_list_def]
      >> REFL_TAC)
  >> strip_tac
  >> PURE_REWRITE_TAC
       [listTheory.MAP,
        compute_registeredCase10173TaylorDotEvalTheory.registered_case10173_word64_object_cv_list_def]
  >> BETA_TAC
  >> PURE_REWRITE_TAC
       [compute_registeredCase10173RadiiEvalTheory.registered_case10173_q_numerator_cv_list_def]
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_decimal_radii_eval_above:
  LENGTH radii = 6 ==>
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_list_of_q»
      [from_cv
        (registered_case10173_q_cv_list
          (MAP
            (\value.
              (bounded_word64_object_cv value,Num 999999999999))
            radii))])
    (registered_case10173_word64_object_cv_list radii)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`items` |->
            `MAP
              (\value.
                (bounded_word64_object_cv value,Num 999999999999))
              radii`,
          `numeric_floor` |-> `8208`]
         compute_registeredCase10173ResultAddAboveEvalTheory.registered_case10173_fs_list_of_q_projection_eval_above)
  >> simp [registered_case10173_decimal_radii_numerators]
QED

val _ = export_theory ();
