(*****************************************************************************
 * Source-box validity for the certified NL finish.
 *
 * The authenticated fixed packet already proves enclosure of the original
 * rational box.  That relation includes exact endpoint ordering.  This file
 * turns the ordering fact into the registered q_box_valid_list result instead
 * of re-evaluating a copied fixture.
 *****************************************************************************)
Theory compute_registeredCase10173BoxValidityEval
Ancestors
  compute_registeredCase10173FixedCertifiedFinishEval
Libs
  bossLib preamble intLib

Definition registered_case10173_q_box_valid_list_body_def:
  registered_case10173_q_box_valid_list_body =
    If (Uop Ispair (Var «boxes»))
      (If
        (App «candle_cv_q_le»
          [Uop Fst (Uop Fst (Var «boxes»));
           Uop Snd (Uop Fst (Var «boxes»))])
        (App «candle_cv_q_box_valid_list» [Uop Snd (Var «boxes»)])
        (Num 0))
      (Num 1)
End

Theorem registered_case10173_q_box_valid_list_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_box_valid_list» =
    SOME ([«boxes»],registered_case10173_q_box_valid_list_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_box_valid_list_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_box_valid_list» [from_cv boxes])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«boxes»,from_cv boxes)]
        registered_case10173_q_box_valid_list_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_q_box_valid_list_lookup]
QED

Theorem registered_case10173_q_le_signed_true_eval:
  left_positive * (right_denominator_minus_one + 1) +
      right_negative * (left_denominator_minus_one + 1) <=
    right_positive * (left_denominator_minus_one + 1) +
      left_negative * (right_denominator_minus_one + 1) /\
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_le»
        [from_cv
          (Pair (Pair (Num left_positive) (Num left_negative))
            (Num left_denominator_minus_one));
         from_cv
          (Pair (Pair (Num right_positive) (Num right_negative))
            (Num right_denominator_minus_one))])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173SqrtCertificateEvalTheory.registered_case10173_q_le_lookup,
        compute_registeredCase10173SqrtCertificateEvalTheory.registered_case10173_q_le_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_bounded_object_q_ints_components:
  !encoded numerator denominator.
    bounded_object_q_ints encoded = SOME (numerator,denominator) ==>
    ?positive negative denominator_minus_one.
      encoded =
        Pair (Pair (Num positive) (Num negative))
          (Num denominator_minus_one) /\
      numerator = (&positive:int) - &negative /\
      denominator = (&(SUC denominator_minus_one):int)
Proof
  ho_match_mp_tac
    compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_ind
  >> rw
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def]
  >> every_case_tac
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> Cases_on `signed`
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> every_case_tac
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> Cases_on `c`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> Cases_on `c0`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
QED

Theorem registered_case10173_int_move_sub_le:
  !a b c d:int. a - b <= c - d ==> a + d <= c + b
Proof
  intLib.ARITH_TAC
QED

Theorem registered_case10173_q_interval_order_components:
  !interval object_interval.
    bounded_object_q_interval_ints interval = SOME object_interval /\
    (FST (FST object_interval)) * (SND (SND object_interval)) <=
      (FST (SND object_interval)) * (SND (FST object_interval)) ==>
    ?left_positive left_negative left_denominator_minus_one
     right_positive right_negative right_denominator_minus_one.
      interval =
        Pair
          (Pair (Pair (Num left_positive) (Num left_negative))
            (Num left_denominator_minus_one))
          (Pair (Pair (Num right_positive) (Num right_negative))
            (Num right_denominator_minus_one)) /\
      left_positive * (right_denominator_minus_one + 1) +
          right_negative * (left_denominator_minus_one + 1) <=
        right_positive * (left_denominator_minus_one + 1) +
          left_negative * (right_denominator_minus_one + 1)
Proof
  ho_match_mp_tac
    compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_ind
  >> rw
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> every_case_tac
  >> gvs []
  >> Cases_on `lower'`
  >> Cases_on `upper'`
  >> imp_res_tac registered_case10173_bounded_object_q_ints_components
  >> gvs []
  >> fs
       [integerTheory.INT_SUB_RDISTRIB,
        integerTheory.INT_OF_NUM_MUL]
  >> imp_res_tac registered_case10173_int_move_sub_le
  >> fs
       [integerTheory.INT_OF_NUM_ADD,
        integerTheory.INT_OF_NUM_LE,
        arithmeticTheory.ADD1]
QED

Theorem registered_case10173_compute_eval_if_true_result:
  compute_eval clock ceqs condition (refs:hol_refs) =
      (M_success (Num 1),refs) /\
  compute_eval clock ceqs yes_branch refs = result ==>
  compute_eval clock ceqs (If condition yes_branch no_branch) refs = result
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac `compute_eval clock ceqs yes_branch refs`
  >> conj_tac
  >- (irule
        (Q.INST [`n` |-> `0`]
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success)
      >> asm_rewrite_tac []
      >> simp [])
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_q_box_head_order_true_eval:
  bounded_object_q_interval_ints interval = SOME object_interval /\
  (FST (FST object_interval)) * (SND (SND object_interval)) <=
    (FST (SND object_interval)) * (SND (FST object_interval)) /\
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_le»
        [Uop Fst
          (Uop Fst (Pair (from_cv interval) (from_cv boxes)));
         Uop Snd
          (Uop Fst (Pair (from_cv interval) (from_cv boxes)))])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> imp_res_tac registered_case10173_q_interval_order_components
  >> gvs []
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_le»
            [from_cv
              (Pair (Pair (Num left_positive) (Num left_negative))
                (Num left_denominator_minus_one));
             from_cv
              (Pair (Pair (Num right_positive) (Num right_negative))
                (Num right_denominator_minus_one))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule
            compute_registeredCase10173HistoricalAtanPointEvalTheory.registered_case10173_compute_eval_uop_fst_argument_result
          >> qexists_tac
               `(Pair
                   (Pair (Num right_positive) (Num right_negative))
                   (Num right_denominator_minus_one):cv)`
          >> irule
               compute_registeredCase10173HistoricalAtanPointEvalTheory.registered_case10173_compute_eval_uop_fst_argument_result
          >> qexists_tac `boxes`
          >> simp
               [compute_evalTheory.compute_eval_def,
                compute_execProofTheory.compute_eval_from_cv,
                compute_execTheory.from_cv_def,
                ml_monadBaseTheory.st_ex_bind_def,
                ml_monadBaseTheory.st_ex_return_def])
      >> irule
           compute_registeredCase10173HistoricalAtanPointEvalTheory.registered_case10173_compute_eval_uop_snd_argument_result
      >> qexists_tac
           `(Pair
               (Pair (Num left_positive) (Num left_negative))
               (Num left_denominator_minus_one):cv)`
      >> irule
           compute_registeredCase10173HistoricalAtanPointEvalTheory.registered_case10173_compute_eval_uop_fst_argument_result
      >> qexists_tac `boxes`
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_execTheory.from_cv_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> irule registered_case10173_q_le_signed_true_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> metis_tac [arithmeticTheory.ADD_COMM]
QED

Theorem registered_case10173_q_box_valid_list_ordered_eval:
  !boxes object_intervals clock refs.
    bounded_object_q_interval_list boxes = SOME object_intervals /\
    EVERY
      (\object_interval.
        (FST (FST object_interval)) * (SND (SND object_interval)) <=
        (FST (SND object_interval)) * (SND (FST object_interval)))
      object_intervals /\
    LENGTH object_intervals + 4 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_box_valid_list» [from_cv boxes])
        (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  ho_match_mp_tac
    compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_list_ind
  >> rw
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_list_def]
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (subst [(«boxes»,Num 0)]
                registered_case10173_q_box_valid_list_body) refs`
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST [`boxes` |-> `(Num 0:cv)`]
                registered_case10173_q_box_valid_list_unfold))
          >> intLib.ARITH_TAC)
      >> simp
           [registered_case10173_q_box_valid_list_body_def,
            compute_evalTheory.subst_def,
            compute_execTheory.from_cv_def,
            Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >- (every_case_tac
      >> gvs
           [compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
            compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def]
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (subst
                [(«boxes»,Pair (from_cv interval) (from_cv boxes))]
                registered_case10173_q_box_valid_list_body) refs`
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST [`boxes` |-> `(Pair interval boxes:cv)`]
                registered_case10173_q_box_valid_list_unfold))
          >> intLib.ARITH_TAC)
      >> simp
           [registered_case10173_q_box_valid_list_body_def,
            compute_evalTheory.subst_def,
            compute_execTheory.from_cv_def]
      >> rw
           [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`argument` |-> `(Pair interval boxes:cv)`]
               compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
      >> irule registered_case10173_compute_eval_if_true_result
      >> conj_tac
      >- (irule registered_case10173_q_box_head_order_true_eval
          >> conj_tac >- intLib.ARITH_TAC
          >> qexists_tac `interval'`
          >> asm_rewrite_tac [])
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_q_box_valid_list» [from_cv boxes]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
          >> simp
               [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components]
          >> intLib.ARITH_TAC)
      >> qpat_x_assum `!clock' refs'. _`
           (qspecl_then [`clock - 1`,`refs`] mp_tac)
      >> impl_tac >- intLib.ARITH_TAC
      >> simp [])
  >> gvs []
QED

Theorem registered_case10173_list_rel_covers_q_ordered:
  !intervals object_intervals.
    LIST_REL bounded_interval64_covers_object_q_ints
      intervals object_intervals ==>
    EVERY
      (\object_interval.
        (FST (FST object_interval)) * (SND (SND object_interval)) <=
        (FST (SND object_interval)) * (SND (FST object_interval)))
      object_intervals
Proof
  Induct_on `intervals`
  >> Cases_on `object_intervals`
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def]
  >> Cases_on `h`
  >> Cases_on `r`
  >> Cases_on `q`
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def]
QED

Theorem registered_case10173_q_box_valid_list_from_coverage_eval:
  bounded_interval64_list_covers_object_q intervals boxes /\
  LENGTH intervals + 4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_box_valid_list» [from_cv boxes])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  rw
    [compute_boundedObjectIntervalRelationTheory.bounded_interval64_list_covers_object_q_def]
  >> Cases_on `bounded_object_q_interval_list boxes`
  >> fs []
  >> irule registered_case10173_q_box_valid_list_ordered_eval
  >> qexists_tac `x`
  >> simp []
  >> conj_tac
  >- (imp_res_tac LIST_REL_LENGTH
      >> intLib.ARITH_TAC)
  >> irule registered_case10173_list_rel_covers_q_ordered
  >> qexists_tac `intervals`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
