(*****************************************************************************
 * Object-q witnesses for the generic scale-2^40 linear Taylor operations.
 *
 * The word checker stores fixed-point intervals, while the existing Candle
 * analytic contract consumes exact rational intervals encoded as [cv].  The
 * functions below construct exact, deliberately unnormalised rational
 * witnesses.  Their decoder theorems make representation independence
 * explicit: later normalization may change bytes, but not the rational value
 * enclosed by the word result.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectLinearRefinement
Ancestors
  compute_boundedAnalyticObjectRefinement compute_boundedQNormalizeRelation
Libs
  bossLib preamble intLib

Definition bounded_object_q_neg_cv_def:
  bounded_object_q_neg_cv
      (Pair (Pair (Num positive) (Num negative)) denominator) =
    Pair (Pair (Num negative) (Num positive)) denominator /\
  bounded_object_q_neg_cv _ = Num 0
End

Definition bounded_object_q_interval_neg_cv_def:
  bounded_object_q_interval_neg_cv (Pair lower upper) =
    Pair (bounded_object_q_neg_cv upper)
      (bounded_object_q_neg_cv lower) /\
  bounded_object_q_interval_neg_cv _ = Num 0
End

Definition bounded_object_q_add_cv_def:
  bounded_object_q_add_cv
      (Pair (Pair (Num left_positive) (Num left_negative))
        (Num left_denominator_minus_one))
      (Pair (Pair (Num right_positive) (Num right_negative))
        (Num right_denominator_minus_one)) =
    Pair
      (Pair
        (Num
          (left_positive * SUC right_denominator_minus_one +
           right_positive * SUC left_denominator_minus_one))
        (Num
          (left_negative * SUC right_denominator_minus_one +
           right_negative * SUC left_denominator_minus_one)))
      (Num
        (SUC left_denominator_minus_one *
           SUC right_denominator_minus_one - 1)) /\
  bounded_object_q_add_cv _ _ = Num 0
End

Definition bounded_object_q_interval_add_cv_def:
  bounded_object_q_interval_add_cv
      (Pair left_lower left_upper) (Pair right_lower right_upper) =
    Pair
      (bounded_object_q_add_cv left_lower right_lower)
      (bounded_object_q_add_cv left_upper right_upper) /\
  bounded_object_q_interval_add_cv _ _ = Num 0
End

Theorem bounded_object_q_ints_components:
  bounded_object_q_ints encoded = SOME (numerator,denominator) ==>
  ?positive negative denominator_minus_one.
    encoded =
      Pair (Pair (Num positive) (Num negative))
        (Num denominator_minus_one) /\
    numerator = (&positive:int) - &negative /\
    denominator = (&(SUC denominator_minus_one):int)
Proof
  qsuff_tac
    `!encoded numerator denominator.
       bounded_object_q_ints encoded = SOME (numerator,denominator) ==>
       ?positive negative denominator_minus_one.
         encoded =
           Pair (Pair (Num positive) (Num negative))
             (Num denominator_minus_one) /\
         numerator = (&positive:int) - &negative /\
         denominator = (&(SUC denominator_minus_one):int)`
  >- metis_tac []
  >> ho_match_mp_tac
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

Theorem bounded_object_q_neg_cv_decodes:
  bounded_object_q_ints source = SOME (numerator,denominator) ==>
  bounded_object_q_ints (bounded_object_q_neg_cv source) =
    SOME (-numerator,denominator)
Proof
  Cases_on `source`
  >> rw [bounded_object_q_neg_cv_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def]
  >> every_case_tac
  >> gvs [bounded_object_q_neg_cv_def,
          compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
          compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> gvs [bounded_object_q_neg_cv_def,
          compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
          compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> Cases_on `c'`
  >> Cases_on `c0'`
  >> gvs [bounded_object_q_neg_cv_def,
          compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
          compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_q_add_cv_decodes:
  bounded_object_q_ints left = SOME (left_numerator,left_denominator) /\
  bounded_object_q_ints right = SOME (right_numerator,right_denominator) ==>
  bounded_object_q_ints (bounded_object_q_add_cv left right) =
    SOME
      (left_numerator * right_denominator +
       right_numerator * left_denominator,
       left_denominator * right_denominator)
Proof
  strip_tac
  >> imp_res_tac bounded_object_q_ints_components
  >> gvs []
  >> `SUC
        (SUC denominator_minus_one' * SUC denominator_minus_one - 1) =
      SUC denominator_minus_one' * SUC denominator_minus_one` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred
        >> simp [])
  >> simp
       [bounded_object_q_add_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        integerTheory.INT_MUL]
  >> conj_tac
  >- (REWRITE_TAC
        [GSYM integerTheory.INT_ADD, GSYM integerTheory.INT_MUL]
      >> INT_RING_TAC)
  >> metis_tac [arithmeticTheory.MULT_COMM]
QED

Theorem bounded_object_q_interval_neg_cv_decodes:
  bounded_object_q_interval_ints source = SOME object_interval ==>
  bounded_object_q_interval_ints
      (bounded_object_q_interval_neg_cv source) =
    SOME (bounded_object_q_interval_neg_ints object_interval)
Proof
  Cases_on `source`
  >> rw [bounded_object_q_interval_neg_cv_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> every_case_tac
  >> gvs [bounded_object_q_interval_neg_cv_def,
          compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> PairCases_on `lower'`
  >> PairCases_on `upper'`
  >> imp_res_tac bounded_object_q_neg_cv_decodes
  >> gvs [bounded_object_q_interval_neg_ints_def]
QED

Theorem bounded_object_q_interval_add_cv_decodes:
  bounded_object_q_interval_ints left = SOME left_object_interval /\
  bounded_object_q_interval_ints right = SOME right_object_interval ==>
  bounded_object_q_interval_ints
      (bounded_object_q_interval_add_cv left right) =
    SOME
      (bounded_object_q_interval_add_ints
        left_object_interval right_object_interval)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw [bounded_object_q_interval_add_cv_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> every_case_tac
  >> gvs [bounded_object_q_interval_add_cv_def,
          compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> PairCases_on `lower'`
  >> PairCases_on `upper'`
  >> PairCases_on `lower''`
  >> PairCases_on `upper''`
  >> `bounded_object_q_ints (bounded_object_q_add_cv c c') =
        SOME
          (lower'0 * lower''1 + lower''0 * lower'1,
           lower'1 * lower''1)` by
       metis_tac [bounded_object_q_add_cv_decodes]
  >> `bounded_object_q_ints (bounded_object_q_add_cv c0 c0') =
        SOME
          (upper'0 * upper''1 + upper''0 * upper'1,
           upper'1 * upper''1)` by
       metis_tac [bounded_object_q_add_cv_decodes]
  >> gvs [bounded_object_q_interval_add_ints_def]
QED

Theorem bounded_interval64_neg_covers_object_q:
  bounded_interval64_covers_object_q source object_interval ==>
  bounded_interval64_covers_object_q
    (bounded_interval64_neg source)
    (bounded_object_q_interval_neg_cv object_interval)
Proof
  rw [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_q_interval_neg_cv_decodes
  >> gvs []
  >> metis_tac [bounded_interval64_neg_covers_object_q_ints]
QED

Theorem bounded_interval64_add_covers_object_q:
  bounded_interval64_covers_object_q left left_object_interval /\
  bounded_interval64_covers_object_q right right_object_interval /\
  bounded_interval64_add left right = SOME result ==>
  bounded_interval64_covers_object_q result
    (bounded_object_q_interval_add_cv
      left_object_interval right_object_interval)
Proof
  rw [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_q_interval_add_cv_decodes
  >> gvs []
  >> PairCases_on `x'`
  >> PairCases_on `x''`
  >> metis_tac [bounded_interval64_add_covers_object_q_ints]
QED

val _ = export_theory ();
