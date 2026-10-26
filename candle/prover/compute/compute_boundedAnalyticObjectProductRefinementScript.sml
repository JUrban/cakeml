(*****************************************************************************
 * Exact object-q witnesses for the generic scale-2^40 interval product.
 *
 * Products deliberately remain unnormalised.  The endpoint selector compares
 * signed rationals by positive-denominator cross multiplication, matching the
 * four-corner interval product independently of any later GCD normalization.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectProductRefinement
Ancestors
  compute_boundedAnalyticObjectLinearRefinement
Libs
  bossLib preamble intLib

Definition bounded_object_q_mul_cv_def:
  bounded_object_q_mul_cv
      (Pair (Pair (Num left_positive) (Num left_negative))
        (Num left_denominator_minus_one))
      (Pair (Pair (Num right_positive) (Num right_negative))
        (Num right_denominator_minus_one)) =
    Pair
      (Pair
        (Num
          (left_positive * right_positive +
           left_negative * right_negative))
        (Num
          (left_positive * right_negative +
           left_negative * right_positive)))
      (Num
        (SUC left_denominator_minus_one *
           SUC right_denominator_minus_one - 1)) /\
  bounded_object_q_mul_cv _ _ = Num 0
End

Definition bounded_int_fraction_mul_def:
  bounded_int_fraction_mul
      ((left_numerator,left_denominator):int # int)
      ((right_numerator,right_denominator):int # int) =
    (left_numerator * right_numerator,
     left_denominator * right_denominator)
End

Definition bounded_int_fraction_le_def:
  bounded_int_fraction_le
      ((left_numerator,left_denominator):int # int)
      ((right_numerator,right_denominator):int # int) <=>
    left_numerator * right_denominator <=
      right_numerator * left_denominator
End

Definition bounded_int_fraction_min_def:
  bounded_int_fraction_min left right =
    if bounded_int_fraction_le left right then left else right
End

Definition bounded_int_fraction_max_def:
  bounded_int_fraction_max left right =
    if bounded_int_fraction_le left right then right else left
End

Definition bounded_int_fraction_min4_def:
  bounded_int_fraction_min4 first second third fourth =
    bounded_int_fraction_min
      (bounded_int_fraction_min first second)
      (bounded_int_fraction_min third fourth)
End

Definition bounded_int_fraction_max4_def:
  bounded_int_fraction_max4 first second third fourth =
    bounded_int_fraction_max
      (bounded_int_fraction_max first second)
      (bounded_int_fraction_max third fourth)
End

Definition bounded_object_q_le_cv_def:
  bounded_object_q_le_cv
      (Pair (Pair (Num left_positive) (Num left_negative))
        (Num left_denominator_minus_one))
      (Pair (Pair (Num right_positive) (Num right_negative))
        (Num right_denominator_minus_one)) =
    (left_positive * SUC right_denominator_minus_one +
        right_negative * SUC left_denominator_minus_one <=
      right_positive * SUC left_denominator_minus_one +
        left_negative * SUC right_denominator_minus_one) /\
  bounded_object_q_le_cv _ _ = F
End

Definition bounded_object_q_min_cv_def:
  bounded_object_q_min_cv left right =
    if bounded_object_q_le_cv left right then left else right
End

Definition bounded_object_q_max_cv_def:
  bounded_object_q_max_cv left right =
    if bounded_object_q_le_cv left right then right else left
End

Definition bounded_object_q_min4_cv_def:
  bounded_object_q_min4_cv first second third fourth =
    bounded_object_q_min_cv
      (bounded_object_q_min_cv first second)
      (bounded_object_q_min_cv third fourth)
End

Definition bounded_object_q_max4_cv_def:
  bounded_object_q_max4_cv first second third fourth =
    bounded_object_q_max_cv
      (bounded_object_q_max_cv first second)
      (bounded_object_q_max_cv third fourth)
End

Definition bounded_object_q_interval_mul_cv_def:
  bounded_object_q_interval_mul_cv
      (Pair left_lower left_upper) (Pair right_lower right_upper) =
    (let lower_lower = bounded_object_q_mul_cv left_lower right_lower;
        lower_upper = bounded_object_q_mul_cv left_lower right_upper;
        upper_lower = bounded_object_q_mul_cv left_upper right_lower;
        upper_upper = bounded_object_q_mul_cv left_upper right_upper
    in
      Pair
        (bounded_object_q_min4_cv
          lower_lower lower_upper upper_lower upper_upper)
        (bounded_object_q_max4_cv
          lower_lower lower_upper upper_lower upper_upper)) /\
  bounded_object_q_interval_mul_cv _ _ = Num 0
End

Definition bounded_object_q_interval_mul_ints_def:
  bounded_object_q_interval_mul_ints
      ((left_lower,left_upper):(int # int) # (int # int))
      ((right_lower,right_upper):(int # int) # (int # int)) =
    let lower_lower = bounded_int_fraction_mul left_lower right_lower;
        lower_upper = bounded_int_fraction_mul left_lower right_upper;
        upper_lower = bounded_int_fraction_mul left_upper right_lower;
        upper_upper = bounded_int_fraction_mul left_upper right_upper
    in
      (bounded_int_fraction_min4
        lower_lower lower_upper upper_lower upper_upper,
       bounded_int_fraction_max4
        lower_lower lower_upper upper_lower upper_upper)
End

Theorem bounded_object_q_mul_cv_decodes:
  bounded_object_q_ints left = SOME left_fraction /\
  bounded_object_q_ints right = SOME right_fraction ==>
  bounded_object_q_ints (bounded_object_q_mul_cv left right) =
    SOME (bounded_int_fraction_mul left_fraction right_fraction)
Proof
  PairCases_on `left_fraction`
  >> PairCases_on `right_fraction`
  >> strip_tac
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
  >> `SUC
        (SUC denominator_minus_one' * SUC denominator_minus_one - 1) =
      SUC denominator_minus_one' * SUC denominator_minus_one` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred
        >> simp [])
  >> simp
       [bounded_object_q_mul_cv_def, bounded_int_fraction_mul_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        integerTheory.INT_MUL]
  >> conj_tac
  >- (REWRITE_TAC
        [GSYM integerTheory.INT_ADD, GSYM integerTheory.INT_MUL]
      >> INT_RING_TAC)
  >> metis_tac [arithmeticTheory.MULT_COMM]
QED

Theorem bounded_object_q_le_cv_correct:
  bounded_object_q_ints left = SOME left_fraction /\
  bounded_object_q_ints right = SOME right_fraction ==>
  (bounded_object_q_le_cv left right <=>
   bounded_int_fraction_le left_fraction right_fraction)
Proof
  PairCases_on `left_fraction`
  >> PairCases_on `right_fraction`
  >> strip_tac
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
  >> simp
       [bounded_object_q_le_cv_def, bounded_int_fraction_le_def,
        GSYM integerTheory.INT_ADD, GSYM integerTheory.INT_MUL]
  >> REWRITE_TAC
       [GSYM integerTheory.INT_LE, GSYM integerTheory.INT_ADD,
        GSYM integerTheory.INT_MUL]
  >> simp [integerTheory.INT_SUB_RDISTRIB]
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_q_min_cv_decodes:
  bounded_object_q_ints left = SOME left_fraction /\
  bounded_object_q_ints right = SOME right_fraction ==>
  bounded_object_q_ints (bounded_object_q_min_cv left right) =
    SOME (bounded_int_fraction_min left_fraction right_fraction)
Proof
  strip_tac
  >> imp_res_tac bounded_object_q_le_cv_correct
  >> rw [bounded_object_q_min_cv_def, bounded_int_fraction_min_def]
QED

Theorem bounded_object_q_max_cv_decodes:
  bounded_object_q_ints left = SOME left_fraction /\
  bounded_object_q_ints right = SOME right_fraction ==>
  bounded_object_q_ints (bounded_object_q_max_cv left right) =
    SOME (bounded_int_fraction_max left_fraction right_fraction)
Proof
  strip_tac
  >> imp_res_tac bounded_object_q_le_cv_correct
  >> rw [bounded_object_q_max_cv_def, bounded_int_fraction_max_def]
QED

Theorem bounded_object_q_min4_cv_decodes:
  bounded_object_q_ints q1 = SOME fraction1 /\
  bounded_object_q_ints q2 = SOME fraction2 /\
  bounded_object_q_ints q3 = SOME fraction3 /\
  bounded_object_q_ints q4 = SOME fraction4 ==>
  bounded_object_q_ints
      (bounded_object_q_min4_cv q1 q2 q3 q4) =
    SOME
      (bounded_int_fraction_min4 fraction1 fraction2 fraction3 fraction4)
Proof
  strip_tac
  >> `bounded_object_q_ints (bounded_object_q_min_cv q1 q2) =
        SOME (bounded_int_fraction_min fraction1 fraction2)` by
       (irule bounded_object_q_min_cv_decodes >> simp [])
  >> `bounded_object_q_ints (bounded_object_q_min_cv q3 q4) =
        SOME (bounded_int_fraction_min fraction3 fraction4)` by
       (irule bounded_object_q_min_cv_decodes >> simp [])
  >> fs [bounded_object_q_min4_cv_def, bounded_int_fraction_min4_def]
  >> irule bounded_object_q_min_cv_decodes
  >> simp []
QED

Theorem bounded_object_q_max4_cv_decodes:
  bounded_object_q_ints q1 = SOME fraction1 /\
  bounded_object_q_ints q2 = SOME fraction2 /\
  bounded_object_q_ints q3 = SOME fraction3 /\
  bounded_object_q_ints q4 = SOME fraction4 ==>
  bounded_object_q_ints
      (bounded_object_q_max4_cv q1 q2 q3 q4) =
    SOME
      (bounded_int_fraction_max4 fraction1 fraction2 fraction3 fraction4)
Proof
  strip_tac
  >> `bounded_object_q_ints (bounded_object_q_max_cv q1 q2) =
        SOME (bounded_int_fraction_max fraction1 fraction2)` by
       (irule bounded_object_q_max_cv_decodes >> simp [])
  >> `bounded_object_q_ints (bounded_object_q_max_cv q3 q4) =
        SOME (bounded_int_fraction_max fraction3 fraction4)` by
       (irule bounded_object_q_max_cv_decodes >> simp [])
  >> fs [bounded_object_q_max4_cv_def, bounded_int_fraction_max4_def]
  >> irule bounded_object_q_max_cv_decodes
  >> simp []
QED

Theorem bounded_object_q_interval_mul_cv_decodes:
  bounded_object_q_interval_ints left = SOME left_object_interval /\
  bounded_object_q_interval_ints right = SOME right_object_interval ==>
  bounded_object_q_interval_ints
      (bounded_object_q_interval_mul_cv left right) =
    SOME
      (bounded_object_q_interval_mul_ints
        left_object_interval right_object_interval)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw
       [bounded_object_q_interval_mul_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> every_case_tac
  >> gvs
       [bounded_object_q_interval_mul_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> `bounded_object_q_ints (bounded_object_q_mul_cv c c') =
        SOME (bounded_int_fraction_mul lower' lower'')` by
       (irule bounded_object_q_mul_cv_decodes >> simp [])
  >> `bounded_object_q_ints (bounded_object_q_mul_cv c c0') =
        SOME (bounded_int_fraction_mul lower' upper'')` by
       (irule bounded_object_q_mul_cv_decodes >> simp [])
  >> `bounded_object_q_ints (bounded_object_q_mul_cv c0 c') =
        SOME (bounded_int_fraction_mul upper' lower'')` by
       (irule bounded_object_q_mul_cv_decodes >> simp [])
  >> `bounded_object_q_ints (bounded_object_q_mul_cv c0 c0') =
        SOME (bounded_int_fraction_mul upper' upper'')` by
       (irule bounded_object_q_mul_cv_decodes >> simp [])
  >> `bounded_object_q_ints
        (bounded_object_q_min4_cv
          (bounded_object_q_mul_cv c c')
          (bounded_object_q_mul_cv c c0')
          (bounded_object_q_mul_cv c0 c')
          (bounded_object_q_mul_cv c0 c0')) =
        SOME
          (bounded_int_fraction_min4
            (bounded_int_fraction_mul lower' lower'')
            (bounded_int_fraction_mul lower' upper'')
            (bounded_int_fraction_mul upper' lower'')
            (bounded_int_fraction_mul upper' upper''))` by
       (irule bounded_object_q_min4_cv_decodes >> simp [])
  >> `bounded_object_q_ints
        (bounded_object_q_max4_cv
          (bounded_object_q_mul_cv c c')
          (bounded_object_q_mul_cv c c0')
          (bounded_object_q_mul_cv c0 c')
          (bounded_object_q_mul_cv c0 c0')) =
        SOME
          (bounded_int_fraction_max4
            (bounded_int_fraction_mul lower' lower'')
            (bounded_int_fraction_mul lower' upper'')
            (bounded_int_fraction_mul upper' lower'')
            (bounded_int_fraction_mul upper' upper''))` by
       (irule bounded_object_q_max4_cv_decodes >> simp [])
  >> gvs [bounded_object_q_interval_mul_ints_def]
QED

val _ = export_theory ();
