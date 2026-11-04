(*****************************************************************************
 * Representation invariance for exact object-q unary certificates.
 *
 * The genuine nonlinear payload can represent one rational endpoint by
 * different integer numerator/denominator pairs at different semantic and
 * runtime boundaries.  These lemmas show that the exact sqrt and positive
 * reciprocal certificate contracts depend on the represented rationals, not
 * on a particular encoding.
 *****************************************************************************)
Theory compute_boundedObjectExactCertificateEquivalence
Ancestors
  compute_boundedCase16594ObjectRuntimePreservation
  compute_boundedAnalyticObjectReciprocalRefinement
  compute_boundedCase16594ObjectVariableEval
Libs
  bossLib preamble intLib

Theorem bounded_object_q_equiv_nonnegative_left:
  !left_numerator left_denominator right_numerator right_denominator:int.
    0 < left_denominator /\
    0 < right_denominator /\
    left_numerator * right_denominator =
      right_numerator * left_denominator /\
    0 <= right_numerator ==>
    0 <= left_numerator
Proof
  rpt strip_tac
  >> `0 <= left_denominator` by intLib.ARITH_TAC
  >> `0 <= right_numerator * left_denominator` by
       (irule integerTheory.INT_LE_MUL >> asm_rewrite_tac [])
  >> `0 <= left_numerator * right_denominator` by asm_rewrite_tac []
  >> `right_denominator * left_numerator =
      left_numerator * right_denominator` by INT_RING_TAC
  >> `0 <= right_denominator * left_numerator` by asm_rewrite_tac []
  >> match_mp_tac
       (Q.INST
         [`multiplier` |-> `right_denominator`,
          `left` |-> `0:int`,
          `right` |-> `left_numerator`]
         compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_int_le_cancel_positive_left)
  >> asm_rewrite_tac [integerTheory.INT_MUL_RZERO]
QED

Theorem bounded_object_q_equiv_positive_left:
  !left_numerator left_denominator right_numerator right_denominator:int.
    0 < left_denominator /\
    0 < right_denominator /\
    left_numerator * right_denominator =
      right_numerator * left_denominator /\
    0 < right_numerator ==>
    0 < left_numerator
Proof
  rpt strip_tac
  >> `0 < right_numerator * left_denominator` by
       (irule (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
        >> asm_rewrite_tac [])
  >> `0 < left_numerator * right_denominator` by asm_rewrite_tac []
  >> `right_denominator * left_numerator =
      left_numerator * right_denominator` by INT_RING_TAC
  >> `0 < right_denominator * left_numerator` by asm_rewrite_tac []
  >> match_mp_tac
       (Q.INST
         [`multiplier` |-> `right_denominator`,
          `value` |-> `left_numerator`]
         compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_int_positive_from_positive_left_product)
  >> asm_rewrite_tac []
QED

Theorem bounded_object_q_sqrt_certificate_exact_equiv_input:
  !left right output.
    bounded_object_q_interval_cv_equiv left right /\
    bounded_object_q_sqrt_certificate_exact right output ==>
    bounded_object_q_sqrt_certificate_exact left output
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `output`
  >> simp
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_def]
  >> strip_tac
  >> imp_res_tac
       compute_boundedQFoldRelationTheory.bounded_object_q_cv_equiv_decodes
  >> fs
       [compute_boundedAnalyticObjectSqrtRefinementTheory.bounded_object_q_sqrt_certificate_exact_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> rpt (CASE_TAC >> fs [])
  >> rpt conj_tac
  >- metis_tac
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
  >- metis_tac
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
  >- (match_mp_tac
        (Q.SPECL
          [`left_numerator'`,`left_denominator'`,
           `right_numerator'`,`right_denominator'`]
          bounded_object_q_equiv_nonnegative_left)
      >> rpt conj_tac
      >- metis_tac
           [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
      >> asm_rewrite_tac [])
  >- (`bounded_object_q_le_cv c c0 =
        bounded_object_q_le_cv c' c0'` by
         (irule
            compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_le_cv_equiv_cong
          >> asm_rewrite_tac [])
      >> `bounded_object_q_le_cv c' c0'` by
         (mp_tac
            (Q.INST
              [`left` |-> `c'`, `right` |-> `c0'`,
               `left_fraction` |->
                 `(right_numerator',right_denominator')`,
               `right_fraction` |->
                 `(right_numerator,right_denominator)`]
              compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct)
          >> impl_tac >- asm_rewrite_tac []
          >> simp
               [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def])
      >> `bounded_object_q_le_cv c c0` by asm_rewrite_tac []
      >> mp_tac
           (Q.INST
             [`left` |-> `c`, `right` |-> `c0`,
              `left_fraction` |->
                `(left_numerator',left_denominator')`,
              `right_fraction` |->
                `(left_numerator,left_denominator)`]
             compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct)
      >> impl_tac >- asm_rewrite_tac []
      >> simp
           [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def])
  >- (mp_tac
        (Q.INST
          [`value` |-> `c''`, `decoded` |-> `(q'',r)`]
          compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_refl)
      >> impl_tac >- asm_rewrite_tac []
      >> strip_tac
      >> `bounded_case10173_q_cv_equiv
            (bounded_object_q_mul_cv c'' c'')
            (bounded_object_q_mul_cv c'' c'')` by
         (irule
            compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_equiv_cong
          >> asm_rewrite_tac [])
      >> `bounded_object_q_ints (bounded_object_q_mul_cv c'' c'') =
            SOME (q'' * q'',r * r)` by
         (mp_tac
            (Q.INST
              [`left` |-> `c''`, `right` |-> `c''`,
               `left_fraction` |-> `(q'',r)`,
               `right_fraction` |-> `(q'',r)`]
              compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes)
          >> impl_tac >- asm_rewrite_tac []
          >> simp
               [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def])
      >> `right_numerator' * (r * r) =
          right_numerator' * r * r` by INT_RING_TAC
      >> `bounded_object_q_le_cv
            (bounded_object_q_mul_cv c'' c'') c'` by
         (mp_tac
            (Q.INST
              [`left` |-> `bounded_object_q_mul_cv c'' c''`,
               `right` |-> `c'`,
               `left_fraction` |-> `(q'' * q'',r * r)`,
               `right_fraction` |->
                 `(right_numerator',right_denominator')`]
              compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct)
          >> impl_tac >- asm_rewrite_tac []
          >> simp
               [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
          >> asm_rewrite_tac [])
      >> `bounded_object_q_le_cv
            (bounded_object_q_mul_cv c'' c'') c` by
         (mp_tac
            (Q.INST
              [`left` |-> `bounded_object_q_mul_cv c'' c''`,
               `left'` |-> `bounded_object_q_mul_cv c'' c''`,
               `right` |-> `c`, `right'` |-> `c'`]
              compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_le_cv_equiv_cong)
          >> impl_tac >- asm_rewrite_tac []
          >> asm_rewrite_tac [])
      >> `left_numerator' * (r * r) =
          left_numerator' * r * r` by INT_RING_TAC
      >> mp_tac
           (Q.INST
             [`left` |-> `bounded_object_q_mul_cv c'' c''`,
              `right` |-> `c`,
              `left_fraction` |-> `(q'' * q'',r * r)`,
              `right_fraction` |->
                `(left_numerator',left_denominator')`]
             compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct)
      >> impl_tac >- asm_rewrite_tac []
      >> simp
           [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
      >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`value` |-> `c0''`, `decoded` |-> `(q',r')`]
         compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_refl)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_mul_cv c0'' c0'')
        (bounded_object_q_mul_cv c0'' c0'')` by
     (irule
        compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_equiv_cong
      >> asm_rewrite_tac [])
  >> `bounded_object_q_ints (bounded_object_q_mul_cv c0'' c0'') =
        SOME (q' * q',r' * r')` by
     (mp_tac
        (Q.INST
          [`left` |-> `c0''`, `right` |-> `c0''`,
           `left_fraction` |-> `(q',r')`,
           `right_fraction` |-> `(q',r')`]
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes)
      >> impl_tac >- asm_rewrite_tac []
      >> simp
           [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def])
  >> mp_tac
       (Q.INST
         [`left` |-> `c0'`,
          `right` |-> `bounded_object_q_mul_cv c0'' c0''`,
          `left_fraction` |-> `(right_numerator,right_denominator)`,
          `right_fraction` |-> `(q' * q',r' * r')`]
         compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct)
  >> impl_tac >- asm_rewrite_tac []
  >> simp
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
  >> strip_tac
  >> `right_numerator * (r' * r') =
      right_numerator * r' * r'` by INT_RING_TAC
  >> `right_numerator * (r' * r') <=
      q' * q' * right_denominator` by
     (qpat_x_assum `right_numerator * r' * r' <= _` mp_tac
      >> asm_rewrite_tac [])
  >> `bounded_object_q_le_cv c0'
        (bounded_object_q_mul_cv c0'' c0'')` by fs []
  >> `bounded_object_q_le_cv c0
        (bounded_object_q_mul_cv c0'' c0'')` by
     (mp_tac
        (Q.INST
          [`left` |-> `c0`, `left'` |-> `c0'`,
           `right` |-> `bounded_object_q_mul_cv c0'' c0''`,
           `right'` |-> `bounded_object_q_mul_cv c0'' c0''`]
          compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_le_cv_equiv_cong)
      >> impl_tac >- asm_rewrite_tac []
      >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`left` |-> `c0`,
          `right` |-> `bounded_object_q_mul_cv c0'' c0''`,
          `left_fraction` |-> `(left_numerator,left_denominator)`,
          `right_fraction` |-> `(q' * q',r' * r')`]
         compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct)
  >> impl_tac >- asm_rewrite_tac []
  >> simp
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
  >> strip_tac
  >> `left_numerator * (r' * r') =
      left_numerator * r' * r'` by INT_RING_TAC
  >> qpat_x_assum `left_numerator * (r' * r') <= _` mp_tac
  >> asm_rewrite_tac []
QED

Theorem bounded_object_q_positive_inv_certificate_exact_equiv_input:
  !left right output.
    bounded_object_q_interval_cv_equiv left right /\
    bounded_object_q_positive_inv_certificate_exact right output ==>
    bounded_object_q_positive_inv_certificate_exact left output
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `output`
  >> simp
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_def]
  >> strip_tac
  >> imp_res_tac
       compute_boundedQFoldRelationTheory.bounded_object_q_cv_equiv_decodes
  >> fs
       [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_object_q_positive_inv_certificate_exact_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> rpt (CASE_TAC >> fs [])
  >> rpt conj_tac
  >- metis_tac
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
  >- metis_tac
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
  >- (match_mp_tac
        (Q.SPECL
          [`left_numerator'`,`left_denominator'`,
           `right_numerator'`,`right_denominator'`]
          bounded_object_q_equiv_positive_left)
      >> rpt conj_tac
      >- metis_tac
           [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
      >> asm_rewrite_tac [])
  >- (match_mp_tac
        (Q.SPECL
          [`left_numerator`,`left_denominator`,
           `right_numerator`,`right_denominator`]
          bounded_object_q_equiv_positive_left)
      >> rpt conj_tac
      >- metis_tac
           [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
      >> asm_rewrite_tac [])
  >- (`bounded_object_q_le_cv c c0 =
        bounded_object_q_le_cv c' c0'` by
         (irule
            compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_le_cv_equiv_cong
          >> asm_rewrite_tac [])
      >> `bounded_object_q_le_cv c' c0'` by
         (mp_tac
            (Q.INST
              [`left` |-> `c'`, `right` |-> `c0'`,
               `left_fraction` |->
                 `(right_numerator',right_denominator')`,
               `right_fraction` |->
                 `(right_numerator,right_denominator)`]
              compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct)
          >> impl_tac >- asm_rewrite_tac []
          >> simp
               [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def])
      >> `bounded_object_q_le_cv c c0` by asm_rewrite_tac []
      >> mp_tac
           (Q.INST
             [`left` |-> `c`, `right` |-> `c0`,
              `left_fraction` |->
                `(left_numerator',left_denominator')`,
              `right_fraction` |->
                `(left_numerator,left_denominator)`]
             compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct)
      >> impl_tac >- asm_rewrite_tac []
      >> simp
           [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def])
  >- (mp_tac
        (Q.INST
          [`value` |-> `c''`, `decoded` |-> `(q'',r)`]
          compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_refl)
      >> impl_tac >- asm_rewrite_tac []
      >> strip_tac
      >> `bounded_case10173_q_cv_equiv
            (bounded_object_q_mul_cv c'' c0)
            (bounded_object_q_mul_cv c'' c0')` by
         (irule
            compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_equiv_cong
          >> asm_rewrite_tac [])
      >> `bounded_object_q_ints bounded_case16594_object_one_cv =
            SOME (1,1)` by EVAL_TAC
      >> mp_tac
           (Q.INST
             [`value` |-> `bounded_case16594_object_one_cv`,
              `decoded` |-> `(1,1)`]
             compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_refl)
      >> impl_tac >- asm_rewrite_tac []
      >> strip_tac
      >> `bounded_object_q_ints (bounded_object_q_mul_cv c'' c0') =
            SOME (q'' * right_numerator,r * right_denominator)` by
         (mp_tac
            (Q.INST
              [`left` |-> `c''`, `right` |-> `c0'`,
               `left_fraction` |-> `(q'',r)`,
               `right_fraction` |->
                 `(right_numerator,right_denominator)`]
              compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes)
          >> impl_tac >- asm_rewrite_tac []
          >> simp
               [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def])
      >> `r * right_denominator =
          right_denominator * r` by INT_RING_TAC
      >> `bounded_object_q_le_cv
            (bounded_object_q_mul_cv c'' c0')
            bounded_case16594_object_one_cv` by
         (mp_tac
            (Q.INST
              [`left` |-> `bounded_object_q_mul_cv c'' c0'`,
               `right` |-> `bounded_case16594_object_one_cv`,
               `left_fraction` |->
                 `(q'' * right_numerator,r * right_denominator)`,
               `right_fraction` |-> `(1,1)`]
              compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct)
          >> impl_tac >- asm_rewrite_tac []
          >> simp
               [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
          >> asm_rewrite_tac [])
      >> `bounded_object_q_le_cv
            (bounded_object_q_mul_cv c'' c0)
            bounded_case16594_object_one_cv` by
         (mp_tac
            (Q.INST
              [`left` |-> `bounded_object_q_mul_cv c'' c0`,
               `left'` |-> `bounded_object_q_mul_cv c'' c0'`,
               `right` |-> `bounded_case16594_object_one_cv`,
               `right'` |-> `bounded_case16594_object_one_cv`]
              compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_le_cv_equiv_cong)
          >> impl_tac >- asm_rewrite_tac []
          >> asm_rewrite_tac [])
      >> `bounded_object_q_ints (bounded_object_q_mul_cv c'' c0) =
            SOME (q'' * left_numerator,r * left_denominator)` by
         (mp_tac
            (Q.INST
              [`left` |-> `c''`, `right` |-> `c0`,
               `left_fraction` |-> `(q'',r)`,
               `right_fraction` |->
                 `(left_numerator,left_denominator)`]
              compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes)
          >> impl_tac >- asm_rewrite_tac []
          >> simp
               [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def])
      >> `r * left_denominator =
          left_denominator * r` by INT_RING_TAC
      >> mp_tac
           (Q.INST
             [`left` |-> `bounded_object_q_mul_cv c'' c0`,
              `right` |-> `bounded_case16594_object_one_cv`,
              `left_fraction` |->
                `(q'' * left_numerator,r * left_denominator)`,
              `right_fraction` |-> `(1,1)`]
             compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct)
      >> impl_tac >- asm_rewrite_tac []
      >> simp
           [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
      >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`value` |-> `c0''`, `decoded` |-> `(q',r')`]
         compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_refl)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_mul_cv c0'' c)
        (bounded_object_q_mul_cv c0'' c')` by
     (irule
        compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_equiv_cong
      >> asm_rewrite_tac [])
  >> `bounded_object_q_ints bounded_case16594_object_one_cv =
        SOME (1,1)` by EVAL_TAC
  >> mp_tac
       (Q.INST
         [`value` |-> `bounded_case16594_object_one_cv`,
          `decoded` |-> `(1,1)`]
         compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_refl)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> `bounded_object_q_ints (bounded_object_q_mul_cv c0'' c') =
        SOME (q' * right_numerator',r' * right_denominator')` by
     (mp_tac
        (Q.INST
          [`left` |-> `c0''`, `right` |-> `c'`,
           `left_fraction` |-> `(q',r')`,
           `right_fraction` |->
             `(right_numerator',right_denominator')`]
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes)
      >> impl_tac >- asm_rewrite_tac []
      >> simp
           [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def])
  >> `r' * right_denominator' =
      right_denominator' * r'` by INT_RING_TAC
  >> `bounded_object_q_le_cv bounded_case16594_object_one_cv
        (bounded_object_q_mul_cv c0'' c')` by
     (mp_tac
        (Q.INST
          [`left` |-> `bounded_case16594_object_one_cv`,
           `right` |-> `bounded_object_q_mul_cv c0'' c'`,
           `left_fraction` |-> `(1,1)`,
           `right_fraction` |->
             `(q' * right_numerator',r' * right_denominator')`]
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct)
      >> impl_tac >- asm_rewrite_tac []
      >> simp
           [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
      >> asm_rewrite_tac [])
  >> `bounded_object_q_le_cv bounded_case16594_object_one_cv
        (bounded_object_q_mul_cv c0'' c)` by
     (mp_tac
        (Q.INST
          [`left` |-> `bounded_case16594_object_one_cv`,
           `left'` |-> `bounded_case16594_object_one_cv`,
           `right` |-> `bounded_object_q_mul_cv c0'' c`,
           `right'` |-> `bounded_object_q_mul_cv c0'' c'`]
          compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_le_cv_equiv_cong)
      >> impl_tac >- asm_rewrite_tac []
      >> asm_rewrite_tac [])
  >> `bounded_object_q_ints (bounded_object_q_mul_cv c0'' c) =
        SOME (q' * left_numerator',r' * left_denominator')` by
     (mp_tac
        (Q.INST
          [`left` |-> `c0''`, `right` |-> `c`,
           `left_fraction` |-> `(q',r')`,
           `right_fraction` |->
             `(left_numerator',left_denominator')`]
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes)
      >> impl_tac >- asm_rewrite_tac []
      >> simp
           [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def])
  >> `r' * left_denominator' =
      left_denominator' * r'` by INT_RING_TAC
  >> mp_tac
       (Q.INST
         [`left` |-> `bounded_case16594_object_one_cv`,
          `right` |-> `bounded_object_q_mul_cv c0'' c`,
          `left_fraction` |-> `(1,1)`,
          `right_fraction` |->
            `(q' * left_numerator',r' * left_denominator')`]
         compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct)
  >> impl_tac >- asm_rewrite_tac []
  >> simp
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
  >> asm_rewrite_tac []
QED

val _ = export_theory ()
