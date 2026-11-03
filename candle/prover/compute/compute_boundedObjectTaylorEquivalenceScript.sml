(*****************************************************************************
 * Representation-independent equivalence for exact object-q Taylor states.
 *
 * The production evaluator is free to normalize a rational while the HOL
 * object semantics deliberately keeps many witnesses unnormalised.  The two
 * states therefore cannot be joined by cv equality.  This relation compares
 * every rational endpoint by its mathematical value while retaining exact
 * agreement of the domain bit, list shape, and Taylor-state layout.
 *****************************************************************************)
open compute_boundedAnalyticObjectPolyProgramRefinementTheory
open compute_boundedPackedObjectEntryContractTheory
open compute_boundedQFoldRelationTheory
open preamble

Theory compute_boundedObjectTaylorEquivalence
Ancestors
  compute_boundedAnalyticObjectPolyProgramRefinement
  compute_boundedPackedObjectEntryContract
  compute_boundedQFoldRelation
Libs
  bossLib preamble intLib

Definition bounded_object_q_cv_equiv_direct_def:
  bounded_object_q_cv_equiv_direct
      (Pair (Pair (Num left_positive) (Num left_negative))
        (Num left_denominator_predecessor))
      (Pair (Pair (Num right_positive) (Num right_negative))
        (Num right_denominator_predecessor)) =
    (left_positive * SUC right_denominator_predecessor +
       right_negative * SUC left_denominator_predecessor =
     right_positive * SUC left_denominator_predecessor +
       left_negative * SUC right_denominator_predecessor) /\
  bounded_object_q_cv_equiv_direct _ _ = F
End

Definition bounded_object_q_interval_cv_equiv_direct_def:
  bounded_object_q_interval_cv_equiv_direct
      (Pair left_lower left_upper) (Pair right_lower right_upper) =
    (bounded_object_q_cv_equiv_direct left_lower right_lower /\
     bounded_object_q_cv_equiv_direct left_upper right_upper) /\
  bounded_object_q_interval_cv_equiv_direct _ _ = F
End

Definition bounded_object_q_interval_cv_equiv_def:
  bounded_object_q_interval_cv_equiv (Pair left_lower left_upper)
      (Pair right_lower right_upper) =
    (bounded_case10173_q_cv_equiv left_lower right_lower /\
     bounded_case10173_q_cv_equiv left_upper right_upper) /\
  bounded_object_q_interval_cv_equiv _ _ = F
End

Theorem bounded_object_q_cv_equiv_direct_correct:
  bounded_object_q_cv_equiv_direct left right <=>
  bounded_case10173_q_cv_equiv left right
Proof
  eq_tac
  >- (qsuff_tac
        `!left right.
           bounded_object_q_cv_equiv_direct left right ==>
           bounded_case10173_q_cv_equiv left right`
      >- metis_tac []
      >> ho_match_mp_tac bounded_object_q_cv_equiv_direct_ind
      >> rpt conj_tac
      >> rpt gen_tac
      >> simp [bounded_object_q_cv_equiv_direct_def]
      >> simp
        [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
         optionTheory.OPTION_BIND_def,integerTheory.INT_MUL,
         integerTheory.INT_ADD]
      >> strip_tac
      >> `(&(left_positive * SUC right_denominator_predecessor +
                right_negative * SUC left_denominator_predecessor):int) =
            &(left_negative * SUC right_denominator_predecessor +
                right_positive * SUC left_denominator_predecessor)` by
           simp []
      >> qpat_x_assum `&(a + b) = &(c + d)`
           (fn th => assume_tac
             (REWRITE_RULE
               [GSYM integerTheory.INT_ADD,GSYM integerTheory.INT_MUL] th))
      >> qpat_x_assum `x:num = y` kall_tac
      >> rw [integerTheory.INT_SUB_RDISTRIB]
      >> PURE_REWRITE_TAC [GSYM integerTheory.INT_MUL]
      >> intLib.ARITH_TAC)
  >> strip_tac
  >> drule
       compute_boundedQFoldRelationTheory.bounded_object_q_cv_equiv_decodes
  >> strip_tac
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
  >> simp [bounded_object_q_cv_equiv_direct_def]
  >> irule (iffLR (SPEC_ALL integerTheory.INT_INJ))
  >> PURE_REWRITE_TAC
       [GSYM integerTheory.INT_ADD,GSYM integerTheory.INT_MUL]
  >> qpat_x_assum `(a - b) * c = (d - e) * f`
       (fn th => assume_tac
         (REWRITE_RULE [integerTheory.INT_SUB_RDISTRIB] th))
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_q_interval_cv_equiv_direct_correct:
  bounded_object_q_interval_cv_equiv_direct left right <=>
  bounded_object_q_interval_cv_equiv left right
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp
    [bounded_object_q_interval_cv_equiv_direct_def,
     bounded_object_q_interval_cv_equiv_def,
     bounded_object_q_cv_equiv_direct_correct]
QED

Definition bounded_object_q_interval_list_cv_equiv_def:
  bounded_object_q_interval_list_cv_equiv (Num 0) (Num 0) = T /\
  bounded_object_q_interval_list_cv_equiv
      (Pair left lefts) (Pair right rights) =
    (bounded_object_q_interval_cv_equiv left right /\
     bounded_object_q_interval_list_cv_equiv lefts rights) /\
  bounded_object_q_interval_list_cv_equiv _ _ = F
Termination
  wf_rel_tac `measure (cv_size o FST)` >> rw []
End

Definition bounded_object_q_interval_list_cv_equiv_direct_def:
  bounded_object_q_interval_list_cv_equiv_direct (Num 0) (Num 0) = T /\
  bounded_object_q_interval_list_cv_equiv_direct
      (Pair left lefts) (Pair right rights) =
    (bounded_object_q_interval_cv_equiv_direct left right /\
     bounded_object_q_interval_list_cv_equiv_direct lefts rights) /\
  bounded_object_q_interval_list_cv_equiv_direct _ _ = F
Termination
  wf_rel_tac `measure (cv_size o FST)` >> rw []
End

Theorem bounded_object_q_interval_list_cv_equiv_direct_correct:
  !left right.
    bounded_object_q_interval_list_cv_equiv_direct left right <=>
    bounded_object_q_interval_list_cv_equiv left right
Proof
  ho_match_mp_tac bounded_object_q_interval_list_cv_equiv_direct_ind
  >> rw
    [bounded_object_q_interval_list_cv_equiv_direct_def,
     bounded_object_q_interval_list_cv_equiv_def,
     bounded_object_q_interval_cv_equiv_direct_correct]
QED

Definition bounded_object_q_taylor_state_encoded_cv_def:
  bounded_object_q_taylor_state_encoded_cv
      (BoundedObjectQTaylor domain center center_gradient value_bound
        gradient_bounds hessian) =
    Pair (if domain then Num 1 else Num 0)
      (Pair center
        (Pair (bounded_object_q_cv_list center_gradient)
          (Pair value_bound
            (Pair (bounded_object_q_cv_list gradient_bounds)
              (bounded_object_q_cv_list hessian)))))
End

Definition bounded_object_q_taylor_domain_def:
  bounded_object_q_taylor_domain
      (BoundedObjectQTaylor domain center center_gradient value_bound
        gradient_bounds hessian) = domain
End

Definition bounded_object_q_taylor_center_def:
  bounded_object_q_taylor_center
      (BoundedObjectQTaylor domain center center_gradient value_bound
        gradient_bounds hessian) = center
End

Definition bounded_object_q_taylor_center_gradient_def:
  bounded_object_q_taylor_center_gradient
      (BoundedObjectQTaylor domain center center_gradient value_bound
        gradient_bounds hessian) = center_gradient
End

Definition bounded_object_q_taylor_value_bound_def:
  bounded_object_q_taylor_value_bound
      (BoundedObjectQTaylor domain center center_gradient value_bound
        gradient_bounds hessian) = value_bound
End

Definition bounded_object_q_taylor_gradient_bounds_def:
  bounded_object_q_taylor_gradient_bounds
      (BoundedObjectQTaylor domain center center_gradient value_bound
        gradient_bounds hessian) = gradient_bounds
End

Definition bounded_object_q_taylor_hessian_def:
  bounded_object_q_taylor_hessian
      (BoundedObjectQTaylor domain center center_gradient value_bound
        gradient_bounds hessian) = hessian
End

Definition bounded_object_q_taylor_state_cv_equiv_def:
  bounded_object_q_taylor_state_cv_equiv
      (Pair left_domain
        (Pair left_center
          (Pair left_center_gradient
            (Pair left_value_bound
              (Pair left_gradient_bounds left_hessian)))))
      (Pair right_domain
        (Pair right_center
          (Pair right_center_gradient
            (Pair right_value_bound
              (Pair right_gradient_bounds right_hessian))))) =
    (left_domain = right_domain /\
     bounded_object_q_interval_cv_equiv left_center right_center /\
     bounded_object_q_interval_list_cv_equiv
       left_center_gradient right_center_gradient /\
     bounded_object_q_interval_cv_equiv left_value_bound right_value_bound /\
     bounded_object_q_interval_list_cv_equiv
       left_gradient_bounds right_gradient_bounds /\
     bounded_object_q_interval_list_cv_equiv left_hessian right_hessian) /\
  bounded_object_q_taylor_state_cv_equiv _ _ = F
End

Definition bounded_object_q_taylor_runtime_equiv_def:
  bounded_object_q_taylor_runtime_equiv runtime semantic <=>
    bounded_object_q_taylor_state_cv_equiv runtime
      (bounded_object_q_taylor_state_encoded_cv semantic)
End

Theorem bounded_object_q_interval_cv_equiv_sym:
  bounded_object_q_interval_cv_equiv left right ==>
  bounded_object_q_interval_cv_equiv right left
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp [bounded_object_q_interval_cv_equiv_def]
  >> metis_tac
       [compute_boundedQRelationAlgebraTheory.bounded_case10173_q_cv_equiv_sym]
QED

Theorem bounded_object_q_interval_cv_equiv_trans:
  bounded_object_q_interval_cv_equiv left middle /\
  bounded_object_q_interval_cv_equiv middle right ==>
  bounded_object_q_interval_cv_equiv left right
Proof
  Cases_on `left`
  >> Cases_on `middle`
  >> Cases_on `right`
  >> simp [bounded_object_q_interval_cv_equiv_def]
  >> metis_tac
    [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans]
QED

Theorem bounded_object_q_interval_list_cv_equiv_encoded:
  !left right.
    bounded_object_q_interval_list_cv_equiv
      (bounded_object_q_cv_list left) (bounded_object_q_cv_list right) <=>
    LIST_REL bounded_object_q_interval_cv_equiv left right
Proof
  Induct
  >> Cases_on `right`
  >> simp
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        bounded_object_q_interval_list_cv_equiv_def,LIST_REL_def]
QED

Theorem bounded_object_q_interval_list_rel_trans:
  !left middle right.
    LIST_REL bounded_object_q_interval_cv_equiv left middle /\
    LIST_REL bounded_object_q_interval_cv_equiv middle right ==>
    LIST_REL bounded_object_q_interval_cv_equiv left right
Proof
  Induct
  >> Cases_on `middle`
  >> Cases_on `right`
  >> simp [LIST_REL_def]
  >> metis_tac [bounded_object_q_interval_cv_equiv_trans]
QED

Theorem bounded_object_q_interval_list_cv_equiv_trans:
  !left middle right.
    bounded_object_q_interval_list_cv_equiv left middle /\
    bounded_object_q_interval_list_cv_equiv middle right ==>
    bounded_object_q_interval_list_cv_equiv left right
Proof
  Induct_on `left`
  >> Cases_on `middle`
  >> Cases_on `right`
  >> simp [bounded_object_q_interval_list_cv_equiv_def]
  >- (Cases_on `n''`
      >> Cases_on `n`
      >> Cases_on `n'`
      >> simp [bounded_object_q_interval_list_cv_equiv_def])
  >> strip_tac
  >> conj_tac
  >- (irule bounded_object_q_interval_cv_equiv_trans
      >> qexists_tac `c`
      >> simp [])
  >> qpat_x_assum `!middle right.
       bounded_object_q_interval_list_cv_equiv left' middle /\
       bounded_object_q_interval_list_cv_equiv middle right ==>
       bounded_object_q_interval_list_cv_equiv left' right`
       (qspecl_then [`c0`,`c0'`] mp_tac)
  >> simp []
QED

Theorem bounded_object_q_taylor_runtime_equiv_fields:
  bounded_object_q_taylor_runtime_equiv
      (Pair (if left_domain then Num 1 else Num 0)
        (Pair left_center
          (Pair (bounded_object_q_cv_list left_center_gradient)
            (Pair left_value_bound
              (Pair (bounded_object_q_cv_list left_gradient_bounds)
                (bounded_object_q_cv_list left_hessian))))))
      (BoundedObjectQTaylor right_domain right_center right_center_gradient
        right_value_bound right_gradient_bounds right_hessian) <=>
    left_domain = right_domain /\
    bounded_object_q_interval_cv_equiv left_center right_center /\
    LIST_REL bounded_object_q_interval_cv_equiv
      left_center_gradient right_center_gradient /\
    bounded_object_q_interval_cv_equiv left_value_bound right_value_bound /\
    LIST_REL bounded_object_q_interval_cv_equiv
      left_gradient_bounds right_gradient_bounds /\
    LIST_REL bounded_object_q_interval_cv_equiv left_hessian right_hessian
Proof
  Cases_on `left_domain`
  >> Cases_on `right_domain`
  >> simp
    [bounded_object_q_taylor_runtime_equiv_def,
     bounded_object_q_taylor_state_encoded_cv_def,
     bounded_object_q_taylor_state_cv_equiv_def,
     bounded_object_q_interval_list_cv_equiv_encoded]
QED

Theorem bounded_object_q_taylor_runtime_equiv_selectors:
  bounded_object_q_taylor_runtime_equiv
      (Pair runtime_domain
        (Pair runtime_center
          (Pair runtime_center_gradient
            (Pair runtime_value_bound
              (Pair runtime_gradient_bounds runtime_hessian)))))
      semantic <=>
    runtime_domain =
      (if bounded_object_q_taylor_domain semantic then Num 1 else Num 0) /\
    bounded_object_q_interval_cv_equiv runtime_center
      (bounded_object_q_taylor_center semantic) /\
    bounded_object_q_interval_list_cv_equiv runtime_center_gradient
      (bounded_object_q_cv_list
        (bounded_object_q_taylor_center_gradient semantic)) /\
    bounded_object_q_interval_cv_equiv runtime_value_bound
      (bounded_object_q_taylor_value_bound semantic) /\
    bounded_object_q_interval_list_cv_equiv runtime_gradient_bounds
      (bounded_object_q_cv_list
        (bounded_object_q_taylor_gradient_bounds semantic)) /\
    bounded_object_q_interval_list_cv_equiv runtime_hessian
      (bounded_object_q_cv_list (bounded_object_q_taylor_hessian semantic))
Proof
  Cases_on `semantic`
  >> simp
    [bounded_object_q_taylor_runtime_equiv_def,
     bounded_object_q_taylor_state_encoded_cv_def,
     bounded_object_q_taylor_state_cv_equiv_def,
     bounded_object_q_taylor_domain_def,
     bounded_object_q_taylor_center_def,
     bounded_object_q_taylor_center_gradient_def,
     bounded_object_q_taylor_value_bound_def,
     bounded_object_q_taylor_gradient_bounds_def,
     bounded_object_q_taylor_hessian_def]
QED

val _ = export_theory ();
