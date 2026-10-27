(*****************************************************************************
 * Object-q refinement for completed Taylor gradient rows.
 *
 * The executable row completion adds a symmetric first-order variation to
 * one center-gradient interval.  Reuse the proved Taylor-value completion by
 * doubling that variation before its explicit one-half operation; this keeps
 * the rounding argument shared rather than duplicating cross-scale algebra.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectGradientRefinement
Ancestors
  compute_boundedAnalyticObjectCompleteRefinement
Libs
  bossLib preamble intLib

Definition bounded_object_q_taylor_gradient_row_complete_cv_def:
  bounded_object_q_taylor_gradient_row_complete_cv center_entry variation =
    bounded_object_q_taylor_value_complete_cv center_entry
      (bounded_object_q_add_cv variation variation)
End

Theorem bounded_taylor_value_completion_covers_object_q:
  bounded_interval64_covers_object_q
      (BoundedInterval64 center_lower center_upper) object_center_value /\
  bounded192_upper_covers_object_q error object_error /\
  bounded_object_q_nonnegative object_error /\
  (&2417851639229258349412352:int) *
      bounded_signed64_to_int result_lower <=
    (&2417851639229258349412352:int) *
      bounded_signed64_to_int center_lower -
    &(bounded192_to_num error) /\
  (&2417851639229258349412352:int) *
      bounded_signed64_to_int center_upper +
    &(bounded192_to_num error) <=
  (&2417851639229258349412352:int) *
      bounded_signed64_to_int result_upper ==>
  bounded_interval64_covers_object_q
    (BoundedInterval64 result_lower result_upper)
    (bounded_object_q_taylor_value_complete_cv
      object_center_value object_error)
Proof
  strip_tac
  >> Cases_on `bounded_object_q_interval_ints object_center_value`
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
  >> PairCases_on `x`
  >> Cases_on `bounded_object_q_ints object_error`
  >> fs [bounded192_upper_covers_object_q_def,
         bounded_object_q_nonnegative_def]
  >> PairCases_on `x`
  >> `bounded_object_q_interval_ints
        (bounded_object_q_taylor_value_complete_cv
          object_center_value object_error) =
      SOME
        (bounded_object_q_interval_add_ints
          ((x0,x1),(x2,x3))
          ((-x0',x1' * (&2:int)),(x0',x1' * (&2:int))))` by
       (irule bounded_object_q_taylor_value_complete_cv_decodes
        >> simp [])
  >> rw
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
  >> gvs []
  >> match_mp_tac bounded_taylor_value_completion_covers_object_q_ints
  >> simp []
QED

Theorem bounded_taylor_gradient_row_complete_covers_object_q:
  bounded_interval64_covers_object_q center_entry object_center_entry /\
  LIST_REL bounded_interval64_covers_object_q
      hessian_row object_hessian_row /\
  bounded_taylor_gradient_row_complete radii center_entry hessian_row =
    SOME result ==>
  bounded_interval64_covers_object_q result
    (bounded_object_q_taylor_gradient_row_complete_cv object_center_entry
      (bounded_object_q_dot_abs_upper_acc_cv radii object_hessian_row
        (bounded_word64_object_q_cv 0w)))
Proof
  Cases_on `center_entry`
  >> Cases_on `result`
  >> strip_tac
  >> rename1
       `bounded_taylor_gradient_row_complete radii
          (BoundedInterval64 center_lower center_upper) hessian_row =
        SOME (BoundedInterval64 result_lower result_upper)`
  >> mp_tac
       (Q.INST
         [`radii` |-> `radii`, `center_lower` |-> `center_lower`,
          `center_upper` |-> `center_upper`,
          `hessian_row` |-> `hessian_row`,
          `result_lower` |-> `result_lower`,
          `result_upper` |-> `result_upper`]
         compute_boundedTaylorGradientBoundsTheory.bounded_taylor_gradient_row_complete_bounds)
  >> impl_tac
  >- simp []
  >> disch_then (qx_choose_then `variation` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`entries` |-> `hessian_row`,
          `object_entries` |-> `object_hessian_row`,
          `radii` |-> `radii`, `result` |-> `variation`]
         bounded_dot_abs_upper_covers_object_q)
  >> impl_tac
  >- simp []
  >> disch_then assume_tac
  >> mp_tac
       (Q.INST
         [`entries` |-> `hessian_row`,
          `object_entries` |-> `object_hessian_row`,
          `radii` |-> `radii`, `result` |-> `variation`]
         bounded_object_q_dot_abs_upper_cv_nonnegative)
  >> impl_tac
  >- simp []
  >> disch_then assume_tac
  >> mp_tac
       (Q.INST
         [`source` |-> `variation`,
          `object` |->
            `bounded_object_q_dot_abs_upper_acc_cv radii
              object_hessian_row (bounded_word64_object_q_cv 0w)`]
         bounded128_scale41_upper_covers_object_q_double)
  >> impl_tac
  >- simp []
  >> disch_then assume_tac
  >> `bounded_object_q_nonnegative
        (bounded_object_q_add_cv
          (bounded_object_q_dot_abs_upper_acc_cv radii object_hessian_row
            (bounded_word64_object_q_cv 0w))
          (bounded_object_q_dot_abs_upper_acc_cv radii object_hessian_row
            (bounded_word64_object_q_cv 0w)))` by
       (match_mp_tac bounded_object_q_add_cv_nonnegative
        >> simp [])
  >> rw [bounded_object_q_taylor_gradient_row_complete_cv_def]
  >> match_mp_tac
       (Q.INST
         [`error` |-> `bounded128_scale41 variation`,
          `object_error` |->
            `bounded_object_q_add_cv
              (bounded_object_q_dot_abs_upper_acc_cv radii
                object_hessian_row (bounded_word64_object_q_cv 0w))
              (bounded_object_q_dot_abs_upper_acc_cv radii
                object_hessian_row (bounded_word64_object_q_cv 0w))`,
          `object_center_value` |-> `object_center_entry`,
          `center_lower` |-> `center_lower`,
          `center_upper` |-> `center_upper`,
          `result_lower` |-> `result_lower`,
          `result_upper` |-> `result_upper`]
         bounded_taylor_value_completion_covers_object_q)
  >> simp [bounded_completion_scale41_value]
  >> intLib.ARITH_TAC
QED

Definition bounded_object_q_taylor_gradient_rows_complete_cv_def:
  bounded_object_q_taylor_gradient_rows_complete_cv radii [] [] = [] /\
  bounded_object_q_taylor_gradient_rows_complete_cv radii [] (_::_) = [] /\
  bounded_object_q_taylor_gradient_rows_complete_cv radii (_::_) [] = [] /\
  bounded_object_q_taylor_gradient_rows_complete_cv radii
      (center_entry::center_rest) (hessian_row::hessian_rest) =
    bounded_object_q_taylor_gradient_row_complete_cv center_entry
      (bounded_object_q_dot_abs_upper_acc_cv radii hessian_row
        (bounded_word64_object_q_cv 0w)) ::
    bounded_object_q_taylor_gradient_rows_complete_cv radii
      center_rest hessian_rest
End

Theorem bounded_taylor_gradient_rows_complete_covers_object_q:
  !center_gradient object_center_gradient hessian_rows
      object_hessian_rows result.
    LIST_REL bounded_interval64_covers_object_q
        center_gradient object_center_gradient /\
    LIST_REL (LIST_REL bounded_interval64_covers_object_q)
        hessian_rows object_hessian_rows /\
    bounded_taylor_gradient_rows_complete
        radii center_gradient hessian_rows = SOME result ==>
    LIST_REL bounded_interval64_covers_object_q result
      (bounded_object_q_taylor_gradient_rows_complete_cv
        radii object_center_gradient object_hessian_rows)
Proof
  Induct_on `center_gradient`
  >> Cases_on `object_center_gradient`
  >> Cases_on `hessian_rows`
  >> Cases_on `object_hessian_rows`
  >> rw [compute_boundedTaylorGradientTheory.bounded_taylor_gradient_rows_complete_def,
         bounded_object_q_taylor_gradient_rows_complete_cv_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> metis_tac [bounded_taylor_gradient_row_complete_covers_object_q]
QED

Theorem bounded_hessian64_rows_list_rel_right:
  bounded_hessian64_rows left = SOME left_rows /\
  LIST_REL element_relation left right ==>
  ?right_rows.
    bounded_hessian64_rows right = SOME right_rows /\
    LIST_REL (LIST_REL element_relation) left_rows right_rows
Proof
  rw [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
QED

Definition bounded_object_q_taylor_gradient_complete_cv_def:
  bounded_object_q_taylor_gradient_complete_cv
      radii center_gradient hessian =
    case bounded_hessian64_rows hessian of
    | NONE => []
    | SOME rows =>
        bounded_object_q_taylor_gradient_rows_complete_cv
          radii center_gradient rows
End

Theorem bounded_taylor_gradient_complete_covers_object_q:
  LIST_REL bounded_interval64_covers_object_q
      center_gradient object_center_gradient /\
  LIST_REL bounded_interval64_covers_object_q hessian object_hessian /\
  bounded_taylor_gradient_complete radii center_gradient hessian =
    SOME result ==>
  LIST_REL bounded_interval64_covers_object_q result
    (bounded_object_q_taylor_gradient_complete_cv
      radii object_center_gradient object_hessian)
Proof
  rw [compute_boundedTaylorGradientTheory.bounded_taylor_gradient_complete_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_hessian64_rows_list_rel_right
  >> rw [bounded_object_q_taylor_gradient_complete_cv_def]
  >> gvs []
  >> match_mp_tac bounded_taylor_gradient_rows_complete_covers_object_q
  >> qexists_tac `center_gradient`
  >> qexists_tac `x`
  >> simp []
QED

val _ = export_theory ();
