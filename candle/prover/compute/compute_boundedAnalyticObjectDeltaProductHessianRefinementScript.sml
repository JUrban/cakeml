(*****************************************************************************
 * Object-q refinement for the compact Hessian of 4 * x_i * delta.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectDeltaProductHessianRefinement
Ancestors
  compute_boundedAnalyticObjectDeltaGradientRefinement
Libs
  bossLib preamble

Definition bounded_object_q_delta_product_hessian_entry_cv_def:
  bounded_object_q_delta_product_hessian_entry_cv coordinate box_coordinate
      delta_gradient row column delta_hessian =
    let base = bounded_object_q_interval_mul_cv
          box_coordinate delta_hessian
    in
      case
        (if row = coordinate then
           case bounded_object_q_nth delta_gradient column of
           | NONE => NONE
           | SOME contribution =>
               SOME (bounded_object_q_interval_add_cv base contribution)
         else SOME base) of
      | NONE => NONE
      | SOME with_row =>
        case
          (if column = coordinate then
             case bounded_object_q_nth delta_gradient row of
             | NONE => NONE
             | SOME contribution =>
                 SOME
                   (bounded_object_q_interval_add_cv with_row contribution)
           else SOME with_row) of
        | NONE => NONE
        | SOME complete_entry =>
            SOME (bounded_object_q_interval_scale4_cv complete_entry)
End

Theorem bounded_delta64_product_hessian_entry_covers_object_q:
  bounded_interval64_covers_object_q
    word_box_coordinate object_box_coordinate /\
  LIST_REL bounded_interval64_covers_object_q
    word_delta_gradient object_delta_gradient /\
  bounded_interval64_covers_object_q
    word_delta_hessian object_delta_hessian /\
  bounded_delta64_product_hessian_entry coordinate word_box_coordinate
    word_delta_gradient row column word_delta_hessian = SOME word_result ==>
  ?object_result.
    bounded_object_q_delta_product_hessian_entry_cv coordinate
      object_box_coordinate object_delta_gradient row column
      object_delta_hessian = SOME object_result /\
    bounded_interval64_covers_object_q word_result object_result
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_product_hessian_entry_def,
      bounded_object_q_delta_product_hessian_entry_cv_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q
  >> imp_res_tac
       compute_boundedAnalyticObjectRefinementTheory.bounded_interval64_nth_covers_object_q_nth
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_add_covers_object_q
  >> imp_res_tac
       compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_interval64_scale4_covers_object_q
  >> gvs []
  >> metis_tac []
QED

Definition bounded_object_q_delta_product_hessian_cv_def:
  bounded_object_q_delta_product_hessian_cv coordinate box_coordinate
      delta_gradient [] [] = SOME [] /\
  bounded_object_q_delta_product_hessian_cv coordinate box_coordinate
      delta_gradient [] (_::_) = NONE /\
  bounded_object_q_delta_product_hessian_cv coordinate box_coordinate
      delta_gradient (_::_) [] = NONE /\
  bounded_object_q_delta_product_hessian_cv coordinate box_coordinate
      delta_gradient ((row,column)::indices) (entry::entries) =
    case bounded_object_q_delta_product_hessian_entry_cv coordinate
      box_coordinate delta_gradient row column entry of
    | NONE => NONE
    | SOME result =>
      case bounded_object_q_delta_product_hessian_cv coordinate box_coordinate
        delta_gradient indices entries of
      | NONE => NONE
      | SOME rest => SOME (result::rest)
End

Theorem bounded_delta64_product_hessian_cons_trace:
  bounded_delta64_product_hessian coordinate box_coordinate delta_gradient
    ((row,column)::indices) (entry::entries) = SOME result ==>
  ?result_entry result_rest.
    bounded_delta64_product_hessian_entry coordinate box_coordinate
      delta_gradient row column entry = SOME result_entry /\
    bounded_delta64_product_hessian coordinate box_coordinate delta_gradient
      indices entries = SOME result_rest /\
    result = result_entry::result_rest
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_product_hessian_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_delta64_product_hessian_covers_object_q:
  !indices entries object_entries word_result.
    bounded_interval64_covers_object_q
      word_box_coordinate object_box_coordinate /\
    LIST_REL bounded_interval64_covers_object_q
      word_delta_gradient object_delta_gradient /\
    LIST_REL bounded_interval64_covers_object_q
      entries object_entries /\
    bounded_delta64_product_hessian coordinate word_box_coordinate
      word_delta_gradient indices entries = SOME word_result ==>
    ?object_result.
      bounded_object_q_delta_product_hessian_cv coordinate
        object_box_coordinate object_delta_gradient indices object_entries =
        SOME object_result /\
      LIST_REL bounded_interval64_covers_object_q
        word_result object_result
Proof
  Induct
  >- (Cases_on `entries`
      >> Cases_on `object_entries`
      >> rw [compute_boundedDeltaTaylorTheory.bounded_delta64_product_hessian_def,
             bounded_object_q_delta_product_hessian_cv_def, LIST_REL_def])
  >> rpt gen_tac
  >> PairCases_on `h`
  >> rpt strip_tac
  >> Cases_on `entries`
  >- fs [compute_boundedDeltaTaylorTheory.bounded_delta64_product_hessian_def]
  >> Cases_on `object_entries`
  >- fs [LIST_REL_def]
  >> fs [LIST_REL_def]
  >> drule bounded_delta64_product_hessian_cons_trace
  >> strip_tac
  >> drule_all bounded_delta64_product_hessian_entry_covers_object_q
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_product_hessian_entry_cv coordinate
          object_box_coordinate object_delta_gradient h0 h1 h' =
          SOME object_entry`
  >> qpat_x_assum `!entries object_entries word_result. _`
       (qspecl_then [`t`, `t'`, `result_rest`] mp_tac)
  >> simp []
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_product_hessian_cv coordinate
          object_box_coordinate object_delta_gradient indices t' =
          SOME object_rest`
  >> qexists_tac `object_entry::object_rest`
  >> fs [bounded_object_q_delta_product_hessian_cv_def, LIST_REL_def]
QED

val _ = export_theory ();
