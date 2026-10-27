(*****************************************************************************
 * Object-q refinement for the compact delta gradient.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectDeltaGradientRefinement
Ancestors
  compute_boundedAnalyticObjectDeltaHessianRefinement
Libs
  bossLib preamble

Definition bounded_delta_signed_term_covers_object_q_def:
  bounded_delta_signed_term_covers_object_q
      (word_negative,word_value) (object_negative,object_value) <=>
    word_negative = object_negative /\
    bounded_interval64_covers_object_q word_value object_value
End

Definition bounded_delta_gradient_signed_indices_def:
  bounded_delta_gradient_signed_indices (coordinate:num) =
    if coordinate = 0 then
      SOME
        ([(T,3);(T,3);(F,8);(F,9);(T,10);(F,12);
          (T,13);(F,14);(T,15);(F,16);(F,17)] : (bool # num) list)
    else if coordinate = 1 then
      SOME
        [(F,3);(F,4);(T,5);(T,9);(T,9);(T,12);
         (F,13);(F,14);(F,16);(T,18);(F,19)]
    else if coordinate = 2 then
      SOME
        [(F,3);(T,4);(F,5);(T,8);(F,9);(F,10);
         (T,14);(T,14);(F,17);(F,19);(T,20)]
    else if coordinate = 3 then
      SOME
        [(T,0);(F,1);(F,2);(T,3);(T,3);(F,4);
         (F,5);(T,7);(F,9);(F,14);(T,19)]
    else if coordinate = 4 then
      SOME
        [(F,1);(T,2);(F,3);(T,6);(F,7);(F,8);
         (T,9);(T,9);(F,10);(F,14);(T,17)]
    else if coordinate = 5 then
      SOME
        [(T,1);(F,2);(F,3);(F,7);(F,9);(T,11);
         (F,12);(F,13);(T,14);(T,14);(T,16)]
    else NONE
End

Definition bounded_delta64_select_signed_terms_def:
  bounded_delta64_select_signed_terms [] products = SOME [] /\
  bounded_delta64_select_signed_terms
      ((negative,index)::indices) products =
    case bounded_interval64_nth products index of
    | NONE => NONE
    | SOME value =>
      case bounded_delta64_select_signed_terms indices products of
      | NONE => NONE
      | SOME rest => SOME ((negative,value)::rest)
End

Definition bounded_object_q_delta_select_signed_terms_cv_def:
  bounded_object_q_delta_select_signed_terms_cv [] products = SOME [] /\
  bounded_object_q_delta_select_signed_terms_cv
      ((negative,index)::indices) products =
    case bounded_object_q_nth products index of
    | NONE => NONE
    | SOME value =>
      case bounded_object_q_delta_select_signed_terms_cv indices products of
      | NONE => NONE
      | SOME rest => SOME ((negative,value)::rest)
End

Theorem bounded_delta64_select_signed_terms_covers_object_q:
  !indices word_terms.
    LIST_REL bounded_interval64_covers_object_q
      word_products object_products /\
    bounded_delta64_select_signed_terms indices word_products =
      SOME word_terms ==>
    ?object_terms.
      bounded_object_q_delta_select_signed_terms_cv
        indices object_products = SOME object_terms /\
      LIST_REL bounded_delta_signed_term_covers_object_q
        word_terms object_terms
Proof
  Induct
  >- (rw [bounded_delta64_select_signed_terms_def,
          bounded_object_q_delta_select_signed_terms_cv_def]
      >> qexists_tac `[]`
      >> simp [LIST_REL_def])
  >> rpt strip_tac
  >> PairCases_on `h`
  >> fs [bounded_delta64_select_signed_terms_def]
  >> Cases_on `bounded_interval64_nth word_products h1`
  >> gvs []
  >> Cases_on
       `bounded_delta64_select_signed_terms indices word_products`
  >> gvs []
  >> rename1
       `bounded_interval64_nth word_products h1 = SOME word_value`
  >> rename1
       `bounded_object_q_delta_select_signed_terms_cv indices
          object_products = SOME object_rest`
  >> drule_all
       compute_boundedAnalyticObjectRefinementTheory.bounded_interval64_nth_covers_object_q_nth
  >> strip_tac
  >> rename1
       `bounded_object_q_nth object_products h1 = SOME object_value`
  >> qexists_tac `(h0,object_value)::object_rest`
  >> simp [bounded_object_q_delta_select_signed_terms_cv_def, LIST_REL_def,
           bounded_delta_signed_term_covers_object_q_def]
QED

Theorem bounded_delta64_gradient_signed_terms_select:
  bounded_delta64_gradient_signed_terms coordinate products =
    SOME word_terms ==>
  ?indices.
    bounded_delta_gradient_signed_indices coordinate = SOME indices /\
    bounded_delta64_select_signed_terms indices products = SOME word_terms
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_signed_terms_def,
      bounded_delta_gradient_signed_indices_def]
  >> every_case_tac
  >> gvs [bounded_delta64_select_signed_terms_def,
          compute_boundedTaylorBaseTheory.bounded_interval64_nth_def]
  >> EVAL_TAC
QED

Definition bounded_object_q_delta_gradient_signed_terms_cv_def:
  bounded_object_q_delta_gradient_signed_terms_cv coordinate products =
    case bounded_delta_gradient_signed_indices coordinate of
    | NONE => NONE
    | SOME indices =>
        bounded_object_q_delta_select_signed_terms_cv indices products
End

Theorem bounded_delta64_gradient_signed_terms_covers_object_q:
  LIST_REL bounded_interval64_covers_object_q
    word_products object_products /\
  bounded_delta64_gradient_signed_terms coordinate word_products =
    SOME word_terms ==>
  ?object_terms.
    bounded_object_q_delta_gradient_signed_terms_cv
      coordinate object_products = SOME object_terms /\
    LIST_REL bounded_delta_signed_term_covers_object_q
      word_terms object_terms
Proof
  strip_tac
  >> drule bounded_delta64_gradient_signed_terms_select
  >> strip_tac
  >> drule_all bounded_delta64_select_signed_terms_covers_object_q
  >> strip_tac
  >> qexists_tac `object_terms`
  >> rw [bounded_object_q_delta_gradient_signed_terms_cv_def]
  >> gvs []
QED

Definition bounded_object_q_delta_apply_signed_terms_cv_def:
  bounded_object_q_delta_apply_signed_terms_cv terms =
    MAP (\(negative,value).
      if negative then bounded_object_q_interval_neg_cv value else value) terms
End

Theorem bounded_delta64_apply_signed_term_covers_object_q:
  bounded_delta_signed_term_covers_object_q word_term object_term ==>
  bounded_interval64_covers_object_q
    ((\(negative,value).
       if negative then bounded_interval64_neg value else value) word_term)
    ((\(negative,value).
       if negative then bounded_object_q_interval_neg_cv value else value)
      object_term)
Proof
  PairCases_on `word_term`
  >> PairCases_on `object_term`
  >> rw [bounded_delta_signed_term_covers_object_q_def]
  >> metis_tac
       [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_neg_covers_object_q]
QED

Theorem bounded_delta64_apply_signed_terms_covers_object_q:
  !word_terms object_terms.
    LIST_REL bounded_delta_signed_term_covers_object_q
      word_terms object_terms ==>
    LIST_REL bounded_interval64_covers_object_q
      (bounded_delta64_apply_signed_terms word_terms)
      (bounded_object_q_delta_apply_signed_terms_cv object_terms)
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_apply_signed_terms_def,
      bounded_object_q_delta_apply_signed_terms_cv_def,
      listTheory.LIST_REL_MAP1, listTheory.LIST_REL_MAP2]
  >> irule listTheory.LIST_REL_mono
  >> qexists_tac `bounded_delta_signed_term_covers_object_q`
  >> simp []
  >> metis_tac [bounded_delta64_apply_signed_term_covers_object_q]
QED

Definition bounded_object_q_delta_gradient_component_from_products_cv_def:
  bounded_object_q_delta_gradient_component_from_products_cv
      coordinate products =
    case bounded_object_q_delta_gradient_signed_terms_cv coordinate products of
    | NONE => NONE
    | SOME terms =>
        SOME (bounded_object_q_interval_sum_cv
          (bounded_object_q_delta_apply_signed_terms_cv terms))
End

Theorem bounded_delta64_gradient_component_from_products_trace:
  bounded_delta64_gradient_component_from_products
    coordinate products = SOME result ==>
  ?word_terms.
    bounded_delta64_gradient_signed_terms coordinate products =
      SOME word_terms /\
    bounded_interval64_sum
      (bounded_delta64_apply_signed_terms word_terms) = SOME result
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_component_from_products_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_delta64_gradient_component_from_products_covers_object_q:
  LIST_REL bounded_interval64_covers_object_q
    word_products object_products /\
  bounded_delta64_gradient_component_from_products
    coordinate word_products = SOME result ==>
  ?object_result.
    bounded_object_q_delta_gradient_component_from_products_cv
      coordinate object_products = SOME object_result /\
    bounded_interval64_covers_object_q result object_result
Proof
  strip_tac
  >> drule bounded_delta64_gradient_component_from_products_trace
  >> strip_tac
  >> drule_all bounded_delta64_gradient_signed_terms_covers_object_q
  >> strip_tac
  >> imp_res_tac bounded_delta64_apply_signed_terms_covers_object_q
  >> qexists_tac
       `bounded_object_q_interval_sum_cv
          (bounded_object_q_delta_apply_signed_terms_cv object_terms)`
  >> rw [bounded_object_q_delta_gradient_component_from_products_cv_def]
  >> match_mp_tac
       (Q.INST
         [`word_values` |-> `bounded_delta64_apply_signed_terms word_terms`,
          `object_values` |->
            `bounded_object_q_delta_apply_signed_terms_cv object_terms`,
          `result` |-> `result`]
         compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_interval64_sum_covers_object_q)
  >> simp []
QED

Definition bounded_object_q_delta_gradient_components_cv_def:
  bounded_object_q_delta_gradient_components_cv [] products = SOME [] /\
  bounded_object_q_delta_gradient_components_cv
      (coordinate::coordinates) products =
    case bounded_object_q_delta_gradient_component_from_products_cv
      coordinate products of
    | NONE => NONE
    | SOME entry =>
      case bounded_object_q_delta_gradient_components_cv
        coordinates products of
      | NONE => NONE
      | SOME rest => SOME (entry::rest)
End

Theorem bounded_delta64_gradient_components_cons_trace:
  bounded_delta64_gradient_components (coordinate::coordinates)
    products = SOME result ==>
  ?word_entry word_rest.
    bounded_delta64_gradient_component_from_products coordinate products =
      SOME word_entry /\
    bounded_delta64_gradient_components coordinates products =
      SOME word_rest /\
    result = word_entry::word_rest
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_components_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_delta64_gradient_components_covers_object_q:
  !coordinates word_result.
    LIST_REL bounded_interval64_covers_object_q
      word_products object_products /\
    bounded_delta64_gradient_components coordinates word_products =
      SOME word_result ==>
    ?object_result.
      bounded_object_q_delta_gradient_components_cv
        coordinates object_products = SOME object_result /\
      LIST_REL bounded_interval64_covers_object_q
        word_result object_result
Proof
  Induct
  >- (rw [compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_components_def,
          bounded_object_q_delta_gradient_components_cv_def]
      >> qexists_tac `[]`
      >> simp [LIST_REL_def])
  >> rpt strip_tac
  >> drule bounded_delta64_gradient_components_cons_trace
  >> strip_tac
  >> drule_all
       bounded_delta64_gradient_component_from_products_covers_object_q
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_gradient_component_from_products_cv
          h object_products = SOME object_entry`
  >> qpat_x_assum `!word_result. _` (qspec_then `word_rest` mp_tac)
  >> simp []
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_gradient_components_cv coordinates
          object_products = SOME object_rest`
  >> qexists_tac `object_entry::object_rest`
  >> fs [bounded_object_q_delta_gradient_components_cv_def, LIST_REL_def]
QED

Definition bounded_object_q_delta_gradient_from_products_cv_def:
  bounded_object_q_delta_gradient_from_products_cv products =
    bounded_object_q_delta_gradient_components_cv [0;1;2;3;4;5] products
End

Theorem bounded_delta64_gradient_from_products_covers_object_q:
  LIST_REL bounded_interval64_covers_object_q
    word_products object_products /\
  bounded_delta64_gradient_from_products word_products = SOME word_result ==>
  ?object_result.
    bounded_object_q_delta_gradient_from_products_cv object_products =
      SOME object_result /\
    LIST_REL bounded_interval64_covers_object_q word_result object_result
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_from_products_def,
      bounded_object_q_delta_gradient_from_products_cv_def]
  >> metis_tac [bounded_delta64_gradient_components_covers_object_q]
QED

val _ = export_theory ();
