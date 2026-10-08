(*****************************************************************************
 * Compact fixed-width state for six-dimensional nonlinear Taylor checking.
 *
 * A state carries only the data needed by subsequent instructions and the
 * final Taylor verdict: center value/gradient, whole-box value/gradient, and
 * the twenty-one independent entries of the symmetric Hessian.  The checked
 * constructor and checked linear operations reject malformed shapes and
 * arithmetic overflow explicitly.
 *****************************************************************************)
Theory compute_boundedTaylorState
Ancestors
  compute_boundedIntervalList
Libs
  bossLib preamble

Datatype:
  bounded_taylor64 =
    BoundedTaylor64
      bool
      bounded_interval64
      (bounded_interval64 list)
      bounded_interval64
      (bounded_interval64 list)
      (bounded_interval64 list)
End

Definition bounded_taylor64_well_formed_def:
  bounded_taylor64_well_formed
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) ⇔
    bounded_interval64_valid center_value ∧
    LENGTH center_gradient = 6 ∧
    bounded_interval64_list_valid center_gradient ∧
    bounded_interval64_valid value_bound ∧
    LENGTH gradient_bounds = 6 ∧
    bounded_interval64_list_valid gradient_bounds ∧
    LENGTH hessian = 21 ∧
    bounded_interval64_list_valid hessian
End

Definition bounded_taylor64_make_def:
  bounded_taylor64_make domain center_value center_gradient
      value_bound gradient_bounds hessian =
    let candidate =
      BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian
    in
      if bounded_taylor64_well_formed candidate then SOME candidate else NONE
End

Definition bounded_taylor64_neg_def:
  bounded_taylor64_neg
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) =
    BoundedTaylor64 domain
      (bounded_interval64_neg center_value)
      (bounded_interval64_list_neg center_gradient)
      (bounded_interval64_neg value_bound)
      (bounded_interval64_list_neg gradient_bounds)
      (bounded_interval64_list_neg hessian)
End

Definition bounded_taylor64_add_unchecked_def:
  bounded_taylor64_add_unchecked
      (BoundedTaylor64 left_domain left_center_value left_center_gradient
        left_value_bound left_gradient_bounds left_hessian)
      (BoundedTaylor64 right_domain right_center_value right_center_gradient
        right_value_bound right_gradient_bounds right_hessian) =
    case bounded_interval64_add left_center_value right_center_value of
    | NONE => NONE
    | SOME center_value =>
      case bounded_interval64_list_add
        left_center_gradient right_center_gradient of
      | NONE => NONE
      | SOME center_gradient =>
        case bounded_interval64_add left_value_bound right_value_bound of
        | NONE => NONE
        | SOME value_bound =>
          case bounded_interval64_list_add
            left_gradient_bounds right_gradient_bounds of
          | NONE => NONE
          | SOME gradient_bounds =>
            case bounded_interval64_list_add left_hessian right_hessian of
            | NONE => NONE
            | SOME hessian =>
                SOME
                  (BoundedTaylor64 (left_domain ∧ right_domain)
                    center_value center_gradient value_bound
                    gradient_bounds hessian)
End

Definition bounded_taylor64_add_def:
  bounded_taylor64_add left right =
    if bounded_taylor64_well_formed left ∧
       bounded_taylor64_well_formed right
    then bounded_taylor64_add_unchecked left right
    else NONE
End

Theorem bounded_taylor64_make_some:
  bounded_taylor64_make domain center_value center_gradient
      value_bound gradient_bounds hessian = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_make_def]
  >> fs []
QED

Theorem bounded_taylor64_neg_well_formed:
  bounded_taylor64_well_formed source ⇒
  bounded_taylor64_well_formed (bounded_taylor64_neg source)
Proof
  Cases_on `source`
  >> rw [bounded_taylor64_well_formed_def, bounded_taylor64_neg_def]
  >> metis_tac [compute_boundedIntervalAddTheory.bounded_interval64_neg_valid,
                 bounded_interval64_list_neg_length,
                 bounded_interval64_list_neg_valid]
QED

Theorem bounded_taylor64_add_unchecked_well_formed:
  bounded_taylor64_well_formed left ∧
  bounded_taylor64_well_formed right ∧
  bounded_taylor64_add_unchecked left right = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw [bounded_taylor64_well_formed_def,
         bounded_taylor64_add_unchecked_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac compute_boundedIntervalAddTheory.bounded_interval64_add_value
  >> imp_res_tac bounded_interval64_list_add_length
  >> imp_res_tac bounded_interval64_list_add_valid
  >> fs [bounded_taylor64_well_formed_def]
QED

Theorem bounded_taylor64_add_well_formed:
  bounded_taylor64_add left right = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_add_def]
  >> metis_tac [bounded_taylor64_add_unchecked_well_formed]
QED

Theorem bounded_taylor64_rejects_bad_shape:
  bounded_taylor64_make T bounded_interval64_zero
    [bounded_interval64_zero] bounded_interval64_zero
    [bounded_interval64_zero] [bounded_interval64_zero] = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_taylor64_linear_closed_test:
  let zeros6 = REPLICATE 6 bounded_interval64_zero in
  let zeros21 = REPLICATE 21 bounded_interval64_zero in
  let state = BoundedTaylor64 T bounded_interval64_zero zeros6
    bounded_interval64_zero zeros6 zeros21 in
  bounded_taylor64_well_formed state ∧
  bounded_taylor64_neg state = state ∧
  bounded_taylor64_add state state = SOME state
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
