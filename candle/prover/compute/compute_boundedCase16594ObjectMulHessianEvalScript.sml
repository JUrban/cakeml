(*****************************************************************************
 * Exact evaluator semantics for the fixed six-dimensional multiplication
 * Hessian.  This layer authenticates the four-product accumulator and the
 * triangular packed-index maps before composing the 21 concrete entries.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectMulHessianEval
Ancestors
  compute_boundedCase16594ObjectMulEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_products_sum4_body_def:
  bounded_case16594_object_products_sum4_body =
    App «candle_cv_q_interval_add»
      [App «candle_cv_q_interval_add»
        [App «candle_cv_q_interval_add»
          [App «candle_cv_q_interval_add»
            [App «candle_cv_q_zero_interval» [];
             App «candle_cv_q_interval_mul»
               [Var «first_left»;Var «first_right»]];
           App «candle_cv_q_interval_mul»
             [Var «second_left»;Var «second_right»]];
         App «candle_cv_q_interval_mul»
           [Var «third_left»;Var «third_right»]];
       App «candle_cv_q_interval_mul»
         [Var «fourth_left»;Var «fourth_right»]]
End

Definition bounded_case16594_object_hessian6_row_body_def:
  bounded_case16594_object_hessian6_row_body =
    If (Binop Less (Var «selector») (Num 6)) (Num 0)
      (If (Binop Less (Var «selector») (Num 11)) (Num 1)
        (If (Binop Less (Var «selector») (Num 15)) (Num 2)
          (If (Binop Less (Var «selector») (Num 18)) (Num 3)
            (If (Binop Less (Var «selector») (Num 20)) (Num 4)
              (Num 5)))))
End

Definition bounded_case16594_object_hessian6_col_body_def:
  bounded_case16594_object_hessian6_col_body =
    If (Binop Less (Var «selector») (Num 6)) (Var «selector»)
      (If (Binop Less (Var «selector») (Num 11))
        (Binop Sub (Var «selector») (Num 5))
        (If (Binop Less (Var «selector») (Num 15))
          (Binop Sub (Var «selector») (Num 9))
          (If (Binop Less (Var «selector») (Num 18))
            (Binop Sub (Var «selector») (Num 12))
            (If (Binop Less (Var «selector») (Num 20))
              (Binop Sub (Var «selector») (Num 14))
              (Num 5)))))
End

Definition bounded_case16594_object_hessian6_row_index_def:
  bounded_case16594_object_hessian6_row_index (selector:num) =
    if selector < 6 then (0:num)
    else if selector < 11 then 1
    else if selector < 15 then 2
    else if selector < 18 then 3
    else if selector < 20 then 4
    else 5
End

Definition bounded_case16594_object_hessian6_col_index_def:
  bounded_case16594_object_hessian6_col_index (selector:num) =
    if selector < 6 then selector
    else if selector < 11 then selector - 5
    else if selector < 15 then selector - 9
    else if selector < 18 then selector - 12
    else if selector < 20 then selector - 14
    else 5
End

Theorem bounded_case16594_object_compute_eval_literal_app8:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME
      ([name1;name2;name3;name4;name5;name6;name7;name8],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv argument1;from_cv argument2;from_cv argument3;
         from_cv argument4;from_cv argument5;from_cv argument6;
         from_cv argument7;from_cv argument8]) (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name1,from_cv argument1);(name2,from_cv argument2);
         (name3,from_cv argument3);(name4,from_cv argument4);
         (name5,from_cv argument5);(name6,from_cv argument6);
         (name7,from_cv argument7);(name8,from_cv argument8)] body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_packed_interval_add_encoded:
  bounded_packed_q_interval_encoded left /\
  bounded_packed_q_interval_encoded right ==>
  bounded_packed_q_interval_encoded
    (bounded_object_q_interval_add_cv left right)
Proof
  metis_tac
    [bounded_case16594_packed_interval_object_encoded,
     bounded_case16594_object_interval_packed_encoded,
     compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded]
QED

Theorem bounded_case16594_packed_interval_mul_encoded:
  bounded_packed_q_interval_encoded left /\
  bounded_packed_q_interval_encoded right ==>
  bounded_packed_q_interval_encoded
    (bounded_object_q_interval_mul_cv left right)
Proof
  metis_tac
    [bounded_case16594_packed_interval_object_encoded,
     bounded_case16594_object_interval_packed_encoded,
     compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded]
QED

Theorem bounded_case16594_packed_zero_interval_encoded[simp]:
  bounded_packed_q_interval_encoded
    (bounded_analytic_source_q_interval_cv 0 0 0)
Proof
  metis_tac
    [bounded_case16594_object_interval_packed_encoded,
     compute_boundedObjectTaylorZeroAlgebraTheory.bounded_analytic_source_q_interval_cv_encoded]
QED

Theorem bounded_case16594_object_interval_accumulate_product_eval:
  bounded_packed_q_interval_encoded accumulator /\
  bounded_packed_q_interval_encoded left /\
  bounded_packed_q_interval_encoded right /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      accumulator_expression (refs:hol_refs) =
    (M_success (from_cv accumulator),refs) /\
  8 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_add»
        [accumulator_expression;
         App «candle_cv_q_interval_mul» [from_cv left;from_cv right]]) refs =
    (M_success
      (from_cv
        (bounded_object_q_interval_add_cv accumulator
          (bounded_object_q_interval_mul_cv left right))),refs)
Proof
  strip_tac
  >> irule bounded_case16594_object_interval_add_argument_results
  >> simp
       [bounded_case16594_packed_interval_mul_encoded,
        compute_boundedCase16594ObjectInverseCoreCongruenceTheory.bounded_case16594_object_q_interval_mul_eval]
QED

Theorem bounded_case16594_object_products_sum4_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_products_sum4» =
    SOME
      ([«first_left»;«first_right»;«second_left»;«second_right»;
        «third_left»;«third_right»;«fourth_left»;«fourth_right»],
       bounded_case16594_object_products_sum4_body)
Proof
  rw [bounded_case16594_object_products_sum4_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_products_sum4_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_products_sum4»
        [from_cv first_left;from_cv first_right;
         from_cv second_left;from_cv second_right;
         from_cv third_left;from_cv third_right;
         from_cv fourth_left;from_cv fourth_right]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«first_left»,from_cv first_left);
         («first_right»,from_cv first_right);
         («second_left»,from_cv second_left);
         («second_right»,from_cv second_right);
         («third_left»,from_cv third_left);
         («third_right»,from_cv third_right);
         («fourth_left»,from_cv fourth_left);
         («fourth_right»,from_cv fourth_right)]
        bounded_case16594_object_products_sum4_body) refs
Proof
  strip_tac
  >> irule bounded_case16594_object_compute_eval_literal_app8
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_products_sum4_lookup
QED

Theorem bounded_case16594_object_products_sum4_eval:
  bounded_packed_q_interval_encoded first_left /\
  bounded_packed_q_interval_encoded first_right /\
  bounded_packed_q_interval_encoded second_left /\
  bounded_packed_q_interval_encoded second_right /\
  bounded_packed_q_interval_encoded third_left /\
  bounded_packed_q_interval_encoded third_right /\
  bounded_packed_q_interval_encoded fourth_left /\
  bounded_packed_q_interval_encoded fourth_right /\
  16 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_products_sum4»
        [from_cv first_left;from_cv first_right;
         from_cv second_left;from_cv second_right;
         from_cv third_left;from_cv third_right;
         from_cv fourth_left;from_cv fourth_right]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_interval_products_sum_acc_cv
          [(first_left,first_right);(second_left,second_right);
           (third_left,third_right);(fourth_left,fourth_right)]
          (bounded_analytic_source_q_interval_cv 0 0 0))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_products_sum4_unfold]
  >> simp
       [bounded_case16594_object_products_sum4_body_def,
        compute_evalTheory.subst_def]
  >> PURE_REWRITE_TAC
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_products_sum_acc_cv_def]
  >> simp []
  >> irule bounded_case16594_object_interval_accumulate_product_eval
  >> simp
       [bounded_case16594_packed_interval_add_encoded,
        bounded_case16594_packed_interval_mul_encoded,
        bounded_case16594_packed_zero_interval_encoded]
  >> irule bounded_case16594_object_interval_accumulate_product_eval
  >> simp
       [bounded_case16594_packed_interval_add_encoded,
        bounded_case16594_packed_interval_mul_encoded,
        bounded_case16594_packed_zero_interval_encoded]
  >> irule bounded_case16594_object_interval_accumulate_product_eval
  >> simp
       [bounded_case16594_packed_interval_add_encoded,
        bounded_case16594_packed_interval_mul_encoded,
        bounded_case16594_packed_zero_interval_encoded]
  >> irule bounded_case16594_object_interval_accumulate_product_eval
  >> simp
       [bounded_case16594_packed_interval_object_encoded,
        bounded_case16594_object_interval_packed_encoded,
        bounded_case16594_object_zero_interval_eval]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_hessian6_row_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_hessian6_row» =
    SOME ([«selector»],bounded_case16594_object_hessian6_row_body)
Proof
  rw [bounded_case16594_object_hessian6_row_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_hessian6_col_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_hessian6_col» =
    SOME ([«selector»],bounded_case16594_object_hessian6_col_body)
Proof
  rw [bounded_case16594_object_hessian6_col_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_hessian6_row_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_hessian6_row»
        [from_cv (compute_exec$Num selector)]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«selector»,from_cv (compute_exec$Num selector))]
        bounded_case16594_object_hessian6_row_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_hessian6_row_lookup
QED

Theorem bounded_case16594_object_hessian6_col_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_hessian6_col»
        [from_cv (compute_exec$Num selector)]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«selector»,from_cv (compute_exec$Num selector))]
        bounded_case16594_object_hessian6_col_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_hessian6_col_lookup
QED

Theorem bounded_case16594_object_hessian6_row_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_hessian6_row»
        [from_cv (compute_exec$Num selector)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (compute_exec$Num
          (bounded_case16594_object_hessian6_row_index selector))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_hessian6_row_unfold]
  >> simp
       [bounded_case16594_object_hessian6_row_body_def,
        bounded_case16594_object_hessian6_row_index_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_reln_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> fs []
QED

Theorem bounded_case16594_object_hessian6_col_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_hessian6_col»
        [from_cv (compute_exec$Num selector)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (compute_exec$Num
          (bounded_case16594_object_hessian6_col_index selector))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_hessian6_col_unfold]
  >> simp
       [bounded_case16594_object_hessian6_col_body_def,
        bounded_case16594_object_hessian6_col_index_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> fs []
QED

Theorem bounded_case16594_object_hessian6_indices_in_range:
  selector < 21 ==>
  bounded_case16594_object_hessian6_row_index selector < 6 /\
  bounded_case16594_object_hessian6_col_index selector < 6
Proof
  rw
    [bounded_case16594_object_hessian6_row_index_def,
     bounded_case16594_object_hessian6_col_index_def]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
