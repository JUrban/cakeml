(*****************************************************************************
 * Exact evaluator semantics for one packed multiplication-Hessian entry.
 * The entry theorem is generic in the six gradient and 21 Hessian entries;
 * later block/list theorems instantiate it for selectors 0 through 20.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectMulHessianEntryEval
Ancestors
  compute_boundedCase16594ObjectMulHessianEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_mul_hessian6_entry_index_body_def:
  bounded_case16594_object_mul_hessian6_entry_index_body =
    App «candle_cv_q_packed_object_products_sum4»
      [Var «right_value»;
       App «candle_cv_q_interval_lookup»
         [Var «selector»;Var «left_hessian»];
       App «candle_cv_q_interval_lookup»
         [App «candle_cv_q_packed_object_hessian6_row» [Var «selector»];
          Var «left_gradient»];
       App «candle_cv_q_interval_lookup»
         [App «candle_cv_q_packed_object_hessian6_col» [Var «selector»];
          Var «right_gradient»];
       App «candle_cv_q_interval_lookup»
         [App «candle_cv_q_packed_object_hessian6_row» [Var «selector»];
          Var «right_gradient»];
       App «candle_cv_q_interval_lookup»
         [App «candle_cv_q_packed_object_hessian6_col» [Var «selector»];
          Var «left_gradient»];
       Var «left_value»;
       App «candle_cv_q_interval_lookup»
         [Var «selector»;Var «right_hessian»]]
End

Definition bounded_case16594_object_mul_hessian6_entry_cv_def:
  bounded_case16594_object_mul_hessian6_entry_cv
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian selector =
    bounded_object_q_interval_products_sum_acc_cv
      [(right_value,EL selector left_hessian);
       (EL (bounded_case16594_object_hessian6_row_index selector)
          left_gradient,
        EL (bounded_case16594_object_hessian6_col_index selector)
          right_gradient);
       (EL (bounded_case16594_object_hessian6_row_index selector)
          right_gradient,
        EL (bounded_case16594_object_hessian6_col_index selector)
          left_gradient);
       (left_value,EL selector right_hessian)]
      (bounded_analytic_source_q_interval_cv 0 0 0)
End

Theorem bounded_case16594_object_compute_eval_app8_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) /\
  compute_eval clock ceqs argument3 refs =
      (M_success (from_cv result3),refs) /\
  compute_eval clock ceqs argument4 refs =
      (M_success (from_cv result4),refs) /\
  compute_eval clock ceqs argument5 refs =
      (M_success (from_cv result5),refs) /\
  compute_eval clock ceqs argument6 refs =
      (M_success (from_cv result6),refs) /\
  compute_eval clock ceqs argument7 refs =
      (M_success (from_cv result7),refs) /\
  compute_eval clock ceqs argument8 refs =
      (M_success (from_cv result8),refs) ==>
  compute_eval clock ceqs
      (App function_name
        [argument1;argument2;argument3;argument4;argument5;argument6;
         argument7;argument8]) refs =
    compute_eval clock ceqs
      (App function_name
        [from_cv result1;from_cv result2;from_cv result3;from_cv result4;
         from_cv result5;from_cv result6;from_cv result7;from_cv result8]) refs
Proof
  Cases_on `clock`
  >> simp []
  >> strip_tac
  >> Cases_on `ALOOKUP ceqs function_name`
  >- simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `x`
  >> Cases_on `LENGTH q = 8`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_mul_hessian6_entry_index_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_mul_hessian6_entry_index» =
    SOME
      ([«left_value»;«right_value»;«left_gradient»;«right_gradient»;
        «left_hessian»;«right_hessian»;«selector»],
       bounded_case16594_object_mul_hessian6_entry_index_body)
Proof
  rw [bounded_case16594_object_mul_hessian6_entry_index_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_mul_hessian6_entry_index_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_mul_hessian6_entry_index»
        [from_cv left_value;from_cv right_value;
         from_cv (bounded_object_q_cv_list left_gradient);
         from_cv (bounded_object_q_cv_list right_gradient);
         from_cv (bounded_object_q_cv_list left_hessian);
         from_cv (bounded_object_q_cv_list right_hessian);
         from_cv (compute_exec$Num selector)]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«left_value»,from_cv left_value);
         («right_value»,from_cv right_value);
         («left_gradient»,from_cv (bounded_object_q_cv_list left_gradient));
         («right_gradient»,from_cv (bounded_object_q_cv_list right_gradient));
         («left_hessian»,from_cv (bounded_object_q_cv_list left_hessian));
         («right_hessian»,from_cv (bounded_object_q_cv_list right_hessian));
         («selector»,from_cv (compute_exec$Num selector))]
        bounded_case16594_object_mul_hessian6_entry_index_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_literal_app7
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_mul_hessian6_entry_index_lookup
QED

Theorem bounded_case16594_object_hessian6_row_source_num_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_hessian6_row»
        [compute_syntax$Num selector]) (refs:hol_refs) =
    (M_success
      (from_cv
        (compute_exec$Num
          (bounded_case16594_object_hessian6_row_index selector))),refs)
Proof
  simp
    [compute_execTheory.from_cv_def,
     SIMP_RULE std_ss [compute_execTheory.from_cv_def]
       bounded_case16594_object_hessian6_row_eval]
QED

Theorem bounded_case16594_object_hessian6_col_source_num_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_hessian6_col»
        [compute_syntax$Num selector]) (refs:hol_refs) =
    (M_success
      (from_cv
        (compute_exec$Num
          (bounded_case16594_object_hessian6_col_index selector))),refs)
Proof
  simp
    [compute_execTheory.from_cv_def,
     SIMP_RULE std_ss [compute_execTheory.from_cv_def]
       bounded_case16594_object_hessian6_col_eval]
QED

Theorem bounded_case16594_object_hessian6_row_lookup_el_eval:
  selector < 21 /\ LENGTH items = 6 /\ 32 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_lookup»
        [App «candle_cv_q_packed_object_hessian6_row»
           [compute_syntax$Num selector];
         from_cv (bounded_object_q_cv_list items)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (EL (bounded_case16594_object_hessian6_row_index selector) items)),
     refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_lookup»
            [from_cv
               (compute_exec$Num
                 (bounded_case16594_object_hessian6_row_index selector));
             from_cv (bounded_object_q_cv_list items)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            bounded_case16594_object_hessian6_row_source_num_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_execTheory.from_cv_def]
  >> irule
       compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
  >> simp [bounded_case16594_object_hessian6_row_index_def]
  >> every_case_tac
  >> fs []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_hessian6_col_lookup_el_eval:
  selector < 21 /\ LENGTH items = 6 /\ 32 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_lookup»
        [App «candle_cv_q_packed_object_hessian6_col»
           [compute_syntax$Num selector];
         from_cv (bounded_object_q_cv_list items)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (EL (bounded_case16594_object_hessian6_col_index selector) items)),
     refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_lookup»
            [from_cv
               (compute_exec$Num
                 (bounded_case16594_object_hessian6_col_index selector));
             from_cv (bounded_object_q_cv_list items)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            bounded_case16594_object_hessian6_col_source_num_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_execTheory.from_cv_def]
  >> irule
       compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
  >> simp [bounded_case16594_object_hessian6_col_index_def]
  >> every_case_tac
  >> fs []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_mul_hessian6_entry_index_eval:
  bounded_packed_q_interval_encoded left_value /\
  bounded_packed_q_interval_encoded right_value /\
  EVERY bounded_packed_q_interval_encoded left_gradient /\
  EVERY bounded_packed_q_interval_encoded right_gradient /\
  EVERY bounded_packed_q_interval_encoded left_hessian /\
  EVERY bounded_packed_q_interval_encoded right_hessian /\
  LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
  LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
  selector < 21 /\ 256 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_mul_hessian6_entry_index»
        [from_cv left_value;from_cv right_value;
         from_cv (bounded_object_q_cv_list left_gradient);
         from_cv (bounded_object_q_cv_list right_gradient);
         from_cv (bounded_object_q_cv_list left_hessian);
         from_cv (bounded_object_q_cv_list right_hessian);
         from_cv (compute_exec$Num selector)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_mul_hessian6_entry_cv
          left_value right_value left_gradient right_gradient
          left_hessian right_hessian selector)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_mul_hessian6_entry_index_unfold]
  >> simp
       [bounded_case16594_object_mul_hessian6_entry_index_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_products_sum4»
            [from_cv right_value;
             from_cv (EL selector left_hessian);
             from_cv
               (EL (bounded_case16594_object_hessian6_row_index selector)
                 left_gradient);
             from_cv
               (EL (bounded_case16594_object_hessian6_col_index selector)
                 right_gradient);
             from_cv
               (EL (bounded_case16594_object_hessian6_row_index selector)
                 right_gradient);
             from_cv
               (EL (bounded_case16594_object_hessian6_col_index selector)
                 left_gradient);
             from_cv left_value;
             from_cv (EL selector right_hessian)]) refs`
  >> conj_tac
  >- (`32 < clock - 1` by intLib.ARITH_TAC
      >> `selector + 2 < clock - 1` by intLib.ARITH_TAC
      >> irule bounded_case16594_object_compute_eval_app8_argument_results
      >> simp
           [compute_execTheory.from_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval,
            bounded_case16594_object_hessian6_row_lookup_el_eval,
            bounded_case16594_object_hessian6_col_lookup_el_eval])
  >> rw [bounded_case16594_object_mul_hessian6_entry_cv_def]
  >> irule bounded_case16594_object_products_sum4_eval
  >> `bounded_case16594_object_hessian6_row_index selector < 6 /\
      bounded_case16594_object_hessian6_col_index selector < 6` by
       metis_tac [bounded_case16594_object_hessian6_indices_in_range]
  >> fs [EVERY_EL]
QED

val _ = export_theory ();
