(*****************************************************************************
 * Exact evaluator semantics for the complete fixed six-dimensional
 * multiplication Hessian.  The runtime builds the 21 packed entries in
 * 6 + 6 + 6 + 3 blocks and joins them with a recursive append.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectMulHessianCompleteEval
Ancestors
  compute_boundedCase16594ObjectMulHessianEntryEval
  compute_boundedCase16594ObjectDispatchProgramTraceEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_mul_hessian6_block6_cv_def:
  bounded_case16594_object_mul_hessian6_block6_cv
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian selector =
    [bounded_case16594_object_mul_hessian6_entry_cv
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian selector;
     bounded_case16594_object_mul_hessian6_entry_cv
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 1);
     bounded_case16594_object_mul_hessian6_entry_cv
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 2);
     bounded_case16594_object_mul_hessian6_entry_cv
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 3);
     bounded_case16594_object_mul_hessian6_entry_cv
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 4);
     bounded_case16594_object_mul_hessian6_entry_cv
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 5)]
End

Definition bounded_case16594_object_mul_hessian6_block3_cv_def:
  bounded_case16594_object_mul_hessian6_block3_cv
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian selector =
    [bounded_case16594_object_mul_hessian6_entry_cv
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian selector;
     bounded_case16594_object_mul_hessian6_entry_cv
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 1);
     bounded_case16594_object_mul_hessian6_entry_cv
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 2)]
End

Definition bounded_case16594_object_mul_hessian6_entries_cv_def:
  bounded_case16594_object_mul_hessian6_entries_cv
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian =
    bounded_case16594_object_mul_hessian6_block6_cv
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian 0 ++
    (bounded_case16594_object_mul_hessian6_block6_cv
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian 6 ++
    (bounded_case16594_object_mul_hessian6_block6_cv
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian 12 ++
     bounded_case16594_object_mul_hessian6_block3_cv
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian 18))
End

Theorem bounded_case16594_object_mul_hessian6_entries_semantic:
  LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
  LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 ==>
  bounded_case16594_object_mul_hessian6_entries_cv
    left_value right_value left_gradient right_gradient
    left_hessian right_hessian =
  bounded_object_q_interval_fused_hessian_cv
    left_value right_value left_hessian right_hessian
    (bounded_object_q_symmetric_product_pairs_cv
      left_gradient right_gradient)
Proof
  rw [listTheory.LENGTH_EQ_NUM_compute]
  >> simp
       [bounded_case16594_object_mul_hessian6_entries_cv_def,
        bounded_case16594_object_mul_hessian6_block6_cv_def,
        bounded_case16594_object_mul_hessian6_block3_cv_def,
        bounded_case16594_object_mul_hessian6_entry_cv_def,
        compute_boundedCase16594ObjectMulHessianEvalTheory.bounded_case16594_object_hessian6_row_index_def,
        compute_boundedCase16594ObjectMulHessianEvalTheory.bounded_case16594_object_hessian6_col_index_def,
        compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_cv_def,
        compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_row_cv_def,
        compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_hessian_cv_def]
QED

Definition bounded_case16594_object_mul_hessian6_entry_exp_def:
  bounded_case16594_object_mul_hessian6_entry_exp selector_expression =
    App «candle_cv_q_packed_object_mul_hessian6_entry_index»
      [Var «left_value»;Var «right_value»;
       Var «left_gradient»;Var «right_gradient»;
       Var «left_hessian»;Var «right_hessian»;
       selector_expression]
End

Definition bounded_case16594_object_mul_hessian6_block6_body_def:
  bounded_case16594_object_mul_hessian6_block6_body =
    App «candle_cv_q_packed_delta_six»
      [bounded_case16594_object_mul_hessian6_entry_exp (Var «selector»);
       bounded_case16594_object_mul_hessian6_entry_exp
         (Binop Add (Var «selector») (Num 1));
       bounded_case16594_object_mul_hessian6_entry_exp
         (Binop Add (Var «selector») (Num 2));
       bounded_case16594_object_mul_hessian6_entry_exp
         (Binop Add (Var «selector») (Num 3));
       bounded_case16594_object_mul_hessian6_entry_exp
         (Binop Add (Var «selector») (Num 4));
       bounded_case16594_object_mul_hessian6_entry_exp
         (Binop Add (Var «selector») (Num 5))]
End

Definition bounded_case16594_object_mul_hessian6_block3_body_def:
  bounded_case16594_object_mul_hessian6_block3_body =
    Pair
      (bounded_case16594_object_mul_hessian6_entry_exp (Var «selector»))
      (Pair
        (bounded_case16594_object_mul_hessian6_entry_exp
          (Binop Add (Var «selector») (Num 1)))
        (Pair
          (bounded_case16594_object_mul_hessian6_entry_exp
            (Binop Add (Var «selector») (Num 2)))
          (Num 0)))
End

Definition bounded_case16594_object_interval_list_append_body_def:
  bounded_case16594_object_interval_list_append_body =
    If (Uop Ispair (Var «left»))
      (Pair (Uop Fst (Var «left»))
        (App «candle_cv_q_packed_object_interval_list_append»
          [Uop Snd (Var «left»);Var «right»]))
      (Var «right»)
End

Definition bounded_case16594_object_mul_hessian6_block_exp_def:
  bounded_case16594_object_mul_hessian6_block_exp function_name selector =
    App function_name
      [Var «left_value»;Var «right_value»;
       Var «left_gradient»;Var «right_gradient»;
       Var «left_hessian»;Var «right_hessian»;Num selector]
End

Definition bounded_case16594_object_mul_hessian6_entries_body_def:
  bounded_case16594_object_mul_hessian6_entries_body =
    App «candle_cv_q_packed_object_interval_list_append»
      [bounded_case16594_object_mul_hessian6_block_exp
         «candle_cv_q_packed_object_mul_hessian6_block6» 0;
       App «candle_cv_q_packed_object_interval_list_append»
        [bounded_case16594_object_mul_hessian6_block_exp
           «candle_cv_q_packed_object_mul_hessian6_block6» 6;
         App «candle_cv_q_packed_object_interval_list_append»
          [bounded_case16594_object_mul_hessian6_block_exp
             «candle_cv_q_packed_object_mul_hessian6_block6» 12;
           bounded_case16594_object_mul_hessian6_block_exp
             «candle_cv_q_packed_object_mul_hessian6_block3» 18]]]
End

Definition bounded_case16594_object_mul_hessian6_body_def:
  bounded_case16594_object_mul_hessian6_body =
    App «candle_cv_q_packed_object_mul_hessian6_entries»
      [Var «left_value»;Var «right_value»;
       Var «left_gradient»;Var «right_gradient»;
       Var «left_hessian»;Var «right_hessian»]
End

Theorem bounded_case16594_object_compute_eval_source_num:
  compute_eval clock ceqs (compute_syntax$Num n) (refs:hol_refs) =
    (M_success (from_cv (compute_exec$Num n)),refs)
Proof
  simp
    [compute_execTheory.from_cv_def,
     Once compute_evalTheory.compute_eval_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_source_num_add:
  compute_eval clock ceqs
      (Binop Add (compute_syntax$Num left) (compute_syntax$Num right))
      (refs:hol_refs) =
    (M_success (from_cv (compute_exec$Num (left + right))),refs)
Proof
  simp
    [compute_execTheory.from_cv_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_arith_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_source_num_as_from_cv:
  compute_syntax$Num n = from_cv (compute_exec$Num n)
Proof
  simp [compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_object_mul_hessian6_entry_index_argument_result:
  bounded_packed_q_interval_encoded left_value /\
  bounded_packed_q_interval_encoded right_value /\
  EVERY bounded_packed_q_interval_encoded left_gradient /\
  EVERY bounded_packed_q_interval_encoded right_gradient /\
  EVERY bounded_packed_q_interval_encoded left_hessian /\
  EVERY bounded_packed_q_interval_encoded right_hessian /\
  LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
  LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
  selector < 21 /\ 256 < clock /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    selector_expression (refs:hol_refs) =
      (M_success (from_cv (compute_exec$Num selector)),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_mul_hessian6_entry_index»
        [from_cv left_value;from_cv right_value;
         from_cv (bounded_object_q_cv_list left_gradient);
         from_cv (bounded_object_q_cv_list right_gradient);
         from_cv (bounded_object_q_cv_list left_hessian);
         from_cv (bounded_object_q_cv_list right_hessian);
         selector_expression]) refs =
    (M_success
      (from_cv
        (bounded_case16594_object_mul_hessian6_entry_cv
          left_value right_value left_gradient right_gradient
          left_hessian right_hessian selector)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_mul_hessian6_entry_index»
            [from_cv left_value;from_cv right_value;
             from_cv (bounded_object_q_cv_list left_gradient);
             from_cv (bounded_object_q_cv_list right_gradient);
             from_cv (bounded_object_q_cv_list left_hessian);
             from_cv (bounded_object_q_cv_list right_hessian);
             from_cv (compute_exec$Num selector)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_app7_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_mul_hessian6_entry_index_eval
  >> simp []
QED

Theorem bounded_case16594_object_mul_hessian6_block6_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_mul_hessian6_block6» =
    SOME
      ([«left_value»;«right_value»;«left_gradient»;«right_gradient»;
        «left_hessian»;«right_hessian»;«selector»],
       bounded_case16594_object_mul_hessian6_block6_body)
Proof
  rw [bounded_case16594_object_mul_hessian6_block6_body_def,
      bounded_case16594_object_mul_hessian6_entry_exp_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_mul_hessian6_block3_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_mul_hessian6_block3» =
    SOME
      ([«left_value»;«right_value»;«left_gradient»;«right_gradient»;
        «left_hessian»;«right_hessian»;«selector»],
       bounded_case16594_object_mul_hessian6_block3_body)
Proof
  rw [bounded_case16594_object_mul_hessian6_block3_body_def,
      bounded_case16594_object_mul_hessian6_entry_exp_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_interval_list_append_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_interval_list_append» =
    SOME
      ([«left»;«right»],bounded_case16594_object_interval_list_append_body)
Proof
  rw [bounded_case16594_object_interval_list_append_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_mul_hessian6_entries_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_mul_hessian6_entries» =
    SOME
      ([«left_value»;«right_value»;«left_gradient»;«right_gradient»;
        «left_hessian»;«right_hessian»],
       bounded_case16594_object_mul_hessian6_entries_body)
Proof
  rw [bounded_case16594_object_mul_hessian6_entries_body_def,
      bounded_case16594_object_mul_hessian6_block_exp_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_mul_hessian6_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_mul_hessian6» =
    SOME
      ([«left_value»;«right_value»;«left_gradient»;«right_gradient»;
        «left_hessian»;«right_hessian»],
       bounded_case16594_object_mul_hessian6_body)
Proof
  rw [bounded_case16594_object_mul_hessian6_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_mul_hessian6_block6_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_mul_hessian6_block6»
        [from_cv left_value;from_cv right_value;
         from_cv left_gradient;from_cv right_gradient;
         from_cv left_hessian;from_cv right_hessian;
         from_cv (compute_exec$Num selector)]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«left_value»,from_cv left_value);(«right_value»,from_cv right_value);
         («left_gradient»,from_cv left_gradient);(«right_gradient»,from_cv right_gradient);
         («left_hessian»,from_cv left_hessian);(«right_hessian»,from_cv right_hessian);
         («selector»,from_cv (compute_exec$Num selector))]
        bounded_case16594_object_mul_hessian6_block6_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_literal_app7
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_mul_hessian6_block6_lookup
QED

Theorem bounded_case16594_object_mul_hessian6_block3_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_mul_hessian6_block3»
        [from_cv left_value;from_cv right_value;
         from_cv left_gradient;from_cv right_gradient;
         from_cv left_hessian;from_cv right_hessian;
         from_cv (compute_exec$Num selector)]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«left_value»,from_cv left_value);(«right_value»,from_cv right_value);
         («left_gradient»,from_cv left_gradient);(«right_gradient»,from_cv right_gradient);
         («left_hessian»,from_cv left_hessian);(«right_hessian»,from_cv right_hessian);
         («selector»,from_cv (compute_exec$Num selector))]
        bounded_case16594_object_mul_hessian6_block3_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_literal_app7
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_mul_hessian6_block3_lookup
QED

Theorem bounded_case16594_object_interval_list_append_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_append»
        [from_cv left;from_cv right]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«left»,from_cv left);(«right»,from_cv right)]
        bounded_case16594_object_interval_list_append_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_interval_list_append_lookup
QED

Theorem bounded_case16594_object_mul_hessian6_entries_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_mul_hessian6_entries»
        [from_cv left_value;from_cv right_value;
         from_cv left_gradient;from_cv right_gradient;
         from_cv left_hessian;from_cv right_hessian]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«left_value»,from_cv left_value);(«right_value»,from_cv right_value);
         («left_gradient»,from_cv left_gradient);(«right_gradient»,from_cv right_gradient);
         («left_hessian»,from_cv left_hessian);(«right_hessian»,from_cv right_hessian)]
        bounded_case16594_object_mul_hessian6_entries_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_mul_hessian6_entries_lookup
QED

Theorem bounded_case16594_object_mul_hessian6_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_mul_hessian6»
        [from_cv left_value;from_cv right_value;
         from_cv left_gradient;from_cv right_gradient;
         from_cv left_hessian;from_cv right_hessian]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«left_value»,from_cv left_value);(«right_value»,from_cv right_value);
         («left_gradient»,from_cv left_gradient);(«right_gradient»,from_cv right_gradient);
         («left_hessian»,from_cv left_hessian);(«right_hessian»,from_cv right_hessian)]
        bounded_case16594_object_mul_hessian6_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_mul_hessian6_lookup
QED

Theorem bounded_case16594_object_interval_list_append_nil_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_append»
        [from_cv (compute_exec$Num 0);from_cv right]) (refs:hol_refs) =
    (M_success (from_cv right),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_interval_list_append_unfold]
  >> simp
       [bounded_case16594_object_interval_list_append_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_interval_list_append_cons_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_append»
        [from_cv left_rest;from_cv right]) (refs:hol_refs) =
    (M_success (from_cv result_rest),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_append»
        [from_cv (compute_exec$Pair left_entry left_rest);from_cv right]) refs =
    (M_success (from_cv (compute_exec$Pair left_entry result_rest)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_interval_list_append_unfold]
  >> simp
       [bounded_case16594_object_interval_list_append_body_def,
        compute_evalTheory.subst_def,
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_if_ispair_pair_components]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_pair_fst_components]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_interval_list_append»
            [from_cv left_rest;from_cv right]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_pair_snd_components]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_interval_list_append_eval:
  !left right clock refs.
    LENGTH left + 1 < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_append»
        [from_cv (bounded_object_q_cv_list left);
         from_cv (bounded_object_q_cv_list right)]) (refs:hol_refs) =
      (M_success
        (from_cv (bounded_object_q_cv_list (left ++ right))),refs)
Proof
  Induct_on `left`
  >- (rpt strip_tac
      >> simp
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             bounded_case16594_object_interval_list_append_nil_eval)
      >> intLib.ARITH_TAC)
  >> rpt strip_tac
  >> PURE_REWRITE_TAC
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        listTheory.APPEND]
  >> irule bounded_case16594_object_interval_list_append_cons_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> qpat_x_assum `!right clock refs. _`
       (qspecl_then [`right`,`clock - 1`,`refs`] mp_tac)
  >> impl_tac >- (fs [] >> intLib.ARITH_TAC)
  >> simp []
QED

Theorem bounded_case16594_object_interval_list_append_argument_results:
  LENGTH left + 1 < clock /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      left_expression (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_cv_list left)),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      right_expression refs =
    (M_success (from_cv (bounded_object_q_cv_list right)),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_append»
        [left_expression;right_expression]) refs =
    (M_success
      (from_cv (bounded_object_q_cv_list (left ++ right))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_interval_list_append»
            [from_cv (bounded_object_q_cv_list left);
             from_cv (bounded_object_q_cv_list right)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp [])
  >> irule bounded_case16594_object_interval_list_append_eval
  >> simp []
QED

Theorem bounded_case16594_object_mul_hessian6_block6_eval:
  bounded_packed_q_interval_encoded left_value /\
  bounded_packed_q_interval_encoded right_value /\
  EVERY bounded_packed_q_interval_encoded left_gradient /\
  EVERY bounded_packed_q_interval_encoded right_gradient /\
  EVERY bounded_packed_q_interval_encoded left_hessian /\
  EVERY bounded_packed_q_interval_encoded right_hessian /\
  LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
  LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
  selector + 5 < 21 /\ 260 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_mul_hessian6_block6»
        [from_cv left_value;from_cv right_value;
         from_cv (bounded_object_q_cv_list left_gradient);
         from_cv (bounded_object_q_cv_list right_gradient);
         from_cv (bounded_object_q_cv_list left_hessian);
         from_cv (bounded_object_q_cv_list right_hessian);
         from_cv (compute_exec$Num selector)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_case16594_object_mul_hessian6_block6_cv
            left_value right_value left_gradient right_gradient
            left_hessian right_hessian selector))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_mul_hessian6_block6_unfold]
  >> simp
       [bounded_case16594_object_mul_hessian6_block6_body_def,
        bounded_case16594_object_mul_hessian6_entry_exp_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_six»
            [from_cv
               (bounded_case16594_object_mul_hessian6_entry_cv
                 left_value right_value left_gradient right_gradient
                 left_hessian right_hessian selector);
             from_cv
               (bounded_case16594_object_mul_hessian6_entry_cv
                 left_value right_value left_gradient right_gradient
                 left_hessian right_hessian (selector + 1));
             from_cv
               (bounded_case16594_object_mul_hessian6_entry_cv
                 left_value right_value left_gradient right_gradient
                 left_hessian right_hessian (selector + 2));
             from_cv
               (bounded_case16594_object_mul_hessian6_entry_cv
                 left_value right_value left_gradient right_gradient
                 left_hessian right_hessian (selector + 3));
             from_cv
               (bounded_case16594_object_mul_hessian6_entry_cv
                 left_value right_value left_gradient right_gradient
                 left_hessian right_hessian (selector + 4));
             from_cv
               (bounded_case16594_object_mul_hessian6_entry_cv
                 left_value right_value left_gradient right_gradient
                 left_hessian right_hessian (selector + 5))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_app6_argument_results
      >> simp
           [bounded_case16594_object_mul_hessian6_entry_index_argument_result,
            compute_boundedPackedObjectFinishEvalTheory.bounded_packed_compute_eval_binop_add_num_results,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_binop_def,
            compute_evalTheory.do_arith_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> intLib.ARITH_TAC)
  >> rw [bounded_case16594_object_mul_hessian6_block6_cv_def]
  >> irule
       compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_delta_six_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_mul_hessian6_block3_eval:
  bounded_packed_q_interval_encoded left_value /\
  bounded_packed_q_interval_encoded right_value /\
  EVERY bounded_packed_q_interval_encoded left_gradient /\
  EVERY bounded_packed_q_interval_encoded right_gradient /\
  EVERY bounded_packed_q_interval_encoded left_hessian /\
  EVERY bounded_packed_q_interval_encoded right_hessian /\
  LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
  LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
  selector + 2 < 21 /\ 260 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_mul_hessian6_block3»
        [from_cv left_value;from_cv right_value;
         from_cv (bounded_object_q_cv_list left_gradient);
         from_cv (bounded_object_q_cv_list right_gradient);
         from_cv (bounded_object_q_cv_list left_hessian);
         from_cv (bounded_object_q_cv_list right_hessian);
         from_cv (compute_exec$Num selector)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_case16594_object_mul_hessian6_block3_cv
            left_value right_value left_gradient right_gradient
            left_hessian right_hessian selector))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_mul_hessian6_block3_unfold]
  >> simp
       [bounded_case16594_object_mul_hessian6_block3_body_def,
        bounded_case16594_object_mul_hessian6_entry_exp_def,
        bounded_case16594_object_mul_hessian6_block3_cv_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (irule bounded_case16594_object_mul_hessian6_entry_index_argument_result
      >> simp [bounded_case16594_object_compute_eval_source_num]
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (irule bounded_case16594_object_mul_hessian6_entry_index_argument_result
      >> simp [bounded_case16594_object_compute_eval_source_num_add]
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (irule bounded_case16594_object_mul_hessian6_entry_index_argument_result
      >> simp [bounded_case16594_object_compute_eval_source_num_add]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_mul_hessian6_entries_eval:
  bounded_packed_q_interval_encoded left_value /\
  bounded_packed_q_interval_encoded right_value /\
  EVERY bounded_packed_q_interval_encoded left_gradient /\
  EVERY bounded_packed_q_interval_encoded right_gradient /\
  EVERY bounded_packed_q_interval_encoded left_hessian /\
  EVERY bounded_packed_q_interval_encoded right_hessian /\
  LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
  LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
  264 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_mul_hessian6_entries»
        [from_cv left_value;from_cv right_value;
         from_cv (bounded_object_q_cv_list left_gradient);
         from_cv (bounded_object_q_cv_list right_gradient);
         from_cv (bounded_object_q_cv_list left_hessian);
         from_cv (bounded_object_q_cv_list right_hessian)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_case16594_object_mul_hessian6_entries_cv
            left_value right_value left_gradient right_gradient
            left_hessian right_hessian))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_mul_hessian6_entries_unfold]
  >> simp
       [bounded_case16594_object_mul_hessian6_entries_body_def,
        bounded_case16594_object_mul_hessian6_block_exp_def,
        compute_evalTheory.subst_def]
  >> PURE_REWRITE_TAC [bounded_case16594_object_source_num_as_from_cv]
  >> PURE_REWRITE_TAC [bounded_case16594_object_mul_hessian6_entries_cv_def]
  >> irule bounded_case16594_object_interval_list_append_argument_results
  >> conj_tac
  >- (simp [bounded_case16594_object_mul_hessian6_block6_cv_def]
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule bounded_case16594_object_mul_hessian6_block6_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_interval_list_append_argument_results
  >> conj_tac
  >- (simp [bounded_case16594_object_mul_hessian6_block6_cv_def]
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule bounded_case16594_object_mul_hessian6_block6_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_interval_list_append_argument_results
  >> conj_tac
  >- (simp [bounded_case16594_object_mul_hessian6_block6_cv_def]
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule bounded_case16594_object_mul_hessian6_block6_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_mul_hessian6_block3_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_mul_hessian6_semantic_eval:
  bounded_packed_q_interval_encoded left_value /\
  bounded_packed_q_interval_encoded right_value /\
  EVERY bounded_packed_q_interval_encoded left_gradient /\
  EVERY bounded_packed_q_interval_encoded right_gradient /\
  EVERY bounded_packed_q_interval_encoded left_hessian /\
  EVERY bounded_packed_q_interval_encoded right_hessian /\
  LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
  LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
  266 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_mul_hessian6»
        [from_cv left_value;from_cv right_value;
         from_cv (bounded_object_q_cv_list left_gradient);
         from_cv (bounded_object_q_cv_list right_gradient);
         from_cv (bounded_object_q_cv_list left_hessian);
         from_cv (bounded_object_q_cv_list right_hessian)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_object_q_interval_fused_hessian_cv
            left_value right_value left_hessian right_hessian
            (bounded_object_q_symmetric_product_pairs_cv
              left_gradient right_gradient)))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_mul_hessian6_unfold]
  >> simp
       [bounded_case16594_object_mul_hessian6_body_def,
        compute_evalTheory.subst_def]
  >> rw [GSYM bounded_case16594_object_mul_hessian6_entries_semantic]
  >> irule bounded_case16594_object_mul_hessian6_entries_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
