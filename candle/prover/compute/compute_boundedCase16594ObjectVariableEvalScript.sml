(*****************************************************************************
 * Exact evaluator and semantic relation for production polynomial variables.
 *
 * The source constructs a six-entry unit gradient by recursively traversing
 * the supplied zero-gradient list.  These lemmas authenticate that recursion
 * once, then package the two lookups and the zero Hessian as one Taylor state.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectVariableEval
Ancestors
  compute_boundedCase16594ObjectPolyAddStepSemanticEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_interval_zeros_body_def:
  bounded_case16594_object_interval_zeros_body =
    If (Uop Ispair (Var «items»))
      (Pair (App «candle_cv_q_zero_interval» [])
        (App «candle_cv_q_dim_interval_zeros» [Uop Snd (Var «items»)]))
      (Num 0)
End

Definition bounded_case16594_object_interval_unit_body_def:
  bounded_case16594_object_interval_unit_body =
    If (Uop Ispair (Var «boxes»))
      (If (Uop Ispair (Var «variable»))
        (App «candle_cv_q_dim_interval_zeros» [Var «boxes»])
        (If (Binop Eq (Var «variable») (Num 0))
          (Pair (App «candle_cv_q_one_interval» [])
            (App «candle_cv_q_dim_interval_zeros» [Uop Snd (Var «boxes»)]))
          (Pair (App «candle_cv_q_zero_interval» [])
            (App «candle_cv_q_dim_interval_unit»
              [Binop Sub (Var «variable») (Num 1);
               Uop Snd (Var «boxes»)]))))
      (Num 0)
End

Definition bounded_case16594_object_one_interval_cv_def:
  bounded_case16594_object_one_interval_cv =
    bounded_analytic_source_q_interval_cv 1 0 0
End

Definition bounded_case16594_object_one_cv_def:
  bounded_case16594_object_one_cv =
    bounded_analytic_source_q_cv 1 0 0
End

Definition bounded_case16594_object_one_interval_body_def:
  bounded_case16594_object_one_interval_body =
    Pair (App «candle_cv_q_one» []) (App «candle_cv_q_one» [])
End

Definition bounded_case16594_object_interval_unit_cv_def:
  bounded_case16594_object_interval_unit_cv variable [] = [] /\
  bounded_case16594_object_interval_unit_cv 0 (item::items) =
    bounded_case16594_object_one_interval_cv::
      REPLICATE (LENGTH items) bounded_case16594_object_zero_interval_cv /\
  bounded_case16594_object_interval_unit_cv (SUC variable) (item::items) =
    bounded_case16594_object_zero_interval_cv::
      bounded_case16594_object_interval_unit_cv variable items
End

Theorem bounded_case16594_object_interval_shape_lookups:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_dim_interval_zeros» =
    SOME ([«items»],bounded_case16594_object_interval_zeros_body) /\
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_dim_interval_unit» =
    SOME
      ([«variable»;«boxes»],
       bounded_case16594_object_interval_unit_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_one_lookups:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_one» =
    SOME ([],from_cv bounded_case16594_object_one_cv) /\
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_one_interval» =
    SOME ([],bounded_case16594_object_one_interval_body)
Proof
  simp
    [bounded_case16594_object_one_cv_def,
     bounded_case16594_object_one_interval_body_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
     compute_execTheory.from_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_one_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_one» []) (refs:hol_refs) =
    (M_success (from_cv bounded_case16594_object_one_cv),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app0
  >> asm_rewrite_tac []
  >> fs [bounded_case16594_object_one_lookups]
QED

Theorem bounded_case16594_object_compute_eval_app0_unfold:
  0 < clock /\
  ALOOKUP ceqs function_name = SOME ([],body) ==>
  compute_eval clock ceqs (App function_name []) (refs:hol_refs) =
    compute_eval (clock - 1) ceqs body refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_one_interval_eval:
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_one_interval» []) (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_one_interval_cv),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          bounded_case16594_object_one_interval_body refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app0_unfold
      >> simp [bounded_case16594_object_one_lookups]
      >> intLib.ARITH_TAC)
  >> simp
       [bounded_case16594_object_one_interval_body_def,
        bounded_case16594_object_one_interval_cv_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> simp
       [bounded_case16594_object_one_eval,
        bounded_case16594_object_one_cv_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_interval_zeros_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_zeros» [from_cv items])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«items»,from_cv items)]
        bounded_case16594_object_interval_zeros_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> simp [bounded_case16594_object_interval_shape_lookups]
QED

Theorem bounded_case16594_object_interval_zeros_nil_eval:
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_zeros» [from_cv (Num 0)])
      (refs:hol_refs) =
    (M_success (from_cv (Num 0)),refs)
Proof
  strip_tac
  >> simp [bounded_case16594_object_interval_zeros_unfold]
  >> simp
       [bounded_case16594_object_interval_zeros_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_interval_zeros_cons_eval:
  3 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_zeros» [from_cv items])
      (refs:hol_refs) = (M_success (from_cv zeros),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_zeros»
        [from_cv (Pair item items)]) refs =
    (M_success
      (from_cv
        (Pair bounded_case16594_object_zero_interval_cv zeros)),refs)
Proof
  strip_tac
  >> simp [bounded_case16594_object_interval_zeros_unfold]
  >> simp
       [bounded_case16594_object_interval_zeros_body_def,
        compute_evalTheory.subst_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_if_ispair_from_cv_pair]
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_dim_interval_zeros»
          [Uop Snd (Pair (from_cv item) (from_cv items))]) refs =
      compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_dim_interval_zeros» [from_cv items]) refs` by
       (irule
          compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
        >> simp
             [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_snd])
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_zero_interval_eval,
        compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_zero_interval_identity]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_interval_zeros_eval:
  !items clock refs.
    4 * (LENGTH items + 1) < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_dim_interval_zeros»
          [from_cv (bounded_object_q_cv_list items)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_object_q_cv_list
            (REPLICATE (LENGTH items)
              bounded_case16594_object_zero_interval_cv))),refs)
Proof
  Induct_on `items`
  >- (rpt gen_tac
      >> strip_tac
      >> simp_tac std_ss
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            LENGTH,REPLICATE]
      >> irule bounded_case16594_object_interval_zeros_nil_eval
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> strip_tac
  >> PURE_REWRITE_TAC
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        LENGTH,REPLICATE]
  >> irule bounded_case16594_object_interval_zeros_cons_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> qpat_x_assum `!clock refs. _`
       (qspecl_then [`clock - 1`,`refs`] mp_tac)
  >> impl_tac
  >- (qpat_x_assum `4 * (LENGTH (h::items) + 1) < clock` mp_tac
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp []
QED

Theorem bounded_case16594_object_interval_unit_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_unit»
        [from_cv variable;from_cv items]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«variable»,from_cv variable);(«boxes»,from_cv items)]
        bounded_case16594_object_interval_unit_body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        bounded_case16594_object_interval_shape_lookups,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_object_interval_unit_num_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_unit»
        [Num variable;from_cv items]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«variable»,Num variable);(«boxes»,from_cv items)]
        bounded_case16594_object_interval_unit_body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        bounded_case16594_object_interval_shape_lookups,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_object_compute_eval_if_ispair_num:
  compute_eval clock ceqs
      (If (Uop Ispair (Num n)) yes_branch no_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs no_branch refs
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_if_eq_zero:
  compute_eval clock ceqs
      (If (Binop Eq (Num 0) (Num 0)) yes_branch no_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs yes_branch refs
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_if_eq_suc_zero:
  compute_eval clock ceqs
      (If (Binop Eq (Num (SUC n)) (Num 0)) yes_branch no_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs no_branch refs
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_interval_unit_zero_cons_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_one_interval» []) (refs:hol_refs) =
    (M_success (from_cv one_cv),refs) /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_zeros» [from_cv items]) refs =
    (M_success (from_cv zeros_cv),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_unit»
        [Num 0;from_cv (Pair item items)]) refs =
    (M_success (from_cv (Pair one_cv zeros_cv)),refs)
Proof
  strip_tac
  >> simp [bounded_case16594_object_interval_unit_num_unfold]
  >> simp
       [bounded_case16594_object_interval_unit_body_def,
        compute_evalTheory.subst_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_if_ispair_from_cv_pair,
        bounded_case16594_object_compute_eval_if_ispair_num,
        bounded_case16594_object_compute_eval_if_eq_zero]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac >- asm_rewrite_tac []
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_dim_interval_zeros»
          [Uop Snd (Pair (from_cv item) (from_cv items))]) refs =
      compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_dim_interval_zeros» [from_cv items]) refs` by
       (irule
          compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> simp
             [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_snd])
  >> simp []
QED

Theorem bounded_case16594_object_interval_unit_suc_cons_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_zero_interval» []) (refs:hol_refs) =
    (M_success (from_cv zero_cv),refs) /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_unit»
        [Num variable;from_cv items]) refs =
    (M_success (from_cv unit_cv),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_unit»
        [Num (SUC variable);from_cv (Pair item items)]) refs =
    (M_success (from_cv (Pair zero_cv unit_cv)),refs)
Proof
  strip_tac
  >> simp [bounded_case16594_object_interval_unit_num_unfold]
  >> simp
       [bounded_case16594_object_interval_unit_body_def,
        compute_evalTheory.subst_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_if_ispair_from_cv_pair,
        bounded_case16594_object_compute_eval_if_ispair_num,
        bounded_case16594_object_compute_eval_if_eq_suc_zero]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac >- asm_rewrite_tac []
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_dim_interval_unit»
          [Binop Sub (Num (SUC variable)) (Num 1);
           Uop Snd (Pair (from_cv item) (from_cv items))]) refs =
      compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_dim_interval_unit»
          [from_cv (Num variable);from_cv items]) refs` by
       (irule
          compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
        >> conj_tac >- intLib.ARITH_TAC
        >> conj_tac
        >- simp
             [compute_evalTheory.compute_eval_def,
              compute_evalTheory.do_binop_def,
              compute_evalTheory.do_arith_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def]
        >> simp
             [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_snd])
  >> fs [compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_object_interval_unit_eval:
  !items variable clock refs.
    variable < LENGTH items /\
    8 * (LENGTH items + 1) < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_dim_interval_unit»
          [Num variable;from_cv (bounded_object_q_cv_list items)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_object_q_cv_list
            (bounded_case16594_object_interval_unit_cv variable items))),refs)
Proof
  Induct_on `items`
  >- simp []
  >> Cases_on `variable`
  >- (rpt gen_tac
      >> strip_tac
      >> PURE_REWRITE_TAC
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            bounded_case16594_object_interval_unit_cv_def]
      >> irule bounded_case16594_object_interval_unit_zero_cons_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule bounded_case16594_object_one_interval_eval
          >> intLib.ARITH_TAC)
      >> irule bounded_case16594_object_interval_zeros_eval
      >> qpat_x_assum `8 * (LENGTH (h::items) + 1) < clock` mp_tac
      >> simp []
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> strip_tac
  >> PURE_REWRITE_TAC
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        bounded_case16594_object_interval_unit_cv_def]
  >> irule bounded_case16594_object_interval_unit_suc_cons_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (qpat_x_assum `!variable clock refs. _`
       (qspecl_then [`n`,`clock - 1`,`refs`] mp_tac)
      >> impl_tac
      >- (qpat_x_assum `SUC n < LENGTH (h::items)` mp_tac
          >> qpat_x_assum `8 * (LENGTH (h::items) + 1) < clock` mp_tac
          >> simp []
          >> intLib.ARITH_TAC)
      >> simp [])
  >> simp
       [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_zero_interval_identity]
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_zero_interval_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_interval_unit_genlist:
  !items variable.
    variable < LENGTH items ==>
    bounded_case16594_object_interval_unit_cv variable items =
      GENLIST
        (\position.
           if position = variable then
             bounded_analytic_source_q_interval_cv 1 0 0
           else bounded_analytic_source_q_interval_cv 0 0 0)
        (LENGTH items)
Proof
  Induct_on `items`
  >> Cases_on `variable`
  >> simp
       [bounded_case16594_object_interval_unit_cv_def,
        bounded_case16594_object_one_interval_cv_def,
        compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_zero_interval_identity,
        listTheory.GENLIST_CONS,
        rich_listTheory.REPLICATE_GENLIST,
        combinTheory.o_DEF,combinTheory.K_DEF]
QED

Theorem bounded_case16594_object_interval_unit_six:
  LENGTH items = 6 /\ variable < 6 ==>
  bounded_case16594_object_interval_unit_cv variable items =
    bounded_object_q_unit_vector variable
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `GENLIST
          (\position.
             if position = variable then
               bounded_analytic_source_q_interval_cv 1 0 0
             else bounded_analytic_source_q_interval_cv 0 0 0)
          (LENGTH items)`
  >> conj_tac
  >- (irule bounded_case16594_object_interval_unit_genlist
      >> simp [])
  >> simp
       [compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_unit_vector_def]
QED

val _ = export_theory ();
