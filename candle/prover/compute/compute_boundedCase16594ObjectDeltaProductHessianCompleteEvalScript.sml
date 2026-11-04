(*****************************************************************************
 * Exact evaluator semantics for the recursive packed Hessian of 4*x_i*delta.
 *
 * The generic list theorem composes one proved product-rule entry through the
 * production two-list recursion.  The fixed wrapper then instantiates the
 * canonical 21 upper-triangular index pairs used by the six-dimensional
 * checker.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaProductHessianCompleteEval
Ancestors
  compute_boundedCase16594ObjectDeltaProductHessianEntryEval
  compute_boundedCase16594ObjectPolyTraceEval
  compute_boundedCase16594ObjectGradientCompleteEval
  compute_boundedPackedObjectEntryContract
Libs
  bossLib preamble intLib

val inherited_object_cv_list_def =
  DB.fetch "compute_boundedCase16594ObjectPolyStepControlEval"
    "bounded_case16594_object_cv_list_def";
val inherited_compute_eval_num =
  DB.fetch "compute_boundedCase16594ObjectPolyStepControlEval"
    "bounded_case16594_object_compute_eval_num";
val inherited_literal_app5 =
  DB.fetch "compute_boundedCase16594ObjectRecompleteControlEval"
    "bounded_case16594_object_compute_eval_literal_app5";
val inherited_if_ispair_pair_components =
  DB.fetch "compute_boundedCase16594ObjectGradientCompleteEval"
    "bounded_case16594_object_compute_eval_if_ispair_pair_components";
val inherited_pair_from_raw_results =
  DB.fetch "compute_boundedCase16594ObjectPolyStepControlEval"
    "bounded_case16594_object_compute_eval_pair_from_raw_results";
val inherited_app6_argument_results =
  DB.fetch "compute_boundedCase16594ObjectStateControlEval"
    "bounded_case16594_object_compute_eval_app6_argument_results";
val inherited_pair_fst_components =
  DB.fetch "compute_boundedCase16594ObjectGradientCompleteEval"
    "bounded_case16594_object_compute_eval_pair_fst_components";
val inherited_pair_snd_components =
  DB.fetch "compute_boundedCase16594ObjectGradientCompleteEval"
    "bounded_case16594_object_compute_eval_pair_snd_components";
val inherited_app5_argument_results =
  DB.fetch "compute_boundedCase16594ObjectPolyTraceEval"
    "bounded_case16594_object_compute_eval_app5_argument_results";
val inherited_object_q_cv_list_def =
  DB.fetch "compute_boundedPackedObjectEntryContract"
    "bounded_object_q_cv_list_def";
val inherited_literal_app4 =
  DB.fetch "compute_boundedCase16594ObjectInverseControlEval"
    "bounded_case16594_object_compute_eval_literal_app4";

Definition bounded_case16594_object_delta_product_hessian_body_def:
  bounded_case16594_object_delta_product_hessian_body =
    If (Uop Ispair (Var «indices»))
      (If (Uop Ispair (Var «entries»))
        (Pair
          (App «candle_cv_q_packed_delta_product_hessian_entry»
            [Var «coordinate»;Var «box_coordinate»;Var «delta_gradient»;
             Uop Fst (Uop Fst (Var «indices»));
             Uop Snd (Uop Fst (Var «indices»));
             Uop Fst (Var «entries»)])
          (App «candle_cv_q_packed_delta_product_hessian»
            [Var «coordinate»;Var «box_coordinate»;Var «delta_gradient»;
             Uop Snd (Var «indices»);Uop Snd (Var «entries»)]))
        (Num 0))
      (Num 0)
End

Definition bounded_case16594_object_delta_product_index_cv_def:
  bounded_case16594_object_delta_product_index_cv (row,column) =
    Pair (Num row) (Num column)
End

Definition bounded_case16594_object_delta_product_hessian_cv_def:
  bounded_case16594_object_delta_product_hessian_cv
      coordinate box_coordinate delta_gradient [] entries = [] /\
  bounded_case16594_object_delta_product_hessian_cv
      coordinate box_coordinate delta_gradient ((row,column)::indices) [] =
    [] /\
  bounded_case16594_object_delta_product_hessian_cv
      coordinate box_coordinate delta_gradient ((row,column)::indices)
      (entry::entries) =
    bounded_case16594_object_delta_product_hessian_entry_cv
      coordinate box_coordinate delta_gradient row column entry ::
    bounded_case16594_object_delta_product_hessian_cv
      coordinate box_coordinate delta_gradient indices entries
End

Definition bounded_case16594_object_delta_product_indices6_def:
  bounded_case16594_object_delta_product_indices6 : (num # num) list =
    [(0,0);(0,1);(0,2);(0,3);(0,4);(0,5);
     (1,1);(1,2);(1,3);(1,4);(1,5);
     (2,2);(2,3);(2,4);(2,5);
     (3,3);(3,4);(3,5);
     (4,4);(4,5);(5,5)]
End

Definition bounded_case16594_object_delta_product_hessian_six_body_def:
  bounded_case16594_object_delta_product_hessian_six_body =
    App «candle_cv_q_packed_delta_product_hessian»
      [Var «coordinate»;Var «box_coordinate»;Var «delta_gradient»;
       from_cv
         (bounded_case16594_object_cv_list
           (MAP bounded_case16594_object_delta_product_index_cv
             bounded_case16594_object_delta_product_indices6));
       Var «delta_hessian»]
End

Theorem bounded_case16594_object_compute_eval_if_ispair_index_cons:
  compute_eval clock ceqs
      (If
        (Uop Ispair
          (Pair (Pair (Num row) (Num column)) (from_cv index_rest)))
        yes_branch no_branch) (refs:hol_refs) =
    compute_eval clock ceqs yes_branch refs
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_index_row:
  compute_eval clock ceqs
      (Uop Fst
        (Uop Fst
          (Pair (Pair (Num row) (Num column)) (from_cv index_rest))))
      (refs:hol_refs) =
    (M_success (Num row),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_index_column:
  compute_eval clock ceqs
      (Uop Snd
        (Uop Fst
          (Pair (Pair (Num row) (Num column)) (from_cv index_rest))))
      (refs:hol_refs) =
    (M_success (Num column),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
     compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_index_rest:
  compute_eval clock ceqs
      (Uop Snd
        (Pair (Pair (Num row) (Num column)) (from_cv index_rest)))
      (refs:hol_refs) =
    (M_success (from_cv index_rest),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_delta_product_hessian_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_product_hessian» =
    SOME
      ([«coordinate»;«box_coordinate»;«delta_gradient»;«indices»;«entries»],
       bounded_case16594_object_delta_product_hessian_body)
Proof
  rw [bounded_case16594_object_delta_product_hessian_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_product_hessian_six_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_product_hessian_six» =
    SOME
      ([«coordinate»;«box_coordinate»;«delta_gradient»;«delta_hessian»],
       bounded_case16594_object_delta_product_hessian_six_body)
Proof
  rw
    [bounded_case16594_object_delta_product_hessian_six_body_def,
     bounded_case16594_object_delta_product_indices6_def,
     bounded_case16594_object_delta_product_index_cv_def,
     inherited_object_cv_list_def,
     compute_execTheory.from_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_product_hessian_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_hessian»
        [from_cv (Num coordinate);from_cv box_coordinate;
         from_cv (bounded_object_q_cv_list delta_gradient);
         from_cv indices;from_cv entries]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«coordinate»,from_cv (Num coordinate));
         («box_coordinate»,from_cv box_coordinate);
         («delta_gradient»,from_cv (bounded_object_q_cv_list delta_gradient));
         («indices»,from_cv indices);(«entries»,from_cv entries)]
        bounded_case16594_object_delta_product_hessian_body) refs
Proof
  strip_tac
  >> irule
       inherited_literal_app5
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_delta_product_hessian_lookup
QED

Theorem bounded_case16594_object_delta_product_hessian_nil_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_hessian»
        [from_cv (Num coordinate);from_cv box_coordinate;
         from_cv (bounded_object_q_cv_list delta_gradient);
         from_cv (Num 0);from_cv (Num 0)]) (refs:hol_refs) =
    (M_success (from_cv (Num 0)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_delta_product_hessian_unfold]
  >> simp
       [bounded_case16594_object_delta_product_hessian_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_delta_product_hessian_cons_eval:
  bounded_packed_q_interval_encoded box_coordinate /\
  EVERY bounded_packed_q_interval_encoded delta_gradient /\
  LENGTH delta_gradient = 6 /\ row < 6 /\ column < 6 /\
  bounded_packed_q_interval_encoded entry /\ 66 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_hessian»
        [from_cv (Num coordinate);from_cv box_coordinate;
         from_cv (bounded_object_q_cv_list delta_gradient);
         from_cv index_rest;from_cv entry_rest]) (refs:hol_refs) =
    (M_success (from_cv completed_rest),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_hessian»
        [from_cv (Num coordinate);from_cv box_coordinate;
         from_cv (bounded_object_q_cv_list delta_gradient);
         from_cv (Pair (Pair (Num row) (Num column)) index_rest);
         from_cv (Pair entry entry_rest)]) refs =
    (M_success
      (from_cv
        (Pair
          (bounded_case16594_object_delta_product_hessian_entry_cv
            coordinate box_coordinate delta_gradient row column entry)
          completed_rest)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_delta_product_hessian_unfold]
  >> simp
       [bounded_case16594_object_delta_product_hessian_body_def,
        compute_evalTheory.subst_def,
        bounded_case16594_object_compute_eval_if_ispair_index_cons,
        inherited_if_ispair_pair_components]
  >> irule
       inherited_pair_from_raw_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_packed_delta_product_hessian_entry»
                [from_cv (Num coordinate);from_cv box_coordinate;
                 from_cv (bounded_object_q_cv_list delta_gradient);
                 from_cv (Num row);from_cv (Num column);from_cv entry]) refs`
      >> conj_tac
      >- (irule
            inherited_app6_argument_results
          >> simp
               [inherited_compute_eval_num,
                compute_execProofTheory.compute_eval_from_cv,
                bounded_case16594_object_compute_eval_index_row,
                bounded_case16594_object_compute_eval_index_column,
                inherited_pair_fst_components,
                inherited_pair_snd_components]
          >> intLib.ARITH_TAC)
      >> irule
           bounded_case16594_object_delta_product_hessian_entry_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_product_hessian»
            [from_cv (Num coordinate);from_cv box_coordinate;
             from_cv (bounded_object_q_cv_list delta_gradient);
             from_cv index_rest;from_cv entry_rest]) refs`
  >> conj_tac
  >- (irule
        inherited_app5_argument_results
      >> simp
           [inherited_compute_eval_num,
            compute_execProofTheory.compute_eval_from_cv,
            bounded_case16594_object_compute_eval_index_rest,
            inherited_pair_snd_components]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_delta_product_hessian_eval:
  !indices entries clock refs.
    bounded_packed_q_interval_encoded box_coordinate /\
    EVERY bounded_packed_q_interval_encoded delta_gradient /\
    LENGTH delta_gradient = 6 /\
    EVERY (λindex. FST index < 6 /\ SND index < 6) indices /\
    EVERY bounded_packed_q_interval_encoded entries /\
    LENGTH indices = LENGTH entries /\
    68 * (LENGTH indices + 1) < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_hessian»
        [from_cv (Num coordinate);from_cv box_coordinate;
         from_cv (bounded_object_q_cv_list delta_gradient);
         from_cv
           (bounded_case16594_object_cv_list
             (MAP bounded_case16594_object_delta_product_index_cv indices));
         from_cv (bounded_object_q_cv_list entries)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_case16594_object_delta_product_hessian_cv
            coordinate box_coordinate delta_gradient indices entries))),refs)
Proof
  Induct_on `indices`
  >- (rpt gen_tac
      >> Cases_on `entries`
      >> simp []
      >> strip_tac
      >> PURE_REWRITE_TAC
           [bounded_case16594_object_delta_product_hessian_cv_def,
            bounded_case16594_object_delta_product_index_cv_def,
            inherited_object_cv_list_def,
            inherited_object_q_cv_list_def,
            listTheory.MAP]
      >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             bounded_case16594_object_delta_product_hessian_nil_eval)
      >> intLib.ARITH_TAC)
  >> Cases_on `h`
  >> rpt gen_tac
  >> Cases_on `entries`
  >- simp []
  >> strip_tac
  >> gvs []
  >> PURE_REWRITE_TAC
       [bounded_case16594_object_delta_product_hessian_cv_def,
        bounded_case16594_object_delta_product_index_cv_def,
        inherited_object_cv_list_def,
        inherited_object_q_cv_list_def,
        listTheory.MAP]
  >> PURE_REWRITE_TAC
       [bounded_case16594_object_delta_product_hessian_cv_def,
        bounded_case16594_object_delta_product_index_cv_def,
        inherited_object_cv_list_def,
        inherited_object_q_cv_list_def]
  >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_delta_product_hessian_cons_eval)
  >> simp []
  >> (conj_tac >- intLib.ARITH_TAC)
  >> first_x_assum irule
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_delta_product_hessian_six_eval:
  bounded_packed_q_interval_encoded box_coordinate /\
  EVERY bounded_packed_q_interval_encoded delta_gradient /\
  LENGTH delta_gradient = 6 /\ coordinate < 6 /\
  EVERY bounded_packed_q_interval_encoded delta_hessian /\
  LENGTH delta_hessian = 21 /\ 1500 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_hessian_six»
        [from_cv (Num coordinate);from_cv box_coordinate;
         from_cv (bounded_object_q_cv_list delta_gradient);
         from_cv (bounded_object_q_cv_list delta_hessian)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_case16594_object_delta_product_hessian_cv
            coordinate box_coordinate delta_gradient
            bounded_case16594_object_delta_product_indices6
            delta_hessian))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«coordinate»,from_cv (Num coordinate));
             («box_coordinate»,from_cv box_coordinate);
             («delta_gradient»,from_cv (bounded_object_q_cv_list delta_gradient));
             («delta_hessian»,from_cv (bounded_object_q_cv_list delta_hessian))]
            bounded_case16594_object_delta_product_hessian_six_body) refs`
  >> conj_tac
  >- (irule
        inherited_literal_app4
      >> simp []
      >> ACCEPT_TAC
           bounded_case16594_object_delta_product_hessian_six_lookup)
  >> simp
       [bounded_case16594_object_delta_product_hessian_six_body_def,
        compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_delta_product_hessian_eval)
  >> simp
       [bounded_case16594_object_delta_product_indices6_def]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
