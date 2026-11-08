(*****************************************************************************
 * Structural evaluator semantics for one explicit-radius object polynomial
 * instruction.
 *
 * Numerical state operations remain premises.  This theory authenticates the
 * generated instruction decoder, stack discipline, and success wrapper before
 * those operations are connected to the object-q semantics.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPolyStepControlEval
Ancestors
  compute_boundedCase16594ObjectRecompleteControlEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_poly_step_body_def:
  bounded_case16594_object_poly_step_body =
    If (Uop Ispair (Var «instruction»))
      (If (Binop Eq (Uop Fst (Var «instruction»)) (Num 0))
        (Pair (Num 1)
          (Pair
            (App «candle_cv_q_packed_object_constant_state»
              [Uop Snd (Var «instruction»)])
            (Var «stack»)))
        (If
          (App «candle_cv_bool_and»
            [Binop Eq (Uop Fst (Var «instruction»)) (Num 1);
             Binop Less (Uop Snd (Var «instruction»)) (Num 6)])
          (Pair (Num 1)
            (Pair
              (App «candle_cv_q_packed_object_variable_state»
                [Var «center_boxes»;Var «outer_boxes»;
                 Uop Snd (Var «instruction»)])
              (Var «stack»)))
          (Pair (Num 0) (Var «stack»))))
      (If (Binop Eq (Var «instruction») (Num 2))
        (If (Uop Ispair (Var «stack»))
          (Pair (Num 1)
            (Pair
              (App «candle_cv_q_packed_object_state_neg»
                [Var «radii»;Uop Fst (Var «stack»)])
              (Uop Snd (Var «stack»))))
          (Pair (Num 0) (Var «stack»)))
        (If (Binop Eq (Var «instruction») (Num 3))
          (If (Uop Ispair (Var «stack»))
            (If (Uop Ispair (Uop Snd (Var «stack»)))
              (Pair (Num 1)
                (Pair
                  (App «candle_cv_q_packed_object_state_add»
                    [Var «radii»;Uop Fst (Uop Snd (Var «stack»));
                     Uop Fst (Var «stack»)])
                  (Uop Snd (Uop Snd (Var «stack»)))))
              (Pair (Num 0) (Var «stack»)))
            (Pair (Num 0) (Var «stack»)))
          (If (Binop Eq (Var «instruction») (Num 4))
            (If (Uop Ispair (Var «stack»))
              (If (Uop Ispair (Uop Snd (Var «stack»)))
                (Pair (Num 1)
                  (Pair
                    (App «candle_cv_q_packed_object_state_mul»
                      [Var «radii»;Uop Fst (Uop Snd (Var «stack»));
                       Uop Fst (Var «stack»)])
                    (Uop Snd (Uop Snd (Var «stack»)))))
                (Pair (Num 0) (Var «stack»)))
              (Pair (Num 0) (Var «stack»)))
            (If (Binop Eq (Var «instruction») (Num 5))
              (If (Uop Ispair (Var «stack»))
                (Pair (Num 1)
                  (Pair
                    (App «candle_cv_q_packed_object_state_mul»
                      [Var «radii»;Uop Fst (Var «stack»);
                       Uop Fst (Var «stack»)])
                    (Uop Snd (Var «stack»))))
                (Pair (Num 0) (Var «stack»)))
              (Pair (Num 0) (Var «stack»))))))
End

Definition bounded_case16594_object_cv_list_def:
  bounded_case16594_object_cv_list [] = Num 0 /\
  bounded_case16594_object_cv_list (item::items) =
    Pair item (bounded_case16594_object_cv_list items)
End

Definition bounded_case16594_object_zero_interval_cv_def:
  bounded_case16594_object_zero_interval_cv =
    Pair (Pair (Pair (Num 0) (Num 0)) (Num 0))
      (Pair (Pair (Num 0) (Num 0)) (Num 0))
End

Definition bounded_case16594_object_zero_gradient6_cv_def:
  bounded_case16594_object_zero_gradient6_cv =
    bounded_case16594_object_cv_list
      (REPLICATE 6 bounded_case16594_object_zero_interval_cv)
End

Definition bounded_case16594_object_zero_hessian21_cv_def:
  bounded_case16594_object_zero_hessian21_cv =
    bounded_case16594_object_cv_list
      (REPLICATE 21 bounded_case16594_object_zero_interval_cv)
End

Definition bounded_case16594_object_constant_state_body_def:
  bounded_case16594_object_constant_state_body =
    App «candle_cv_q_packed_object_state_make»
      [Num 1;
       Pair (Var «rational_payload») (Var «rational_payload»);
       App «candle_cv_q_packed_object_zero_gradient6» [];
       Pair (Var «rational_payload») (Var «rational_payload»);
       App «candle_cv_q_packed_object_zero_gradient6» [];
       App «candle_cv_q_packed_object_zero_hessian21» []]
End

Definition bounded_case16594_object_constant_state_cv_def:
  bounded_case16594_object_constant_state_cv payload =
    bounded_case16594_object_state_cv
      (Num 1) (Pair payload payload)
      bounded_case16594_object_zero_gradient6_cv
      (Pair payload payload)
      bounded_case16594_object_zero_gradient6_cv
      bounded_case16594_object_zero_hessian21_cv
End

Definition bounded_case16594_object_state_neg_body_def:
  bounded_case16594_object_state_neg_body =
    Let «center_value»
      (App «candle_cv_q_interval_neg»
        [App «candle_cv_q_packed_object_state_center_value»
          [Var «state»]])
      (Let «center_gradient»
        (App «candle_cv_q_dim_interval_list_neg»
          [App «candle_cv_q_packed_object_state_center_gradient»
            [Var «state»]])
        (Let «packed_hessian»
          (App «candle_cv_q_dim_interval_list_neg»
            [App «candle_cv_q_packed_object_state_packed_hessian»
              [Var «state»]])
          (App «candle_cv_q_packed_object_state_recomplete»
            [Var «radii»;
             App «candle_cv_q_packed_object_state_domain» [Var «state»];
             Var «center_value»;Var «center_gradient»;
             Var «packed_hessian»])))
End

Definition bounded_case16594_object_state_mul_body_def:
  bounded_case16594_object_state_mul_body =
    Let «center_value»
      (App «candle_cv_q_interval_mul»
        [App «candle_cv_q_packed_object_state_center_value» [Var «left»];
         App «candle_cv_q_packed_object_state_center_value» [Var «right»]])
      (Let «center_gradient»
        (App «candle_cv_q_packed_object_fused_scale_add»
          [App «candle_cv_q_packed_object_state_center_value» [Var «right»];
           App «candle_cv_q_packed_object_state_center_gradient» [Var «left»];
           App «candle_cv_q_packed_object_state_center_value» [Var «left»];
           App «candle_cv_q_packed_object_state_center_gradient» [Var «right»]])
        (Let «packed_hessian»
          (App «candle_cv_q_packed_object_mul_hessian6»
            [App «candle_cv_q_packed_object_state_value_bound» [Var «left»];
             App «candle_cv_q_packed_object_state_value_bound» [Var «right»];
             App «candle_cv_q_packed_object_state_gradient_bounds» [Var «left»];
             App «candle_cv_q_packed_object_state_gradient_bounds» [Var «right»];
             App «candle_cv_q_packed_object_state_packed_hessian» [Var «left»];
             App «candle_cv_q_packed_object_state_packed_hessian» [Var «right»]])
          (App «candle_cv_q_packed_object_state_recomplete»
            [Var «radii»;
             App «candle_cv_bool_and»
               [App «candle_cv_q_packed_object_state_domain» [Var «left»];
                App «candle_cv_q_packed_object_state_domain» [Var «right»]];
             Var «center_value»;Var «center_gradient»;
             Var «packed_hessian»])))
End

Theorem bounded_case16594_object_poly_step_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_poly_step» =
    SOME
      ([«center_boxes»;«outer_boxes»;«radii»;«instruction»;«stack»],
       bounded_case16594_object_poly_step_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_poly_step_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv instruction;from_cv stack]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («instruction»,from_cv instruction);(«stack»,from_cv stack)]
        bounded_case16594_object_poly_step_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectRecompleteControlEvalTheory.bounded_case16594_object_compute_eval_literal_app5
  >> asm_rewrite_tac [bounded_case16594_object_poly_step_lookup]
QED

Theorem bounded_case16594_object_poly_step_constant_control_eval:
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («instruction»,from_cv (Pair (Num 0) payload));
         («stack»,from_cv stack)]
        bounded_case16594_object_poly_step_body) (refs:hol_refs) =
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (Pair (Num 1)
        (Pair
          (App «candle_cv_q_packed_object_constant_state» [from_cv payload])
          (from_cv stack))) refs
Proof
  simp
    [bounded_case16594_object_poly_step_body_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.subst_def,
     compute_execTheory.from_cv_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.option_def,
     compute_evalTheory.check_def,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     compute_evalTheory.do_fst_def,
     compute_evalTheory.do_snd_def,
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_pair_from_raw_results:
  compute_eval clock ceqs left_expression (refs:hol_refs) =
      (M_success left_value,refs) /\
  compute_eval clock ceqs right_expression refs =
      (M_success right_value,refs) ==>
  compute_eval clock ceqs (Pair left_expression right_expression) refs =
    (M_success (Pair left_value right_value),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_num:
  compute_eval clock ceqs (Num n) (refs:hol_refs) =
    (M_success (Num n),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_pair_of_cv:
  compute_eval clock ceqs
      (Pair (from_cv left) (from_cv right)) (refs:hol_refs) =
    (M_success (from_cv (Pair left right)),refs)
Proof
  simp [compute_execTheory.from_cv_def]
  >> irule bounded_case16594_object_compute_eval_pair_from_raw_results
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_case16594_object_compute_eval_literal_app0:
  0 < clock /\
  ALOOKUP ceqs function_name = SOME ([],from_cv result) ==>
  compute_eval clock ceqs (App function_name []) (refs:hol_refs) =
    (M_success (from_cv result),refs)
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
QED

Theorem bounded_case16594_object_compute_eval_literal_app2:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME ([first_name;second_name],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv (first_argument:cv);from_cv (second_argument:cv)])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(first_name,from_cv first_argument);
         (second_name,from_cv second_argument)] body) refs
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

Theorem bounded_case16594_object_compute_eval_literal_app3:
  0 < clock /\
  ALOOKUP ceqs function_name =
      SOME ([name1;name2;name3],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv value1;from_cv value2;from_cv value3])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name1,from_cv value1);(name2,from_cv value2);
         (name3,from_cv value3)] body) refs
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
QED

Theorem bounded_case16594_object_zero_lookups:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_zero_gradient6» =
    SOME ([],from_cv bounded_case16594_object_zero_gradient6_cv) /\
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_zero_hessian21» =
    SOME ([],from_cv bounded_case16594_object_zero_hessian21_cv)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_zero_gradient6_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_zero_gradient6» [])
      (refs:hol_refs) =
    (M_success (from_cv bounded_case16594_object_zero_gradient6_cv),refs)
Proof
  strip_tac
  >> irule bounded_case16594_object_compute_eval_literal_app0
  >> asm_rewrite_tac []
  >> fs [bounded_case16594_object_zero_lookups]
QED

Theorem bounded_case16594_object_zero_hessian21_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_zero_hessian21» [])
      (refs:hol_refs) =
    (M_success (from_cv bounded_case16594_object_zero_hessian21_cv),refs)
Proof
  strip_tac
  >> irule bounded_case16594_object_compute_eval_literal_app0
  >> asm_rewrite_tac []
  >> fs [bounded_case16594_object_zero_lookups]
QED

Theorem bounded_case16594_object_constant_state_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_constant_state» =
    SOME ([«rational_payload»],bounded_case16594_object_constant_state_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_constant_state_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_constant_state» [from_cv payload])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«rational_payload»,from_cv payload)]
        bounded_case16594_object_constant_state_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_constant_state_lookup
QED

Theorem bounded_case16594_object_constant_state_arguments_eval:
  1 < clock ==>
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_make»
        [Num 1;Pair (from_cv payload) (from_cv payload);
         App «candle_cv_q_packed_object_zero_gradient6» [];
         Pair (from_cv payload) (from_cv payload);
         App «candle_cv_q_packed_object_zero_gradient6» [];
         App «candle_cv_q_packed_object_zero_hessian21» []])
      (refs:hol_refs) =
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_make»
        [from_cv (Num 1);from_cv (Pair payload payload);
         from_cv bounded_case16594_object_zero_gradient6_cv;
         from_cv (Pair payload payload);
         from_cv bounded_case16594_object_zero_gradient6_cv;
         from_cv bounded_case16594_object_zero_hessian21_cv]) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_app6_argument_results
  >> simp
       [bounded_case16594_object_compute_eval_num,
        bounded_case16594_object_compute_eval_pair_of_cv,
        compute_execProofTheory.compute_eval_from_cv,
        bounded_case16594_object_zero_gradient6_eval,
        bounded_case16594_object_zero_hessian21_eval]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_constant_state_subst:
  subst [(«rational_payload»,from_cv payload)]
      bounded_case16594_object_constant_state_body =
    App «candle_cv_q_packed_object_state_make»
      [Num 1;Pair (from_cv payload) (from_cv payload);
       App «candle_cv_q_packed_object_zero_gradient6» [];
       Pair (from_cv payload) (from_cv payload);
       App «candle_cv_q_packed_object_zero_gradient6» [];
       App «candle_cv_q_packed_object_zero_hessian21» []]
Proof
  simp_tac (pure_ss)
    [bounded_case16594_object_constant_state_body_def,
     compute_evalTheory.subst_def,listTheory.MAP,
     alistTheory.ALOOKUP_def,boolTheory.EQ_REFL,
     boolTheory.COND_CLAUSES,optionTheory.option_case_def]
QED

Theorem bounded_case16594_object_constant_state_body_normalizes:
  1 < clock ==>
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«rational_payload»,from_cv payload)]
        bounded_case16594_object_constant_state_body) (refs:hol_refs) =
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_make»
        [from_cv (Num 1);from_cv (Pair payload payload);
         from_cv bounded_case16594_object_zero_gradient6_cv;
         from_cv (Pair payload payload);
         from_cv bounded_case16594_object_zero_gradient6_cv;
         from_cv bounded_case16594_object_zero_hessian21_cv]) refs
Proof
  strip_tac
  >> PURE_REWRITE_TAC [bounded_case16594_object_constant_state_subst]
  >> irule bounded_case16594_object_constant_state_arguments_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_constant_state_eval:
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_constant_state» [from_cv payload])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_case16594_object_constant_state_cv payload)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
          (subst [(«rational_payload»,from_cv payload)]
             bounded_case16594_object_constant_state_body) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_constant_state_unfold
      >> intLib.ARITH_TAC)
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_make»
            [from_cv (Num 1);from_cv (Pair payload payload);
             from_cv bounded_case16594_object_zero_gradient6_cv;
             from_cv (Pair payload payload);
             from_cv bounded_case16594_object_zero_gradient6_cv;
             from_cv bounded_case16594_object_zero_hessian21_cv]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_constant_state_body_normalizes
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [bounded_case16594_object_constant_state_cv_def]
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_make_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_poly_step_constant_eval_from_state:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_constant_state» [from_cv payload])
      (refs:hol_refs) = (M_success (from_cv result_state),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Pair (Num 0) payload);from_cv stack]) refs =
    (M_success
      (from_cv (Pair (Num 1) (Pair result_state stack))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_poly_step_unfold]
  >> PURE_REWRITE_TAC
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          bounded_case16594_object_poly_step_constant_control_eval]
  >> irule bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- simp [bounded_case16594_object_compute_eval_num]
  >> irule bounded_case16594_object_compute_eval_pair_from_raw_results
  >> asm_simp_tac std_ss [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_case16594_object_poly_step_constant_eval:
  2 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Pair (Num 0) payload);from_cv stack]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (bounded_case16594_object_constant_state_cv payload)
            stack))),refs)
Proof
  strip_tac
  >> irule bounded_case16594_object_poly_step_constant_eval_from_state
  >> conj_tac >- intLib.ARITH_TAC
  >> irule bounded_case16594_object_constant_state_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_neg_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_neg» =
    SOME ([«radii»;«state»],bounded_case16594_object_state_neg_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_state_neg_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_neg»
        [from_cv radii;from_cv state_cv]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«radii»,from_cv radii);(«state»,from_cv state_cv)]
        bounded_case16594_object_state_neg_body) refs
Proof
  strip_tac
  >> irule bounded_case16594_object_compute_eval_literal_app2
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_state_neg_lookup
QED

Theorem bounded_case16594_object_state_neg_eval_from_components:
  4 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_neg»
        [App «candle_cv_q_packed_object_state_center_value»
          [from_cv state_cv]]) (refs:hol_refs) =
      (M_success (from_cv next_center_value),refs) /\
  compute_eval (clock - 2) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg»
        [App «candle_cv_q_packed_object_state_center_gradient»
          [from_cv state_cv]]) refs =
      (M_success (from_cv next_center_gradient),refs) /\
  compute_eval (clock - 3) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg»
        [App «candle_cv_q_packed_object_state_packed_hessian»
          [from_cv state_cv]]) refs =
      (M_success (from_cv next_packed_hessian),refs) /\
  compute_eval (clock - 4) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_recomplete»
        [from_cv radii;
         App «candle_cv_q_packed_object_state_domain» [from_cv state_cv];
         from_cv next_center_value;from_cv next_center_gradient;
         from_cv next_packed_hessian]) refs =
      (M_success (from_cv result_state),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_neg»
        [from_cv radii;from_cv state_cv]) refs =
      (M_success (from_cv result_state),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_state_neg_unfold]
  >> simp
       [bounded_case16594_object_state_neg_body_def,
        compute_evalTheory.subst_def]
  >> irule
       (Q.INST [`value` |-> `next_center_value`]
          compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_center_value`
  >> conj_tac >- asm_rewrite_tac []
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (Q.INST [`value` |-> `next_center_gradient`]
          compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_center_gradient`
  >> conj_tac >- asm_rewrite_tac []
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (Q.INST [`value` |-> `next_packed_hessian`]
          compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_packed_hessian`
  >> conj_tac >- asm_rewrite_tac []
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_poly_step_neg_control_eval:
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («instruction»,from_cv (Num 2));
         («stack»,from_cv (Pair operand rest))]
        bounded_case16594_object_poly_step_body) (refs:hol_refs) =
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (Pair (Num 1)
        (Pair
          (App «candle_cv_q_packed_object_state_neg»
            [from_cv radii;from_cv operand])
          (from_cv rest))) refs
Proof
  simp
    [bounded_case16594_object_poly_step_body_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.subst_def,
     compute_execTheory.from_cv_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.option_def,
     compute_evalTheory.check_def,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     compute_evalTheory.do_fst_def,
     compute_evalTheory.do_snd_def,
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_poly_step_neg_eval_from_state:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_neg»
        [from_cv radii;from_cv operand])
      (refs:hol_refs) = (M_success (from_cv result_state),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num 2);from_cv (Pair operand rest)]) refs =
    (M_success
      (from_cv (Pair (Num 1) (Pair result_state rest))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_poly_step_unfold]
  >> PURE_REWRITE_TAC
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          bounded_case16594_object_poly_step_neg_control_eval]
  >> irule bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- simp [bounded_case16594_object_compute_eval_num]
  >> irule bounded_case16594_object_compute_eval_pair_from_raw_results
  >> asm_simp_tac std_ss [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_case16594_object_state_mul_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_mul» =
    SOME ([«radii»;«left»;«right»],
      bounded_case16594_object_state_mul_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_state_mul_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_mul»
        [from_cv radii;from_cv left_cv;from_cv right_cv])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«radii»,from_cv radii);(«left»,from_cv left_cv);
              («right»,from_cv right_cv)]
        bounded_case16594_object_state_mul_body) refs
Proof
  strip_tac
  >> irule bounded_case16594_object_compute_eval_literal_app3
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_state_mul_lookup
QED

Theorem bounded_case16594_object_state_mul_eval_from_components:
  4 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_mul»
        [App «candle_cv_q_packed_object_state_center_value» [from_cv left_cv];
         App «candle_cv_q_packed_object_state_center_value» [from_cv right_cv]])
      (refs:hol_refs) = (M_success (from_cv next_center_value),refs) /\
  compute_eval (clock - 2) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_fused_scale_add»
        [App «candle_cv_q_packed_object_state_center_value» [from_cv right_cv];
         App «candle_cv_q_packed_object_state_center_gradient» [from_cv left_cv];
         App «candle_cv_q_packed_object_state_center_value» [from_cv left_cv];
         App «candle_cv_q_packed_object_state_center_gradient» [from_cv right_cv]])
      refs = (M_success (from_cv next_center_gradient),refs) /\
  compute_eval (clock - 3) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_mul_hessian6»
        [App «candle_cv_q_packed_object_state_value_bound» [from_cv left_cv];
         App «candle_cv_q_packed_object_state_value_bound» [from_cv right_cv];
         App «candle_cv_q_packed_object_state_gradient_bounds» [from_cv left_cv];
         App «candle_cv_q_packed_object_state_gradient_bounds» [from_cv right_cv];
         App «candle_cv_q_packed_object_state_packed_hessian» [from_cv left_cv];
         App «candle_cv_q_packed_object_state_packed_hessian» [from_cv right_cv]])
      refs = (M_success (from_cv next_packed_hessian),refs) /\
  compute_eval (clock - 4) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_recomplete»
        [from_cv radii;
         App «candle_cv_bool_and»
           [App «candle_cv_q_packed_object_state_domain» [from_cv left_cv];
            App «candle_cv_q_packed_object_state_domain» [from_cv right_cv]];
         from_cv next_center_value;from_cv next_center_gradient;
         from_cv next_packed_hessian]) refs =
      (M_success (from_cv result_state),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_mul»
        [from_cv radii;from_cv left_cv;from_cv right_cv]) refs =
      (M_success (from_cv result_state),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_state_mul_unfold]
  >> simp
       [bounded_case16594_object_state_mul_body_def,
        compute_evalTheory.subst_def]
  >> irule
       (Q.INST [`value` |-> `next_center_value`]
          compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_center_value`
  >> conj_tac >- asm_rewrite_tac []
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (Q.INST [`value` |-> `next_center_gradient`]
          compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_center_gradient`
  >> conj_tac >- asm_rewrite_tac []
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (Q.INST [`value` |-> `next_packed_hessian`]
          compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_packed_hessian`
  >> conj_tac >- asm_rewrite_tac []
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_poly_step_mul_control_eval:
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («instruction»,from_cv (Num 4));
         («stack»,from_cv (Pair right_state (Pair left_state rest)))]
        bounded_case16594_object_poly_step_body) (refs:hol_refs) =
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (Pair (Num 1)
        (Pair
          (App «candle_cv_q_packed_object_state_mul»
            [from_cv radii;from_cv left_state;from_cv right_state])
          (from_cv rest))) refs
Proof
  simp
    [bounded_case16594_object_poly_step_body_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.subst_def,
     compute_execTheory.from_cv_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.option_def,
     compute_evalTheory.check_def,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     compute_evalTheory.do_fst_def,
     compute_evalTheory.do_snd_def,
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_poly_step_mul_eval_from_state:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_mul»
        [from_cv radii;from_cv left_state;from_cv right_state])
      (refs:hol_refs) = (M_success (from_cv result_state),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num 4);
         from_cv (Pair right_state (Pair left_state rest))]) refs =
    (M_success
      (from_cv (Pair (Num 1) (Pair result_state rest))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_poly_step_unfold]
  >> PURE_REWRITE_TAC
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          bounded_case16594_object_poly_step_mul_control_eval]
  >> irule bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- simp [bounded_case16594_object_compute_eval_num]
  >> irule bounded_case16594_object_compute_eval_pair_from_raw_results
  >> asm_simp_tac std_ss [compute_execProofTheory.compute_eval_from_cv]
QED

val _ = export_theory ();
