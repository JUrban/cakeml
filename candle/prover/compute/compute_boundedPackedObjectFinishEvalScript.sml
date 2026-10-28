(*****************************************************************************
 * Source-faithful final shape, sign, finish, and acceptance evaluation for
 * the mechanically exported five-payload packed-object entry.
 *****************************************************************************)
Theory compute_boundedPackedObjectFinishEval
Ancestors
  compute_boundedPackedObjectValueEval
Libs
  bossLib preamble intLib

Definition bounded_packed_list_length_body_def:
  bounded_packed_list_length_body =
    If (Uop Ispair (Var «items»))
      (Binop Add (Num 1)
        (App «candle_cv_list_length» [Uop Snd (Var «items»)]))
      (Num 0)
End

Definition bounded_packed_bool_and_body_def:
  bounded_packed_bool_and_body =
    If (Var «a») (Var «b») (Num 0)
End

Definition bounded_packed_q_finish6_body_def:
  bounded_packed_q_finish6_body =
    Let «bound»
      (App «candle_cv_q_packed_object_value_bound6»
        [Var «radii»;Var «center_value»;Var «center_gradient»;Var «packed»])
      (Let «shape»
        (App «candle_cv_bool_and»
          [Binop Eq
            (App «candle_cv_list_length» [Var «radii»]) (Num 6);
           App «candle_cv_bool_and»
            [Binop Eq
              (App «candle_cv_list_length» [Var «center_gradient»]) (Num 6);
             Binop Eq
              (App «candle_cv_list_length» [Var «packed»]) (Num 21)]])
        (Pair
          (If (App «candle_cv_bool_and» [Var «domain»;Var «shape»])
            (If
              (App «candle_cv_q_le»
                [App «candle_cv_q_zero» [];Uop Snd (Var «bound»)])
              (Num 0) (Num 1))
            (Num 0))
          (Uop Snd (Var «bound»))))
End

Definition bounded_packed_q_accept6_body_def:
  bounded_packed_q_accept6_body =
    Uop Fst
      (App «candle_cv_q_packed_object_finish6»
        [Var «domain»;Var «radii»;Var «center_value»;
         Var «center_gradient»;Var «packed»])
End

Theorem bounded_packed_list_length_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs «candle_cv_list_length» =
    SOME ([«items»],bounded_packed_list_length_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_bool_and_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs «candle_cv_bool_and» =
    SOME ([«a»;«b»],bounded_packed_bool_and_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_q_finish6_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs
      «candle_cv_q_packed_object_finish6» =
    SOME
      ([«domain»;«radii»;«center_value»;«center_gradient»;«packed»],
       bounded_packed_q_finish6_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_q_accept6_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs
      «candle_cv_q_packed_object_accept6» =
    SOME
      ([«domain»;«radii»;«center_value»;«center_gradient»;«packed»],
       bounded_packed_q_accept6_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_compute_eval_literal_app1:
  0 < clock /\
  ALOOKUP ceqs function_name = SOME ([argument_name],body) ==>
  compute_eval clock ceqs
      (App function_name [from_cv argument]) (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst [(argument_name,from_cv argument)] body) refs
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

Theorem bounded_packed_list_length_unfold:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_list_length» [from_cv items]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (subst [(«items»,from_cv items)] bounded_packed_list_length_body) refs
Proof
  strip_tac
  >> irule bounded_packed_compute_eval_literal_app1
  >> simp [bounded_packed_list_length_lookup]
QED

Theorem bounded_packed_compute_eval_binop_add_num_results:
  compute_eval clock ceqs left (refs:hol_refs) =
      (M_success (Num left_result),refs) /\
  compute_eval clock ceqs right refs =
      (M_success (Num right_result),refs) ==>
  compute_eval clock ceqs (Binop Add left right) refs =
    (M_success (Num (left_result + right_result)),refs)
Proof
  simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_list_length_nil_eval:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_list_length» [from_cv (Num 0)]) (refs:hol_refs) =
    (M_success (Num 0),refs)
Proof
  strip_tac
  >> rw [bounded_packed_list_length_unfold]
  >> simp
       [bounded_packed_list_length_body_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_list_length_cons_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (App «candle_cv_list_length» [from_cv items]) (refs:hol_refs) =
    (M_success (Num result_length),refs) ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_list_length» [from_cv (Pair item items)]) refs =
    (M_success (Num (SUC result_length)),refs)
Proof
  strip_tac
  >> rw [bounded_packed_list_length_unfold]
  >> simp
       [bounded_packed_list_length_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def,
        compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair]
  >> irule EQ_TRANS
  >> qexists_tac
       `(M_success (Num (1 + result_length)),refs)`
  >> conj_tac
  >- (irule bounded_packed_compute_eval_binop_add_num_results
      >> conj_tac
      >- simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1) bounded_packed_object_entry_ceqs
              (App «candle_cv_list_length» [from_cv items]) refs`
      >> conj_tac
      >- (irule
            compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app1_argument_result
          >> simp
               [compute_evalTheory.compute_eval_def,
                compute_execProofTheory.compute_eval_from_cv,
                compute_evalTheory.do_uop_def,
                compute_evalTheory.do_snd_def,
                ml_monadBaseTheory.st_ex_bind_def,
                ml_monadBaseTheory.st_ex_return_def]
          >> intLib.ARITH_TAC)
      >> simp [])
  >> simp []
QED

Theorem bounded_packed_list_length_eval:
  !items clock refs.
    LENGTH items + 1 < clock ==>
    compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_list_length»
          [from_cv (bounded_object_q_cv_list items)]) (refs:hol_refs) =
      (M_success (Num (LENGTH items)),refs)
Proof
  Induct_on `items`
  >- (rpt strip_tac
      >> rw
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             bounded_packed_list_length_nil_eval)
      >> intLib.ARITH_TAC)
  >> rpt strip_tac
  >> rw
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_list_length_cons_eval)
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qpat_x_assum `!clock refs. _`
       (qspecl_then [`clock - 1`,`refs`] mp_tac)
  >> impl_tac
  >- (Cases_on `clock` >> fs [])
  >> simp []
QED

Theorem bounded_packed_compute_eval_binop_eq_num_result:
  compute_eval clock ceqs expression (refs:hol_refs) =
      (M_success (Num actual),refs) ==>
  compute_eval clock ceqs (Binop Eq expression (Num expected)) refs =
    (M_success (Num (if actual = expected then 1 else 0)),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_compute_eval_binop_eq_num_same:
  compute_eval clock ceqs expression (refs:hol_refs) =
      (M_success (Num expected),refs) ==>
  compute_eval clock ceqs (Binop Eq expression (Num expected)) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`actual` |-> `expected`]
         bounded_packed_compute_eval_binop_eq_num_result)
  >> simp []
QED

Theorem bounded_packed_bool_and_true_one_eval:
  0 < clock /\
  compute_eval clock bounded_packed_object_entry_ceqs
      first_expression (refs:hol_refs) = (M_success (Num 1),refs) /\
  compute_eval clock bounded_packed_object_entry_ceqs
      second_expression refs = (M_success (Num 1),refs) ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_bool_and»
        [first_expression;second_expression]) refs =
    (M_success (Num 1),refs)
Proof
  Cases_on `clock`
  >- simp []
  >> strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_bool_and_lookup,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.subst_def,
        bounded_packed_bool_and_body_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_q_shape6_eval:
  LENGTH radii = 6 /\
  LENGTH center_gradient = 6 /\
  LENGTH packed = 21 /\
  23 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_bool_and»
        [Binop Eq
          (App «candle_cv_list_length»
            [from_cv (bounded_object_q_cv_list radii)]) (Num 6);
         App «candle_cv_bool_and»
          [Binop Eq
            (App «candle_cv_list_length»
              [from_cv (bounded_object_q_cv_list center_gradient)]) (Num 6);
           Binop Eq
            (App «candle_cv_list_length»
              [from_cv (bounded_object_q_cv_list packed)]) (Num 21)]])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule bounded_packed_bool_and_true_one_eval
  >> conj_tac
  >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_packed_compute_eval_binop_eq_num_same
      >> simp [bounded_packed_list_length_eval])
  >> irule bounded_packed_bool_and_true_one_eval
  >> conj_tac
  >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_packed_compute_eval_binop_eq_num_same
      >> simp [bounded_packed_list_length_eval])
  >> irule bounded_packed_compute_eval_binop_eq_num_same
  >> simp [bounded_packed_list_length_eval]
QED

Definition bounded_packed_q_source_interval_upper_cv_def:
  bounded_packed_q_source_interval_upper_cv (Pair lower upper) = upper /\
  bounded_packed_q_source_interval_upper_cv _ = Num 0
End

Theorem bounded_packed_q_source_interval_upper_encoded:
  bounded_packed_q_interval_encoded object_interval ==>
  bounded_object_q_encoded
    (bounded_packed_q_source_interval_upper_cv object_interval)
Proof
  rw
    [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> fs [bounded_packed_q_source_interval_upper_cv_def]
QED

Theorem bounded_packed_q_strict_negative_encoded:
  bounded_object_q_strict_negative_cv value ==>
  bounded_object_q_encoded value
Proof
  rw
    [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_strict_negative_cv_def,
     compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_packed_q_strict_negative_not_zero_le:
  bounded_object_q_strict_negative_cv value ==>
  ~bounded_object_q_le_cv bounded_object_q_zero_cv value
Proof
  strip_tac
  >> `bounded_object_q_encoded value` by
       metis_tac [bounded_packed_q_strict_negative_encoded]
  >> imp_res_tac
       compute_boundedPackedObjectPrimitiveCompareEvalTheory.bounded_packed_q_encoded_components
  >> gvs
       [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_strict_negative_cv_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_compute_eval_if_true_result:
  compute_eval clock ceqs condition (refs:hol_refs) =
      (M_success (Num 1),refs) /\
  compute_eval clock ceqs true_branch refs = result ==>
  compute_eval clock ceqs (If condition true_branch false_branch) refs = result
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     ml_monadBaseTheory.st_ex_bind_def]
QED

Theorem bounded_packed_compute_eval_if_false_result:
  compute_eval clock ceqs condition (refs:hol_refs) =
      (M_success (Num 0),refs) /\
  compute_eval clock ceqs false_branch refs = result ==>
  compute_eval clock ceqs (If condition true_branch false_branch) refs = result
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     ml_monadBaseTheory.st_ex_bind_def]
QED

Theorem bounded_packed_q_zero_le_strict_negative_eval:
  bounded_object_q_strict_negative_cv upper /\
  2 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_le»
        [App «candle_cv_q_zero» [];from_cv upper]) (refs:hol_refs) =
    (M_success (Num 0),refs)
Proof
  strip_tac
  >> `bounded_object_q_encoded upper` by
       metis_tac [bounded_packed_q_strict_negative_encoded]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_le»
            [from_cv bounded_object_q_zero_cv;from_cv upper]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_zero_eval]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_boundedPackedObjectPrimitiveCompareEvalTheory.bounded_packed_q_le_eval,
        compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_encoded,
        bounded_packed_q_strict_negative_not_zero_le,
        compute_execTheory.from_cv_def]
QED

Theorem bounded_packed_q_zero_le_interval_upper_negative_eval:
  bounded_packed_q_interval_encoded object_interval /\
  bounded_object_q_strict_negative_cv
    (bounded_packed_q_source_interval_upper_cv object_interval) /\
  3 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_le»
        [App «candle_cv_q_zero» [];
         Uop Snd (from_cv object_interval)]) (refs:hol_refs) =
    (M_success (Num 0),refs)
Proof
  rw
    [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> fs [bounded_packed_q_source_interval_upper_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_le»
            [from_cv bounded_object_q_zero_cv;from_cv upper]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule
            compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_zero_eval
          >> intLib.ARITH_TAC)
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_snd_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> `~bounded_object_q_le_cv bounded_object_q_zero_cv upper` by
       metis_tac [bounded_packed_q_strict_negative_not_zero_le]
  >> simp
       [compute_boundedPackedObjectPrimitiveCompareEvalTheory.bounded_packed_q_le_eval,
        compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_encoded,
        compute_execTheory.from_cv_def]
QED

Theorem bounded_packed_q_final_pair_eval:
  bounded_packed_q_interval_encoded object_interval /\
  bounded_object_q_strict_negative_cv
    (bounded_packed_q_source_interval_upper_cv object_interval) /\
  4 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (Pair
        (If
          (App «candle_cv_bool_and»
            [from_cv (Num 1);from_cv (Num 1)])
          (If
            (App «candle_cv_q_le»
              [App «candle_cv_q_zero» [];
               Uop Snd (from_cv object_interval)])
            (Num 0) (Num 1))
          (Num 0))
        (Uop Snd (from_cv object_interval))) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (bounded_packed_q_source_interval_upper_cv object_interval))),refs)
Proof
  rw
    [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> fs [bounded_packed_q_source_interval_upper_cv_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |-> `Num 1`,`right_result` |-> `upper`]
           compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_pair_from_results))
  >> conj_tac
  >- (irule bounded_packed_compute_eval_if_true_result
      >> conj_tac
      >- (irule bounded_packed_bool_and_true_one_eval
          >> simp
               [compute_evalTheory.compute_eval_def,
                ml_monadBaseTheory.st_ex_return_def])
      >> irule bounded_packed_compute_eval_if_false_result
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST [`object_interval` |-> `Pair lower upper`]
                bounded_packed_q_zero_le_interval_upper_negative_eval))
          >> simp
               [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def,
                bounded_packed_q_source_interval_upper_cv_def]
          >> intLib.ARITH_TAC)
      >> simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_q_finish6_body_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 /\
  bounded_object_q_strict_negative_cv
    (bounded_packed_q_source_interval_upper_cv
      (bounded_packed_q_source_value_bound6_cv
        radii center_value center_gradient packed)) /\
  200 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (subst
        [(«domain»,from_cv (Num 1));
         («radii»,from_cv (bounded_object_q_cv_list radii));
         («center_value»,from_cv center_value);
         («center_gradient»,from_cv
            (bounded_object_q_cv_list center_gradient));
         («packed»,from_cv (bounded_object_q_cv_list packed))]
        bounded_packed_q_finish6_body) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (bounded_packed_q_source_interval_upper_cv
            (bounded_packed_q_source_value_bound6_cv
              radii center_value center_gradient packed)))),refs)
Proof
  strip_tac
  >> simp
       [bounded_packed_q_finish6_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_value_bound6_cv
          radii center_value center_gradient packed`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_value_bound6_eval
      >> simp [])
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac `Num 1`
  >> conj_tac
  >- (simp [compute_execTheory.from_cv_def]
      >> irule bounded_packed_q_shape6_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`object_interval` |->
              `bounded_packed_q_source_value_bound6_cv
                 radii center_value center_gradient packed`]
           bounded_packed_q_final_pair_eval))
  >> simp
       [compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_source_value_bound6_encoded]
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_q_finish6_unfold:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_object_finish6»
        [from_cv domain_value;from_cv radii;from_cv center_value;
         from_cv center_gradient;from_cv packed]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (subst
        [(«domain»,from_cv domain_value);(«radii»,from_cv radii);
         («center_value»,from_cv center_value);
         («center_gradient»,from_cv center_gradient);
         («packed»,from_cv packed)]
        bounded_packed_q_finish6_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectQuadraticTermAtEvalTheory.bounded_packed_compute_eval_literal_app5
  >> simp [bounded_packed_q_finish6_lookup]
QED

Theorem bounded_packed_q_finish6_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 /\
  bounded_object_q_strict_negative_cv
    (bounded_packed_q_source_interval_upper_cv
      (bounded_packed_q_source_value_bound6_cv
        radii center_value center_gradient packed)) /\
  202 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_object_finish6»
        [from_cv (Num 1);
         from_cv (bounded_object_q_cv_list radii);
         from_cv center_value;
         from_cv (bounded_object_q_cv_list center_gradient);
         from_cv (bounded_object_q_cv_list packed)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (bounded_packed_q_source_interval_upper_cv
            (bounded_packed_q_source_value_bound6_cv
              radii center_value center_gradient packed)))),refs)
Proof
  strip_tac
  >> rw [bounded_packed_q_finish6_unfold]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_q_finish6_body_eval)
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_compute_eval_fst_argument_pair_result:
  compute_eval clock ceqs expression (refs:hol_refs) =
      (M_success (from_cv (Pair left right)),refs) ==>
  compute_eval clock ceqs (Uop Fst expression) refs =
    (M_success (from_cv left),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_fst_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_q_accept6_unfold:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_object_accept6»
        [from_cv domain_value;from_cv radii;from_cv center_value;
         from_cv center_gradient;from_cv packed]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (subst
        [(«domain»,from_cv domain_value);(«radii»,from_cv radii);
         («center_value»,from_cv center_value);
         («center_gradient»,from_cv center_gradient);
         («packed»,from_cv packed)]
        bounded_packed_q_accept6_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectQuadraticTermAtEvalTheory.bounded_packed_compute_eval_literal_app5
  >> simp [bounded_packed_q_accept6_lookup]
QED

Theorem bounded_packed_q_accept6_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 /\
  bounded_object_q_strict_negative_cv
    (bounded_packed_q_source_interval_upper_cv
      (bounded_packed_q_source_value_bound6_cv
        radii center_value center_gradient packed)) /\
  205 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_object_accept6»
        [from_cv (Num 1);
         from_cv (bounded_object_q_cv_list radii);
         from_cv center_value;
         from_cv (bounded_object_q_cv_list center_gradient);
         from_cv (bounded_object_q_cv_list packed)]) (refs:hol_refs) =
    (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> rw [bounded_packed_q_accept6_unfold]
  >> simp
       [bounded_packed_q_accept6_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left` |-> `Num 1`,
            `right` |->
              `bounded_packed_q_source_interval_upper_cv
                 (bounded_packed_q_source_value_bound6_cv
                    radii center_value center_gradient packed)`]
           bounded_packed_compute_eval_fst_argument_pair_result))
  >> qexistsl_tac [`center_gradient`,`center_value`,`packed`,`radii`]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_q_finish6_eval)
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
