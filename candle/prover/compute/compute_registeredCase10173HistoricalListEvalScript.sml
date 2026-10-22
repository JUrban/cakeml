(*****************************************************************************
 * Registered evaluator semantics for historical interval constants and
 * fixed-arity list constructors.
 *
 * These small carriers are shared by the center gradient, Hessian, and the
 * recursive interval sums.  Keeping them above the changing analytic proofs
 * gives those proofs a cheap, reusable list boundary.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalListEval
Ancestors
  compute_registeredCase10173HistoricalIntervalEval
Libs
  bossLib preamble

Definition registered_case10173_fs_one_body_def:
  registered_case10173_fs_one_body =
    Pair (App «candle_cv_fs_scale» []) (Num 0)
End

Definition registered_case10173_fs_interval_one_body_def:
  registered_case10173_fs_interval_one_body =
    Pair (App «candle_cv_fs_one» []) (App «candle_cv_fs_one» [])
End

Definition registered_case10173_cv_list_def:
  registered_case10173_cv_list ([]:cv list) = (Num 0:cv) /\
  registered_case10173_cv_list (value::values) =
    Pair value (registered_case10173_cv_list values)
End

Definition registered_case10173_interval_zero_cv_def:
  registered_case10173_interval_zero_cv =
    Pair (Pair (Num 0) (Num 0)) (Pair (Num 0) (Num 0))
End

Definition registered_case10173_fs_interval_sum_object_def:
  registered_case10173_fs_interval_sum_object ([]:cv list) =
      SOME registered_case10173_interval_zero_cv /\
  registered_case10173_fs_interval_sum_object (value::values) =
    case registered_case10173_fs_interval_sum_object values of
    | NONE => NONE
    | SOME rest => bounded_object_fs_interval_add value rest
End

Definition registered_case10173_fs_angle_six_body_def:
  registered_case10173_fs_angle_six_body =
    Pair (Var «a»)
      (Pair (Var «b»)
        (Pair (Var «c»)
          (Pair (Var «d»)
            (Pair (Var «e»)
              (Pair (Var «f») (Num 0))))))
End

Definition registered_case10173_fs_angle_seven_body_def:
  registered_case10173_fs_angle_seven_body =
    Pair (Var «a»)
      (Pair (Var «b»)
        (Pair (Var «c»)
          (Pair (Var «d»)
            (Pair (Var «e»)
              (Pair (Var «f»)
                (Pair (Var «g») (Num 0)))))))
End

Definition registered_case10173_fs_angle_ten_body_def:
  registered_case10173_fs_angle_ten_body =
    Pair (Var «a»)
      (Pair (Var «b»)
        (Pair (Var «c»)
          (Pair (Var «d»)
            (Pair (Var «e»)
              (Pair (Var «f»)
                (Pair (Var «g»)
                  (Pair (Var «h»)
                    (Pair (Var «i»)
                      (Pair (Var «j») (Num 0))))))))))
End

Definition registered_case10173_fs_angle_interval_sum_body_def:
  registered_case10173_fs_angle_interval_sum_body =
    If (Uop Ispair (Var «items»))
      (App «candle_cv_fs_interval_add»
        [Uop Fst (Var «items»);
         App «candle_cv_fs_angle_interval_sum»
           [Uop Snd (Var «items»)]])
      (App «candle_cv_fs_interval_zero» [])
End

Theorem registered_case10173_fs_one_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_one» =
    SOME ([],registered_case10173_fs_one_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_one_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_one» =
    SOME ([],registered_case10173_fs_interval_one_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_six_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_six» =
    SOME
      ([«a»;«b»;«c»;«d»;«e»;«f»],
       registered_case10173_fs_angle_six_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_seven_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_seven» =
    SOME
      ([«a»;«b»;«c»;«d»;«e»;«f»;«g»],
       registered_case10173_fs_angle_seven_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_ten_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_ten» =
    SOME
      ([«a»;«b»;«c»;«d»;«e»;«f»;«g»;«h»;«i»;«j»],
       registered_case10173_fs_angle_ten_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_interval_sum_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_interval_sum» =
    SOME ([«items»],registered_case10173_fs_angle_interval_sum_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_interval_sum_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum» [from_cv items])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«items»,from_cv items)]
        registered_case10173_fs_angle_interval_sum_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_angle_interval_sum_lookup]
QED

Theorem registered_case10173_fs_one_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_one» []) (refs:hol_refs) =
    (M_success
      (from_cv (Pair (Num 1000000000000) (Num 0))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_one_lookup,
        registered_case10173_fs_one_body_def,
        compute_execTheory.from_cv_def,
        compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_interval_zero_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_zero» []) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num 0) (Num 0))
          (Pair (Num 0) (Num 0)))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_interval_zero_lookup,
        compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_interval_zero_body_def,
        compute_registeredCase10173TaylorDotEvalTheory.registered_case10173_fs_zero_eval,
        compute_execTheory.from_cv_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_interval_one_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_one» []) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num 1000000000000) (Num 0))
          (Pair (Num 1000000000000) (Num 0)))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_interval_one_lookup,
        registered_case10173_fs_interval_one_body_def,
        compute_execTheory.from_cv_def,
        registered_case10173_fs_one_lookup,
        registered_case10173_fs_one_body_def,
        compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_angle_six_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_six»
        [from_cv a;from_cv b;from_cv c;from_cv d;from_cv e;from_cv f])
      (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_list [a;b;c;d;e;f])),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_angle_six_lookup,
        registered_case10173_fs_angle_six_body_def,
        registered_case10173_cv_list_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_angle_seven_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_seven»
        [from_cv a;from_cv b;from_cv c;from_cv d;from_cv e;from_cv f;
         from_cv g]) (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_list [a;b;c;d;e;f;g])),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_angle_seven_lookup,
        registered_case10173_fs_angle_seven_body_def,
        registered_case10173_cv_list_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_angle_ten_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_ten»
        [from_cv a;from_cv b;from_cv c;from_cv d;from_cv e;from_cv f;
         from_cv g;from_cv h;from_cv i;from_cv j]) (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_cv_list [a;b;c;d;e;f;g;h;i;j])),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_angle_ten_lookup,
        registered_case10173_fs_angle_ten_body_def,
        registered_case10173_cv_list_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_angle_interval_sum_object_list_eval:
  !values result clock refs.
    registered_case10173_fs_interval_sum_object values = SOME result /\
    LENGTH values + 5 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_angle_interval_sum»
          [from_cv (registered_case10173_cv_list values)])
        (refs:hol_refs) =
      (M_success (from_cv result),refs)
Proof
  Induct_on `values`
  >- (rpt strip_tac
      >> gvs
           [registered_case10173_fs_interval_sum_object_def,
            registered_case10173_cv_list_def]
      >> rw
           [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST [`items` |-> `(Num 0:cv)`]
                registered_case10173_fs_angle_interval_sum_unfold)]
      >> simp
           [registered_case10173_fs_angle_interval_sum_body_def,
            compute_evalTheory.subst_def]
      >> rw
           [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST [`argument` |-> `(Num 0:cv)`]
                compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
      >> simp
           [registered_case10173_interval_zero_cv_def,
            registered_case10173_fs_interval_zero_eval,
            compute_execTheory.from_cv_def]
      >> intLib.ARITH_TAC)
  >> rpt strip_tac
  >> Cases_on `registered_case10173_fs_interval_sum_object values`
  >> gvs [registered_case10173_fs_interval_sum_object_def]
  >> simp [registered_case10173_cv_list_def,compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`items` |->
               `(Pair h (registered_case10173_cv_list values):cv)`]
            registered_case10173_fs_angle_interval_sum_unfold)]
  >> simp
       [registered_case10173_fs_angle_interval_sum_body_def,
        compute_evalTheory.subst_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair h (registered_case10173_cv_list values):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_angle_interval_sum»
          [from_cv (registered_case10173_cv_list values)]) refs =
      (M_success (from_cv x),refs)` by
       (first_x_assum irule
        >> simp []
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_angle_interval_sum»
          [Uop Snd
            (Pair (from_cv h)
              (from_cv (registered_case10173_cv_list values)))]) refs =
      (M_success (from_cv x),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_angle_interval_sum»
             [Uop Snd
               (Pair (from_cv h)
                 (from_cv (registered_case10173_cv_list values)))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_angle_interval_sum»
             [from_cv (registered_case10173_cv_list values)]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
        >> rw []
        >> simp [])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_add»
          [Uop Fst
            (Pair (from_cv h)
              (from_cv (registered_case10173_cv_list values)));
           App «candle_cv_fs_angle_interval_sum»
             [Uop Snd
               (Pair (from_cv h)
                 (from_cv (registered_case10173_cv_list values)))]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_add» [from_cv h;from_cv x]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> conj_tac >- intLib.ARITH_TAC
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
  >> rw []
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_add_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
