(*****************************************************************************
 * Registered evaluator semantics for the historical root-record boundary.
 *
 * The strengthened packet already proves the four positive square-root
 * certificate facts.  This theory connects those object facts to the exact
 * historical CakeML certificate and list-check functions.
 *****************************************************************************)
Theory compute_registeredCase10173RootRecordEval
Ancestors
  compute_registeredCase10173AnalyticProgramSqrtEval
  compute_boundedObjectCertificateDecimal
Libs
  bossLib preamble

Definition registered_case10173_hist_bool_not_body_def:
  registered_case10173_hist_bool_not_body =
    If (Var «value») (Num 0) (Num 1)
End

Definition registered_case10173_hist_bool_and_body_def:
  registered_case10173_hist_bool_and_body =
    If (Var «left») (Var «right») (Num 0)
End

Definition registered_case10173_hist_num_le_body_def:
  registered_case10173_hist_num_le_body =
    App «candle_cv_fs_hist_bool_not»
      [Binop Less (Var «right») (Var «left»)]
End

Definition registered_case10173_hist_root_certificate_body_def:
  registered_case10173_hist_root_certificate_body =
    (Let «input_lower» (Uop Fst (Uop Fst (Var «input»))) (Let «input_upper» (Uop Fst (Uop Snd (Var «input»))) (Let «root_lower_pair» (Uop Fst (Var «root_value»)) (Let «root_upper_pair» (Uop Snd (Var «root_value»)) (Let «root_lower» (Uop Fst (Var «root_lower_pair»)) (Let «root_upper» (Uop Fst (Var «root_upper_pair»)) (Let «root_shape» (App «candle_cv_fs_hist_bool_and» [Uop Ispair (Var «root_value»);App «candle_cv_fs_hist_bool_and» [Uop Ispair (Var «root_lower_pair»);App «candle_cv_fs_hist_bool_and» [Uop Ispair (Var «root_upper_pair»);App «candle_cv_fs_hist_bool_and» [App «candle_cv_fs_hist_bool_not» [Uop Ispair (Var «root_lower»)];App «candle_cv_fs_hist_bool_and» [App «candle_cv_fs_hist_bool_not» [Uop Ispair (Var «root_upper»)];App «candle_cv_fs_hist_bool_and» [Binop Eq (Uop Snd (Var «root_lower_pair»)) (Num 0);Binop Eq (Uop Snd (Var «root_upper_pair»)) (Num 0)]]]]]]) (App «candle_cv_fs_hist_bool_and» [Var «root_shape»;App «candle_cv_fs_hist_bool_and» [Binop Less (Num 0) (Var «input_lower»);App «candle_cv_fs_hist_bool_and» [App «candle_cv_fs_hist_num_le» [Var «input_lower»;Var «input_upper»];App «candle_cv_fs_hist_bool_and» [Binop Less (Num 0) (Var «root_lower»);App «candle_cv_fs_hist_bool_and» [App «candle_cv_fs_hist_num_le» [Var «root_lower»;Var «root_upper»];App «candle_cv_fs_hist_bool_and» [App «candle_cv_fs_hist_num_le» [Binop Mul (Var «root_lower») (Var «root_lower»);Binop Mul (Var «input_lower») (App «candle_cv_fs_scale» [])];App «candle_cv_fs_hist_num_le» [Binop Mul (Var «input_upper») (App «candle_cv_fs_scale» []);Binop Mul (Var «root_upper») (Var «root_upper»)]]]]]]]))))))))
End

Definition registered_case10173_hist_positive_root_certificate_body_def:
  registered_case10173_hist_positive_root_certificate_body =
    App «candle_cv_fs_hist_bool_and»
      [Binop Eq (Uop Snd (Uop Fst (Var «input»))) (Num 0);
       App «candle_cv_fs_hist_bool_and»
         [Binop Eq (Uop Snd (Uop Snd (Var «input»))) (Num 0);
          App «candle_cv_fs_hist_root_certificate»
            [Var «input»;Var «root_value»]]]
End

Theorem registered_case10173_hist_bool_not_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_bool_not» =
    SOME ([«value»],registered_case10173_hist_bool_not_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_bool_and_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_bool_and» =
    SOME ([«left»;«right»],registered_case10173_hist_bool_and_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_num_le_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_num_le» =
    SOME ([«left»;«right»],registered_case10173_hist_num_le_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_root_certificate_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_root_certificate» =
    SOME
      ([«input»;«root_value»],
       registered_case10173_hist_root_certificate_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_positive_root_certificate_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_positive_root_certificate» =
    SOME
      ([«input»;«root_value»],
       registered_case10173_hist_positive_root_certificate_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_scale_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_scale» =
    SOME ([],Num 1000000000000)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_positive_root_certificate_eval:
  bounded_object_fs_hist_positive_root_certificate
      (Pair (Pair (Num input_lower) (Num 0))
        (Pair (Num input_upper) (Num 0)))
      (Pair (Pair (Num root_lower) (Num 0))
        (Pair (Num root_upper) (Num 0))) = Num 1 /\
  40 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_root_certificate»
        [from_cv
          (Pair (Pair (Num input_lower) (Num 0))
            (Pair (Num input_upper) (Num 0)));
         from_cv
          (Pair (Pair (Num root_lower) (Num 0))
            (Pair (Num root_upper) (Num 0)))]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  rw
    [compute_boundedObjectCertificateDecimalTheory.bounded_object_fs_hist_positive_root_certificate_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_hist_positive_root_certificate_lookup,
        registered_case10173_hist_positive_root_certificate_body_def,
        registered_case10173_hist_root_certificate_lookup,
        registered_case10173_hist_root_certificate_body_def,
        registered_case10173_hist_bool_and_lookup,
        registered_case10173_hist_bool_and_body_def,
        registered_case10173_hist_bool_not_lookup,
        registered_case10173_hist_bool_not_body_def,
        registered_case10173_hist_num_le_lookup,
        registered_case10173_hist_num_le_body_def,
        registered_case10173_fs_scale_lookup,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_hist_bool_and_true_one_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      first_expression (refs:hol_refs) = (M_success (Num 1),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      second_expression refs = (M_success (Num 1),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_bool_and»
        [first_expression;second_expression]) refs =
    (M_success (Num 1),refs)
Proof
  Cases_on `clock`
  >- simp []
  >> strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_hist_bool_and_lookup,
        registered_case10173_hist_bool_and_body_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.subst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Definition registered_case10173_hist_root_list_check_body_def:
  registered_case10173_hist_root_list_check_body =
    If (Uop Ispair (Var «inputs»))
      (If (Uop Ispair (Var «roots»))
        (App «candle_cv_fs_hist_bool_and»
          [App «candle_cv_fs_hist_positive_root_certificate»
            [Uop Fst (Var «inputs»);Uop Fst (Var «roots»)];
           App «candle_cv_fs_hist_root_list_check»
            [Uop Snd (Var «inputs»);Uop Snd (Var «roots»)]])
        (Num 0))
      (If (Uop Ispair (Var «roots»))
        (Num 0)
        (App «candle_cv_fs_hist_bool_and»
          [Binop Eq (Var «inputs») (Num 0);
           Binop Eq (Var «roots») (Num 0)]))
End

Theorem registered_case10173_hist_root_list_check_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_root_list_check» =
    SOME
      ([«inputs»;«roots»],
       registered_case10173_hist_root_list_check_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_root_list_check_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_root_list_check»
        [from_cv inputs;from_cv roots]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«inputs»,from_cv inputs);(«roots»,from_cv roots)]
        registered_case10173_hist_root_list_check_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_hist_root_list_check_lookup]
QED

Theorem registered_case10173_hist_root_list_check_nil_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_root_list_check»
        [from_cv (Num 0);from_cv (Num 0)]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp [registered_case10173_hist_root_list_check_unfold]
  >> simp
       [registered_case10173_hist_root_list_check_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        registered_case10173_hist_bool_and_lookup,
        registered_case10173_hist_bool_and_body_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_hist_root_list_check_cons_eval:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_root_certificate»
        [from_cv input;from_cv root]) (refs:hol_refs) =
      (M_success (Num 1),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_root_list_check»
        [from_cv inputs;from_cv roots]) refs =
      (M_success (Num 1),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_root_list_check»
        [from_cv (Pair input inputs);from_cv (Pair root roots)]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp [registered_case10173_hist_root_list_check_unfold]
  >> simp
       [registered_case10173_hist_root_list_check_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> irule registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_positive_root_certificate»
            [Uop Fst (Pair (from_cv input) (from_cv inputs));
             Uop Fst (Pair (from_cv root) (from_cv roots))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_positive_root_certificate»
            [from_cv input;from_cv root]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
      >> fs [])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_root_list_check»
          [Uop Snd (Pair (from_cv input) (from_cv inputs));
           Uop Snd (Pair (from_cv root) (from_cv roots))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_root_list_check»
          [from_cv inputs;from_cv roots]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> fs []
QED

Definition registered_case10173_hist_root_inputs_body_def:
  registered_case10173_hist_root_inputs_body =
    Let «center_boxes»
      (App «candle_cv_q_center_environment_list» [Var «boxes»])
      (Let «center_environment»
        (App «candle_cv_fs_interval_list_of_q» [Var «center_boxes»])
        (Let «box_environment»
          (App «candle_cv_fs_interval_list_of_q» [Var «boxes»])
          (Pair
            (App «candle_cv_fs_angle_delta_value»
              [Var «center_environment»])
            (Pair
              (App «candle_cv_fs_angle_interval_scale»
                [Num 4;
                 App «candle_cv_fs_interval_lookup»
                   [Num 0;Var «center_environment»]])
              (Pair
                (App «candle_cv_fs_hist_second_value»
                  [App «candle_cv_fs_hist_delta_second»
                    [Var «box_environment»]])
                (Pair
                  (App «candle_cv_fs_angle_interval_scale»
                    [Num 4;
                     App «candle_cv_fs_interval_lookup»
                       [Num 0;Var «box_environment»]])
                  (Num 0)))))))
End

Definition registered_case10173_hist_root_record_check_body_def:
  registered_case10173_hist_root_record_check_body =
    App «candle_cv_fs_hist_root_list_check»
      [App «candle_cv_case10173_hist_root_inputs» [Var «boxes»];
       Var «roots»]
End

Theorem registered_case10173_hist_root_inputs_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_case10173_hist_root_inputs» =
    SOME ([«boxes»],registered_case10173_hist_root_inputs_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_root_record_check_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_case10173_hist_root_record_check» =
    SOME
      ([«boxes»;«roots»],
       registered_case10173_hist_root_record_check_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_root_inputs_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_root_inputs» [from_cv boxes])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«boxes»,from_cv boxes)]
        registered_case10173_hist_root_inputs_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_hist_root_inputs_lookup]
QED

Theorem registered_case10173_hist_root_record_check_eval:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_root_inputs» [from_cv boxes])
      (refs:hol_refs) = (M_success (from_cv inputs),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_root_list_check»
        [from_cv inputs;from_cv roots]) refs =
      (M_success (Num 1),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_root_record_check»
        [from_cv boxes;from_cv roots]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_case10173_hist_root_record_check»
          [from_cv boxes;from_cv roots]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (subst
          [(«boxes»,from_cv boxes);(«roots»,from_cv roots)]
          registered_case10173_hist_root_record_check_body) refs` by
       (irule
          compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
        >> simp [registered_case10173_hist_root_record_check_lookup])
  >> pop_assum SUBST1_TAC
  >> simp
       [registered_case10173_hist_root_record_check_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_root_list_check»
          [App «candle_cv_case10173_hist_root_inputs» [from_cv boxes];
           from_cv roots]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_root_list_check»
          [from_cv inputs;from_cv roots]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv])
  >> fs []
QED

val _ = export_theory ();
