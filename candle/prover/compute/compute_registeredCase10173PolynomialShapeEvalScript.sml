(*****************************************************************************
 * Registered evaluator semantics for polynomial-state shape constructors.
 *
 * Constant and variable polynomial instructions build zero gradients and
 * Hessians by traversing the authenticated dimension list.  These lemmas
 * expose those traversals once, so later polynomial-result refinements do not
 * replay their source evaluator definitions for every packet.
 *****************************************************************************)
Theory compute_registeredCase10173PolynomialShapeEval
Ancestors
  compute_registeredCase10173HistoricalBasicEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_interval_zeros_body_def:
  registered_case10173_fs_interval_zeros_body =
    If (Uop Ispair (Var «items»))
      (Pair (App «candle_cv_fs_interval_zero» [])
        (App «candle_cv_fs_interval_zeros» [Uop Snd (Var «items»)]))
      (Num 0)
End

Definition registered_case10173_fs_interval_zero_matrix_body_def:
  registered_case10173_fs_interval_zero_matrix_body =
    If (Uop Ispair (Var «row_lists»))
      (Pair (App «candle_cv_fs_interval_zeros» [Var «width»])
        (App «candle_cv_fs_interval_zero_matrix»
          [Var «width»;Uop Snd (Var «row_lists»)]))
      (Num 0)
End

Theorem registered_case10173_fs_interval_zeros_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_zeros» =
    SOME ([«items»],registered_case10173_fs_interval_zeros_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_zero_matrix_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_zero_matrix» =
    SOME
      ([«width»;«row_lists»],
       registered_case10173_fs_interval_zero_matrix_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_zeros_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_zeros» [from_cv items])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«items»,from_cv items)]
        registered_case10173_fs_interval_zeros_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_interval_zeros_lookup]
QED

Theorem registered_case10173_fs_interval_zero_matrix_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_zero_matrix»
        [from_cv width;from_cv row_lists]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«width»,from_cv width);(«row_lists»,from_cv row_lists)]
        registered_case10173_fs_interval_zero_matrix_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_interval_zero_matrix_lookup]
QED

Theorem registered_case10173_fs_interval_zeros_nil_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_zeros» [from_cv (Num 0)])
      (refs:hol_refs) =
    (M_success (from_cv (Num 0)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_interval_zeros_unfold]
  >> simp
       [registered_case10173_fs_interval_zeros_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_interval_zeros_cons_eval:
  3 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_zeros» [from_cv items])
      (refs:hol_refs) = (M_success (from_cv zeros),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_zeros»
        [from_cv (Pair item items)]) refs =
    (M_success
      (from_cv
        (Pair
          (bounded_interval64_object_cv bounded_interval64_zero)
          zeros)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_interval_zeros_unfold]
  >> simp
       [registered_case10173_fs_interval_zeros_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_zeros»
          [Uop Snd (Pair (from_cv item) (from_cv items))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_zeros» [from_cv items]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_zero_eval,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedIntervalListTheory.bounded_interval64_zero_def]
QED

Theorem registered_case10173_fs_interval_zeros_object_eval:
  !items clock refs.
    4 * (LENGTH items + 1) < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_zeros»
          [from_cv (bounded_interval64_object_cv_list items)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_interval64_object_cv_list
            (REPLICATE (LENGTH items) bounded_interval64_zero))),refs)
Proof
  Induct_on `items`
  >- (rpt gen_tac
      >> strip_tac
      >> simp_tac std_ss
           [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
            LENGTH, REPLICATE]
      >> irule registered_case10173_fs_interval_zeros_nil_eval
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> strip_tac
  >> PURE_REWRITE_TAC
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        LENGTH, REPLICATE]
  >> irule registered_case10173_fs_interval_zeros_cons_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> qpat_x_assum `!clock refs. _`
       (qspecl_then [`clock - 1`,`refs`] mp_tac)
  >> impl_tac
  >- (qpat_x_assum `4 * (LENGTH (h::items) + 1) < clock` mp_tac
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp []
QED

Theorem registered_case10173_fs_interval_zero_matrix_nil_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_zero_matrix»
        [from_cv width;from_cv (Num 0)]) (refs:hol_refs) =
    (M_success (from_cv (Num 0)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_interval_zero_matrix_unfold]
  >> simp
       [registered_case10173_fs_interval_zero_matrix_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_interval_zero_matrix_cons_eval:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_zeros» [from_cv width])
      (refs:hol_refs) = (M_success (from_cv zero_row),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_zero_matrix»
        [from_cv width;from_cv row_lists]) refs =
    (M_success (from_cv zero_rows),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_zero_matrix»
        [from_cv width;from_cv (Pair row row_lists)]) refs =
    (M_success (from_cv (Pair zero_row zero_rows)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_interval_zero_matrix_unfold]
  >> simp
       [registered_case10173_fs_interval_zero_matrix_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> conj_tac >- simp []
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_zero_matrix»
          [from_cv width;
           Uop Snd (Pair (from_cv row) (from_cv row_lists))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_zero_matrix»
          [from_cv width;from_cv row_lists]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> conj_tac >- intLib.ARITH_TAC
        >> conj_tac >- simp [compute_execProofTheory.compute_eval_from_cv]
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> simp []
QED

Theorem registered_case10173_fs_interval_zero_matrix_object_eval:
  !rows clock refs.
    4 * (LENGTH width + LENGTH rows + 2) < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_zero_matrix»
          [from_cv (bounded_interval64_object_cv_list width);
           from_cv (bounded_interval64_object_cv_list rows)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_interval64_object_cv_matrix
            (REPLICATE (LENGTH rows)
              (REPLICATE (LENGTH width) bounded_interval64_zero)))),refs)
Proof
  Induct_on `rows`
  >- (rpt gen_tac
      >> strip_tac
      >> simp_tac std_ss
           [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
            compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def,
            LENGTH, REPLICATE]
      >> irule registered_case10173_fs_interval_zero_matrix_nil_eval
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> strip_tac
  >> PURE_REWRITE_TAC
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def,
        LENGTH, REPLICATE]
  >> irule registered_case10173_fs_interval_zero_matrix_cons_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (qpat_x_assum `!clock refs. _`
        (qspecl_then [`clock - 1`,`refs`] mp_tac)
      >> impl_tac
      >- (qpat_x_assum
            `4 * (LENGTH width + LENGTH (h::rows) + 2) < clock` mp_tac
          >> simp []
          >> intLib.ARITH_TAC)
      >> simp [])
  >> irule registered_case10173_fs_interval_zeros_object_eval
  >> qpat_x_assum
       `4 * (LENGTH width + LENGTH (h::rows) + 2) < clock` mp_tac
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
