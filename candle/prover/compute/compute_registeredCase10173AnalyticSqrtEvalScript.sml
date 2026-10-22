(*****************************************************************************
 * Registered evaluator semantics for analytic square-root data plumbing.
 *
 * These functions are structural preparation, not numerical checking.  A
 * general evaluator theorem lets the authenticated fast path account for
 * them once per source-program shape instead of replaying them per cell.
 *****************************************************************************)
Theory compute_registeredCase10173AnalyticSqrtEval
Ancestors
  compute_registeredCase10173AuthenticatedEval
Libs
  bossLib preamble

Definition registered_case10173_analytic_instruction_is_sqrt_body_def:
  registered_case10173_analytic_instruction_is_sqrt_body =
    If (Uop Ispair (Var «instruction»))
      (Binop Eq (Uop Fst (Var «instruction»)) (Num 1))
      (Num 0)
End

Definition registered_case10173_analytic_instruction_patch_sqrt_body_def:
  registered_case10173_analytic_instruction_patch_sqrt_body =
    If (Uop Ispair (Var «instruction»))
      (If (Binop Eq (Uop Fst (Var «instruction»)) (Num 1))
        (If (Uop Ispair (Var «intervals»))
          (Pair (Uop Snd (Var «intervals»))
            (Pair (Num 1) (Uop Fst (Var «intervals»))))
          (Pair (Var «intervals») (Var «instruction»)))
        (Pair (Var «intervals») (Var «instruction»)))
      (Pair (Var «intervals») (Var «instruction»))
End

Theorem registered_case10173_analytic_instruction_is_sqrt_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_analytic_instruction_is_sqrt» =
    SOME
      ([«instruction»],
       registered_case10173_analytic_instruction_is_sqrt_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_analytic_instruction_patch_sqrt_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_analytic_instruction_patch_sqrt» =
    SOME
      ([«intervals»;«instruction»],
       registered_case10173_analytic_instruction_patch_sqrt_body)
Proof
  EVAL_TAC
QED

Definition registered_case10173_analytic_instruction_is_sqrt_cv_def:
  registered_case10173_analytic_instruction_is_sqrt_cv
      (Pair tag payload : cv) =
    (if tag = Num 1 then Num 1 else Num 0) /\
  registered_case10173_analytic_instruction_is_sqrt_cv (Num n) = Num 0
End

Definition registered_case10173_analytic_instruction_patch_sqrt_cv_def:
  registered_case10173_analytic_instruction_patch_sqrt_cv intervals
      (Pair tag payload : cv) =
    (if tag = Num 1 then
       case intervals of
       | Pair interval rest => Pair rest (Pair (Num 1) interval)
       | Num n => Pair intervals (Pair tag payload)
     else Pair intervals (Pair tag payload)) /\
  registered_case10173_analytic_instruction_patch_sqrt_cv intervals
      (Num n) = Pair intervals (Num n)
End

Theorem compute_eval_literal_app2:
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
         (second_name,from_cv second_argument)] body)
      refs
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

Theorem registered_case10173_analytic_instruction_is_sqrt_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_analytic_instruction_is_sqrt»
        [from_cv instruction]) (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_analytic_instruction_is_sqrt_cv
          instruction)),refs)
Proof
  Cases_on `clock`
  >> simp []
  >> Cases_on `instruction`
  >- simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_analytic_instruction_is_sqrt_lookup,
        registered_case10173_analytic_instruction_is_sqrt_body_def,
        registered_case10173_analytic_instruction_is_sqrt_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `c`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_analytic_instruction_is_sqrt_lookup,
        registered_case10173_analytic_instruction_is_sqrt_body_def,
        registered_case10173_analytic_instruction_is_sqrt_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> IF_CASES_TAC
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_analytic_instruction_patch_sqrt_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_analytic_instruction_patch_sqrt»
        [from_cv intervals;from_cv instruction]) (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_analytic_instruction_patch_sqrt_cv
          intervals instruction)),refs)
Proof
  Cases_on `clock`
  >> simp []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_analytic_instruction_patch_sqrt_lookup,
        registered_case10173_analytic_instruction_patch_sqrt_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `instruction`
  >- simp
       [registered_case10173_analytic_instruction_patch_sqrt_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `c`
  >> Cases_on `intervals`
  >> simp
       [registered_case10173_analytic_instruction_patch_sqrt_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> IF_CASES_TAC
  >> simp [compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
