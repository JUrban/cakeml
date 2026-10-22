(*****************************************************************************
 * Registered evaluator semantics for recursive analytic square-root data.
 *
 * The source program is traversed once to check that its square-root
 * instructions consume exactly the supplied interval data, and once to
 * substitute that data.  These general evaluator theorems keep that
 * structural preparation out of the per-cell numerical refinement proof.
 *****************************************************************************)
Theory compute_registeredCase10173AnalyticProgramSqrtEval
Ancestors
  compute_registeredCase10173AnalyticSqrtEval
Libs
  bossLib preamble

Definition registered_case10173_analytic_program_sqrt_data_exact_body_def:
  registered_case10173_analytic_program_sqrt_data_exact_body =
    If (Uop Ispair (Var «program»))
      (If
        (App «candle_cv_analytic_instruction_is_sqrt»
          [Uop Fst (Var «program»)])
        (If (Uop Ispair (Var «intervals»))
          (App «candle_cv_analytic_program_sqrt_data_exact»
            [Uop Snd (Var «intervals»);Uop Snd (Var «program»)])
          (Num 0))
        (App «candle_cv_analytic_program_sqrt_data_exact»
          [Var «intervals»;Uop Snd (Var «program»)]))
      (If (Uop Ispair (Var «intervals»)) (Num 0) (Num 1))
End

Definition registered_case10173_analytic_program_patch_sqrt_body_def:
  registered_case10173_analytic_program_patch_sqrt_body =
    If (Uop Ispair (Var «program»))
      (Let «patched_instruction»
        (App «candle_cv_analytic_instruction_patch_sqrt»
          [Var «intervals»;Uop Fst (Var «program»)])
        (Let «patched_program»
          (App «candle_cv_analytic_program_patch_sqrt»
            [Uop Fst (Var «patched_instruction»);
             Uop Snd (Var «program»)])
          (Pair (Uop Fst (Var «patched_program»))
            (Pair (Uop Snd (Var «patched_instruction»))
              (Uop Snd (Var «patched_program»))))))
      (Pair (Var «intervals») (Var «program»))
End

Theorem registered_case10173_analytic_program_sqrt_data_exact_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_analytic_program_sqrt_data_exact» =
    SOME
      ([«intervals»;«program»],
       registered_case10173_analytic_program_sqrt_data_exact_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_analytic_program_patch_sqrt_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_analytic_program_patch_sqrt» =
    SOME
      ([«intervals»;«program»],
       registered_case10173_analytic_program_patch_sqrt_body)
Proof
  EVAL_TAC
QED

Definition registered_case10173_analytic_program_sqrt_data_exact_cv_def:
  registered_case10173_analytic_program_sqrt_data_exact_cv intervals
      (Pair instruction program : cv) =
    (if registered_case10173_analytic_instruction_is_sqrt_cv instruction =
          Num 1 then
       case intervals of
       | Pair interval remaining =>
           registered_case10173_analytic_program_sqrt_data_exact_cv
             remaining program
       | Num n => Num 0
     else
       registered_case10173_analytic_program_sqrt_data_exact_cv
         intervals program) /\
  registered_case10173_analytic_program_sqrt_data_exact_cv intervals
      (Num n) =
    (case intervals of
     | Pair interval remaining => Num 0
     | Num m => Num 1)
End

Definition registered_case10173_analytic_program_patch_sqrt_cv_def:
  registered_case10173_analytic_program_patch_sqrt_cv intervals
      (Pair instruction program : cv) =
    (case
       registered_case10173_analytic_instruction_patch_sqrt_cv
         intervals instruction
     of
     | Pair remaining patched_instruction =>
         (case
            registered_case10173_analytic_program_patch_sqrt_cv
              remaining program
          of
          | Pair final_remaining patched_program =>
              Pair final_remaining
                (Pair patched_instruction patched_program)
          | Num n => Num n)
     | Num n => Num n) /\
  registered_case10173_analytic_program_patch_sqrt_cv intervals
      (Num n) = Pair intervals (Num n)
End

Theorem registered_case10173_analytic_program_sqrt_data_exact_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_analytic_program_sqrt_data_exact»
        [from_cv intervals;from_cv program]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«intervals»,from_cv intervals);(«program»,from_cv program)]
        registered_case10173_analytic_program_sqrt_data_exact_body) refs
Proof
  strip_tac
  >> irule compute_eval_literal_app2
  >> simp
       [registered_case10173_analytic_program_sqrt_data_exact_lookup]
QED

Theorem registered_case10173_analytic_instruction_is_sqrt_fst_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_analytic_instruction_is_sqrt»
        [Uop Fst (Pair (from_cv instruction) (from_cv program))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_analytic_instruction_is_sqrt_cv
          instruction)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_instruction_is_sqrt»
          [Uop Fst
            (Pair (from_cv instruction) (from_cv program))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_instruction_is_sqrt»
          [from_cv instruction]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
  >> pop_assum SUBST1_TAC
  >> irule registered_case10173_analytic_instruction_is_sqrt_eval
  >> simp []
QED

Theorem registered_case10173_analytic_program_sqrt_data_exact_eval_from_results:
  !program intervals interval_expression program_expression clock refs.
    cv_size program + 2 < clock /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      interval_expression (refs:hol_refs) =
        (M_success (from_cv intervals),refs) /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      program_expression refs = (M_success (from_cv program),refs) ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_program_sqrt_data_exact»
          [interval_expression;program_expression]) refs =
      (M_success
        (from_cv
          (registered_case10173_analytic_program_sqrt_data_exact_cv
            intervals program)),refs)
Proof
  Induct_on `program`
  >- (rpt strip_tac
      >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
            (App «candle_cv_analytic_program_sqrt_data_exact»
              [interval_expression;program_expression]) refs =
          compute_eval clock registered_case10173_historical_chunk16_ceqs
            (App «candle_cv_analytic_program_sqrt_data_exact»
              [from_cv intervals;from_cv (Num n)]) refs` by
           (irule
              compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
            >> simp [])
      >> pop_assum SUBST1_TAC
      >> simp
           [registered_case10173_analytic_program_sqrt_data_exact_unfold,
            registered_case10173_analytic_program_sqrt_data_exact_body_def,
            registered_case10173_analytic_program_sqrt_data_exact_cv_def,
            compute_evalTheory.subst_def]
      >> Cases_on `intervals`
      >> simp
           [compute_execTheory.from_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_program_sqrt_data_exact»
          [interval_expression;program_expression]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_program_sqrt_data_exact»
          [from_cv intervals;from_cv (Pair program program')]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp [])
  >> pop_assum SUBST1_TAC
  >> simp
       [registered_case10173_analytic_program_sqrt_data_exact_unfold,
        registered_case10173_analytic_program_sqrt_data_exact_body_def,
        registered_case10173_analytic_program_sqrt_data_exact_cv_def,
        compute_evalTheory.subst_def]
  >> simp
       [compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> `0 < clock - 1` by fs [cvTheory.cv_size_def]
  >> `!remaining.
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_analytic_program_sqrt_data_exact»
            [from_cv remaining;
             Uop Snd (Pair (from_cv program) (from_cv program'))]) refs =
        (M_success
          (from_cv
            (registered_case10173_analytic_program_sqrt_data_exact_cv
              remaining program')),refs)` by
       (gen_tac
        >> qpat_x_assum
             `!intervals interval_expression program_expression clock refs.
                cv_size program' + 2 < clock /\ _ ==> _`
             (qspecl_then
               [`remaining`,`from_cv remaining`,
                `Uop Snd (Pair (from_cv program) (from_cv program'))`,
                `clock - 1`,`refs`] mp_tac)
        >> fs
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components,
              compute_execProofTheory.compute_eval_from_cv,
              cvTheory.cv_size_def])
  >> `!interval remaining.
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_analytic_program_sqrt_data_exact»
            [Uop Snd (from_cv (Pair interval remaining));
             Uop Snd (Pair (from_cv program) (from_cv program'))]) refs =
        (M_success
          (from_cv
            (registered_case10173_analytic_program_sqrt_data_exact_cv
              remaining program')),refs)` by
       (rpt gen_tac
        >> qpat_x_assum
             `!intervals interval_expression program_expression clock refs.
                cv_size program' + 2 < clock /\ _ ==> _`
             (qspecl_then
               [`remaining`,`Uop Snd (from_cv (Pair interval remaining))`,
                `Uop Snd (Pair (from_cv program) (from_cv program'))`,
                `clock - 1`,`refs`] mp_tac)
        >> fs
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_pair,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components,
              compute_execProofTheory.compute_eval_from_cv,
              cvTheory.cv_size_def])
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_analytic_instruction_is_sqrt_fst_eval,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `program`
  >- (simp
        [registered_case10173_analytic_instruction_is_sqrt_cv_def,
         Once compute_execTheory.from_cv_def]
      >> fs [Once compute_execTheory.from_cv_def])
  >> Cases_on `c = Num 1`
  >- (fs
        [registered_case10173_analytic_instruction_is_sqrt_cv_def,
         Once compute_execTheory.from_cv_def]
      >> simp
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv]
      >> Cases_on `intervals`
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> fs
       [registered_case10173_analytic_instruction_is_sqrt_cv_def,
        Once compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_analytic_program_sqrt_data_exact_eval:
  cv_size program + 2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_analytic_program_sqrt_data_exact»
        [from_cv intervals;from_cv program]) (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_analytic_program_sqrt_data_exact_cv
          intervals program)),refs)
Proof
  strip_tac
  >> irule
       registered_case10173_analytic_program_sqrt_data_exact_eval_from_results
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem registered_case10173_analytic_instruction_patch_sqrt_cv_pair:
  ?remaining patched_instruction.
    registered_case10173_analytic_instruction_patch_sqrt_cv
      intervals instruction = Pair remaining patched_instruction
Proof
  Cases_on `instruction`
  >- simp [registered_case10173_analytic_instruction_patch_sqrt_cv_def]
  >> Cases_on `c`
  >> Cases_on `intervals`
  >> simp [registered_case10173_analytic_instruction_patch_sqrt_cv_def]
  >> every_case_tac
  >> simp []
QED

Theorem registered_case10173_analytic_program_patch_sqrt_cv_pair:
  !program intervals.
    ?remaining patched_program.
      registered_case10173_analytic_program_patch_sqrt_cv
        intervals program = Pair remaining patched_program
Proof
  Induct_on `program`
  >- simp [registered_case10173_analytic_program_patch_sqrt_cv_def]
  >> gen_tac
  >> qspecl_then [`intervals`,`program`] strip_assume_tac
       (GEN_ALL
         registered_case10173_analytic_instruction_patch_sqrt_cv_pair)
  >> qpat_x_assum
       `!intervals. ?remaining patched_program.
          registered_case10173_analytic_program_patch_sqrt_cv
            intervals program' = Pair remaining patched_program`
       (qspec_then `remaining` strip_assume_tac)
  >> fs [registered_case10173_analytic_program_patch_sqrt_cv_def]
QED

Theorem registered_case10173_analytic_program_patch_sqrt_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_analytic_program_patch_sqrt»
        [from_cv intervals;from_cv program]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«intervals»,from_cv intervals);(«program»,from_cv program)]
        registered_case10173_analytic_program_patch_sqrt_body) refs
Proof
  strip_tac
  >> irule compute_eval_literal_app2
  >> simp [registered_case10173_analytic_program_patch_sqrt_lookup]
QED

Theorem registered_case10173_analytic_instruction_patch_sqrt_fst_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_analytic_instruction_patch_sqrt»
        [from_cv intervals;
         Uop Fst (Pair (from_cv instruction) (from_cv program))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_analytic_instruction_patch_sqrt_cv
          intervals instruction)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_instruction_patch_sqrt»
          [from_cv intervals;
           Uop Fst (Pair (from_cv instruction) (from_cv program))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_instruction_patch_sqrt»
          [from_cv intervals;from_cv instruction]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components,
              compute_execProofTheory.compute_eval_from_cv])
  >> pop_assum SUBST1_TAC
  >> irule registered_case10173_analytic_instruction_patch_sqrt_eval
  >> simp []
QED

Theorem registered_case10173_analytic_program_patch_sqrt_eval_from_results:
  !program intervals interval_expression program_expression clock refs.
    2 * cv_size program + 5 < clock /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      interval_expression (refs:hol_refs) =
        (M_success (from_cv intervals),refs) /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      program_expression refs = (M_success (from_cv program),refs) ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_program_patch_sqrt»
          [interval_expression;program_expression]) refs =
      (M_success
        (from_cv
          (registered_case10173_analytic_program_patch_sqrt_cv
            intervals program)),refs)
Proof
  Induct_on `program`
  >- (rpt strip_tac
      >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
            (App «candle_cv_analytic_program_patch_sqrt»
              [interval_expression;program_expression]) refs =
          compute_eval clock registered_case10173_historical_chunk16_ceqs
            (App «candle_cv_analytic_program_patch_sqrt»
              [from_cv intervals;from_cv (Num n)]) refs` by
           (irule
              compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
            >> fs [cvTheory.cv_size_def])
      >> pop_assum SUBST1_TAC
      >> simp
           [registered_case10173_analytic_program_patch_sqrt_unfold,
            registered_case10173_analytic_program_patch_sqrt_body_def,
            registered_case10173_analytic_program_patch_sqrt_cv_def,
            compute_evalTheory.subst_def,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv,
            compute_execTheory.from_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_program_patch_sqrt»
          [interval_expression;program_expression]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_program_patch_sqrt»
          [from_cv intervals;from_cv (Pair program program')]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> fs [cvTheory.cv_size_def])
  >> pop_assum SUBST1_TAC
  >> simp
       [registered_case10173_analytic_program_patch_sqrt_unfold,
        registered_case10173_analytic_program_patch_sqrt_body_def,
        registered_case10173_analytic_program_patch_sqrt_cv_def,
        compute_evalTheory.subst_def,
        compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> qspecl_then [`intervals`,`program`] strip_assume_tac
       (GEN_ALL
         registered_case10173_analytic_instruction_patch_sqrt_cv_pair)
  >> qspecl_then [`program'`,`remaining`] strip_assume_tac
       registered_case10173_analytic_program_patch_sqrt_cv_pair
  >> `0 < clock - 1` by fs [cvTheory.cv_size_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- fs []
  >> qexists_tac `from_cv (Pair remaining patched_instruction)`
  >> conj_tac
  >- fs [registered_case10173_analytic_instruction_patch_sqrt_fst_eval]
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> `0 < clock - 2` by fs [cvTheory.cv_size_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- fs []
  >> qexists_tac `from_cv (Pair remaining' patched_program)`
  >> conj_tac
  >- (qpat_x_assum
        `!intervals interval_expression program_expression clock refs.
           2 * cv_size program' + 5 < clock /\ _ ==> _`
        (qspecl_then
          [`remaining`,
           `Uop Fst
              (Pair (from_cv remaining) (from_cv patched_instruction))`,
           `Uop Snd (Pair (from_cv program) (from_cv program'))`,
           `clock - 2`,`refs`] mp_tac)
      >> fs
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components,
            compute_execProofTheory.compute_eval_from_cv,
            cvTheory.cv_size_def]
      >> strip_tac
      >> first_x_assum irule
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_analytic_program_patch_sqrt_eval:
  2 * cv_size program + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_analytic_program_patch_sqrt»
        [from_cv intervals;from_cv program]) (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_analytic_program_patch_sqrt_cv
          intervals program)),refs)
Proof
  strip_tac
  >> irule registered_case10173_analytic_program_patch_sqrt_eval_from_results
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

val _ = export_theory ();
