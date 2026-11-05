(*****************************************************************************
 * Successful compute evaluation is stable under additional clock fuel.
 *
 * The evaluator reports timeout only when an App or Let is entered at zero
 * clock.  Once a run has succeeded, adding fuel cannot change its value or
 * state.  Keeping the evaluator and evaluator-list statements together makes
 * the result follow the mutual recursion exactly.
 *****************************************************************************)
Theory compute_evalSuccessMonotonicity
Ancestors
  compute_eval
Libs
  bossLib preamble intLib

Theorem compute_eval_success_add_clock:
  (!clock ceqs expression result state final_state extra.
    compute_eval clock ceqs expression state =
      (M_success result,final_state) ==>
    compute_eval (clock + extra) ceqs expression state =
      (M_success result,final_state)) /\
  (!clock ceqs expressions results state final_state extra.
    compute_eval_list clock ceqs expressions state =
      (M_success results,final_state) ==>
    compute_eval_list (clock + extra) ceqs expressions state =
      (M_success results,final_state))
Proof
  ho_match_mp_tac compute_evalTheory.compute_eval_ind
  >> rpt conj_tac
  >- simp [compute_evalTheory.compute_eval_def]
  >- simp [compute_evalTheory.compute_eval_def,
           ml_monadBaseTheory.st_ex_return_def]
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval clock ceqs (Pair expression expression') refs =
              (M_success result,final_refs)`
      >> rw [Once compute_evalTheory.compute_eval_def]
      >> Cases_on `compute_eval clock ceqs expression refs`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def]
      >> Cases_on `compute_eval clock ceqs expression' r`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def]
      >> qpat_x_assum
           `!result state final_state extra.
              compute_eval clock ceqs expression state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`extra`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> qpat_x_assum
           `!result state final_state extra.
              compute_eval clock ceqs expression' state = _ ==> _`
           (mp_tac o Q.SPECL [`a'`,`r`,`final_refs`,`extra`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> simp [Once compute_evalTheory.compute_eval_def,
               ml_monadBaseTheory.st_ex_bind_def,
               ml_monadBaseTheory.st_ex_return_def])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval clock ceqs (Uop uop expression) refs =
              (M_success result,final_refs)`
      >> rw [Once compute_evalTheory.compute_eval_def]
      >> Cases_on `compute_eval clock ceqs expression refs`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> qpat_x_assum
           `!result state final_state extra. _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`extra`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> simp [Once compute_evalTheory.compute_eval_def,
               ml_monadBaseTheory.st_ex_bind_def])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval clock ceqs (Binop bop expression expression') refs =
              (M_success result,final_refs)`
      >> rw [Once compute_evalTheory.compute_eval_def]
      >> Cases_on `compute_eval clock ceqs expression refs`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> Cases_on `compute_eval clock ceqs expression' r`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> qpat_x_assum
           `!result state final_state extra.
              compute_eval clock ceqs expression state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`extra`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> qpat_x_assum
           `!result state final_state extra.
              compute_eval clock ceqs expression' state = _ ==> _`
           (mp_tac o Q.SPECL [`a'`,`r`,`r'`,`extra`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> simp [Once compute_evalTheory.compute_eval_def,
               ml_monadBaseTheory.st_ex_bind_def])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval clock ceqs (App f expressions) refs =
              (M_success result,final_refs)`
      >> Cases_on `clock = 0`
      >> gvs [compute_evalTheory.compute_eval_def,
              holKernelTheory.raise_Failure_def]
      >> Cases_on `ALOOKUP ceqs f`
      >> gvs [compute_evalTheory.option_def,
              ml_monadBaseTheory.st_ex_bind_def,
              holKernelTheory.raise_Failure_def]
      >> PairCases_on `(x:mlstring list # compute_exp)`
      >> gvs [compute_evalTheory.option_def,
              compute_evalTheory.check_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def,
              holKernelTheory.raise_Failure_def]
      >> Cases_on `LENGTH x0 = LENGTH expressions`
      >> gvs [ml_monadBaseTheory.st_ex_ignore_bind_def,
              ml_monadBaseTheory.st_ex_bind_def,
              holKernelTheory.raise_Failure_def]
      >> Cases_on `compute_eval_list clock ceqs expressions refs`
      >> Cases_on `q`
      >> gvs []
      >> strip_tac
      >> qpat_x_assum
           `!results state final_state extra.
              compute_eval_list clock ceqs expressions state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`extra`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> `clock - 1 + extra = clock + extra - 1` by intLib.ARITH_TAC
      >> qpat_x_assum
           `!args cs' exp result state final_state extra. _`
           (mp_tac o
              Q.SPECL [`x0`,`a`,`x1`,`result`,`r`,`final_refs`,`extra`])
      >> asm_rewrite_tac []
      >> simp [])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval clock ceqs
              (If expression expression' expression'') refs =
              (M_success result,final_refs)`
      >> rw [Once compute_evalTheory.compute_eval_def]
      >> Cases_on `compute_eval clock ceqs expression refs`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> Cases_on `a`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def,
              holKernelTheory.raise_Failure_def]
      >> TRY (Cases_on `n` >> gvs [])
      >> qpat_x_assum
           `!result state final_state extra.
              compute_eval clock ceqs expression state = _ ==> _`
           drule
      >> simp [Once compute_evalTheory.compute_eval_def,
               ml_monadBaseTheory.st_ex_bind_def]
      >> metis_tac [])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval clock ceqs (Let s expression q) refs =
              (M_success result,final_refs)`
      >> Cases_on `clock = 0`
      >> gvs [compute_evalTheory.compute_eval_def,
              holKernelTheory.raise_Failure_def]
      >> Cases_on `compute_eval clock ceqs expression refs`
      >> Cases_on `q'`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> strip_tac
      >> qpat_x_assum
           `!result state final_state extra.
              compute_eval clock ceqs expression state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`extra`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> `clock - 1 + extra = clock + extra - 1` by intLib.ARITH_TAC
      >> qpat_x_assum
           `!x result state final_state extra. _`
           (mp_tac o Q.SPECL [`a`,`result`,`r`,`final_refs`,`extra`])
      >> asm_rewrite_tac []
      >> simp [])
  >- simp [compute_evalTheory.compute_eval_def,
           ml_monadBaseTheory.st_ex_return_def]
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval_list clock ceqs (expression::expressions) refs =
              (M_success results,final_refs)`
      >> rw [Once compute_evalTheory.compute_eval_def]
      >> Cases_on `compute_eval clock ceqs expression refs`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> Cases_on `compute_eval_list clock ceqs expressions r`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def]
      >> qpat_x_assum
           `!result state final_state extra.
              compute_eval clock ceqs expression state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`extra`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> qpat_x_assum
           `!results state final_state extra.
              compute_eval_list clock ceqs expressions state = _ ==> _`
           (mp_tac o Q.SPECL [`a'`,`r`,`final_refs`,`extra`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> simp [Once compute_evalTheory.compute_eval_def,
               ml_monadBaseTheory.st_ex_bind_def,
               ml_monadBaseTheory.st_ex_return_def])
QED

Theorem compute_eval_success_state_independent:
  (!clock ceqs expression result state final_state other_state.
    compute_eval clock ceqs expression state =
      (M_success result,final_state) ==>
    final_state = state /\
    compute_eval clock ceqs expression other_state =
      (M_success result,other_state)) /\
  (!clock ceqs expressions results state final_state other_state.
    compute_eval_list clock ceqs expressions state =
      (M_success results,final_state) ==>
    final_state = state /\
    compute_eval_list clock ceqs expressions other_state =
      (M_success results,other_state))
Proof
  ho_match_mp_tac compute_evalTheory.compute_eval_ind
  >> rpt conj_tac
  >- simp [compute_evalTheory.compute_eval_def,
           holKernelTheory.raise_Failure_def]
  >- simp [compute_evalTheory.compute_eval_def,
           ml_monadBaseTheory.st_ex_return_def]
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval clock ceqs (Pair expression expression') refs =
              (M_success result,final_refs)`
      >> rw [Once compute_evalTheory.compute_eval_def]
      >> Cases_on `compute_eval clock ceqs expression refs`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def]
      >> Cases_on `compute_eval clock ceqs expression' r`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def]
      >> qpat_x_assum
           `!result state final_state other_state.
              compute_eval clock ceqs expression state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`other_state`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> qpat_x_assum
           `!result state final_state other_state.
              compute_eval clock ceqs expression' state = _ ==> _`
           (mp_tac o Q.SPECL [`a'`,`r`,`final_refs`,`other_state`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> simp [Once compute_evalTheory.compute_eval_def,
               ml_monadBaseTheory.st_ex_bind_def,
               ml_monadBaseTheory.st_ex_return_def])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval clock ceqs (Uop uop expression) refs =
              (M_success result,final_refs)`
      >> rw [Once compute_evalTheory.compute_eval_def]
      >> Cases_on `compute_eval clock ceqs expression refs`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> qpat_x_assum
           `!result state final_state other_state.
              compute_eval clock ceqs expression state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`other_state`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> simp [Once compute_evalTheory.compute_eval_def,
               ml_monadBaseTheory.st_ex_bind_def]
      >> Cases_on `uop`
      >> Cases_on `a`
      >> gvs [compute_evalTheory.do_uop_def,
              compute_evalTheory.do_fst_def,
              compute_evalTheory.do_snd_def,
              compute_evalTheory.do_ispair_def,
              ml_monadBaseTheory.st_ex_return_def])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval clock ceqs (Binop bop expression expression') refs =
              (M_success result,final_refs)`
      >> rw [Once compute_evalTheory.compute_eval_def]
      >> Cases_on `compute_eval clock ceqs expression refs`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> Cases_on `compute_eval clock ceqs expression' r`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> qpat_x_assum
           `!result state final_state other_state.
              compute_eval clock ceqs expression state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`other_state`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> qpat_x_assum
           `!result state final_state other_state.
              compute_eval clock ceqs expression' state = _ ==> _`
           (mp_tac o Q.SPECL [`a'`,`r`,`r'`,`other_state`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> simp [Once compute_evalTheory.compute_eval_def,
               ml_monadBaseTheory.st_ex_bind_def]
      >> Cases_on `bop`
      >> Cases_on `a`
      >> Cases_on `a'`
      >> gvs [compute_evalTheory.do_binop_def,
              compute_evalTheory.do_arith_def,
              compute_evalTheory.do_reln_def,
              compute_evalTheory.do_eq_def,
              ml_monadBaseTheory.st_ex_return_def])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval clock ceqs (App f expressions) refs =
              (M_success result,final_refs)`
      >> Cases_on `clock = 0`
      >> gvs [compute_evalTheory.compute_eval_def,
              holKernelTheory.raise_Failure_def]
      >> Cases_on `ALOOKUP ceqs f`
      >> gvs [compute_evalTheory.option_def,
              ml_monadBaseTheory.st_ex_bind_def,
              holKernelTheory.raise_Failure_def]
      >> PairCases_on `(x:mlstring list # compute_exp)`
      >> gvs [compute_evalTheory.option_def,
              compute_evalTheory.check_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def,
              holKernelTheory.raise_Failure_def]
      >> Cases_on `LENGTH x0 = LENGTH expressions`
      >> gvs [ml_monadBaseTheory.st_ex_ignore_bind_def,
              ml_monadBaseTheory.st_ex_bind_def,
              holKernelTheory.raise_Failure_def]
      >> Cases_on `compute_eval_list clock ceqs expressions refs`
      >> Cases_on `q`
      >> gvs []
      >> strip_tac
      >> qpat_x_assum
           `!results state final_state other_state.
              compute_eval_list clock ceqs expressions state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`other_state`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> qpat_x_assum
           `!args cs' exp result state final_state other_state.
              compute_eval (clock - 1) ceqs
                (subst (ZIP (args,cs')) exp) state = _ ==> _`
           (mp_tac o
              Q.SPECL
                [`x0`,`a`,`x1`,`result`,`r`,`final_refs`,`other_state`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> simp [compute_evalTheory.compute_eval_def,
               compute_evalTheory.option_def,
               compute_evalTheory.check_def,
               ml_monadBaseTheory.st_ex_ignore_bind_def,
               ml_monadBaseTheory.st_ex_bind_def,
               ml_monadBaseTheory.st_ex_return_def])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval clock ceqs
              (If expression expression' expression'') refs =
              (M_success result,final_refs)`
      >> rw [Once compute_evalTheory.compute_eval_def]
      >> Cases_on `compute_eval clock ceqs expression refs`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> Cases_on `a`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def,
              holKernelTheory.raise_Failure_def]
      >- (Cases_on `n` >> gvs [] >> metis_tac [])
      >- (qpat_x_assum
             `!result state final_state other_state.
                compute_eval clock ceqs expression state = _ ==> _`
             (mp_tac o
                Q.SPECL [`Pair c c0`,`refs`,`r`,`other_state`])
          >> asm_rewrite_tac []
          >> strip_tac
          >> qpat_x_assum
               `!result state final_state other_state.
                  compute_eval clock ceqs expression'' state = _ ==> _`
               (mp_tac o
                  Q.SPECL [`result`,`r`,`final_refs`,`other_state`])
          >> asm_rewrite_tac []
          >> strip_tac
          >> simp [Once compute_evalTheory.compute_eval_def,
                   ml_monadBaseTheory.st_ex_bind_def])
      >- (Cases_on `n`
          >> gvs []
          >- (qpat_x_assum
                 `!result state final_state other_state.
                    compute_eval clock ceqs expression state = _ ==> _`
                 (mp_tac o Q.SPECL [`Num 0`,`refs`,`r`,`other_state`])
              >> asm_rewrite_tac []
              >> strip_tac
              >> qpat_x_assum
                   `!result state final_state other_state.
                      compute_eval clock ceqs expression'' state = _ ==> _`
                   (mp_tac o
                      Q.SPECL [`result`,`r`,`final_refs`,`other_state`])
              >> asm_rewrite_tac []
              >> strip_tac
              >> simp [Once compute_evalTheory.compute_eval_def,
                       ml_monadBaseTheory.st_ex_bind_def])
          >- (qpat_x_assum
                 `!result state final_state other_state.
                    compute_eval clock ceqs expression state = _ ==> _`
                 (mp_tac o
                    Q.SPECL [`Num (SUC n')`,`refs`,`r`,`other_state`])
              >> asm_rewrite_tac []
              >> strip_tac
              >> qpat_x_assum
                   `!result state final_state other_state.
                      compute_eval clock ceqs expression' state = _ ==> _`
                   (mp_tac o
                      Q.SPECL [`result`,`r`,`final_refs`,`other_state`])
              >> asm_rewrite_tac []
              >> strip_tac
              >> simp [Once compute_evalTheory.compute_eval_def,
                       ml_monadBaseTheory.st_ex_bind_def])))
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval clock ceqs (Let s expression q) refs =
              (M_success result,final_refs)`
      >> Cases_on `clock = 0`
      >> gvs [compute_evalTheory.compute_eval_def,
              holKernelTheory.raise_Failure_def]
      >> Cases_on `compute_eval clock ceqs expression refs`
      >> Cases_on `q'`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> strip_tac
      >> qpat_x_assum
           `!result state final_state other_state.
              compute_eval clock ceqs expression state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`other_state`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> qpat_x_assum
           `!x result state final_state other_state.
              compute_eval (clock - 1) ceqs
                (subst [(s,x)] q) state = _ ==> _`
           (mp_tac o
              Q.SPECL [`a`,`result`,`r`,`final_refs`,`other_state`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> simp [compute_evalTheory.compute_eval_def,
               ml_monadBaseTheory.st_ex_bind_def])
  >- simp [compute_evalTheory.compute_eval_def,
           ml_monadBaseTheory.st_ex_return_def]
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> rename1
           `compute_eval_list clock ceqs (expression::expressions) refs =
              (M_success results,final_refs)`
      >> rw [Once compute_evalTheory.compute_eval_def]
      >> Cases_on `compute_eval clock ceqs expression refs`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> Cases_on `compute_eval_list clock ceqs expressions r`
      >> Cases_on `q`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def]
      >> qpat_x_assum
           `!result state final_state other_state.
              compute_eval clock ceqs expression state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`other_state`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> qpat_x_assum
           `!results state final_state other_state.
              compute_eval_list clock ceqs expressions state = _ ==> _`
           (mp_tac o Q.SPECL [`a'`,`r`,`final_refs`,`other_state`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> simp [Once compute_evalTheory.compute_eval_def,
               ml_monadBaseTheory.st_ex_bind_def,
               ml_monadBaseTheory.st_ex_return_def])
QED

Theorem compute_eval_success_change_state:
  !clock ceqs expression result (refs:hol_refs) other_refs.
    compute_eval clock ceqs expression refs =
        (M_success result,refs) ==>
    compute_eval clock ceqs expression other_refs =
        (M_success result,other_refs)
Proof
  metis_tac [CONJUNCT1 compute_eval_success_state_independent]
QED

Theorem compute_eval_success_mono:
  compute_eval lower ceqs expression refs =
      (M_success result,final_refs) /\
  lower <= upper ==>
  compute_eval upper ceqs expression refs =
      (M_success result,final_refs)
Proof
  strip_tac
  >> `upper = lower + (upper - lower)` by intLib.ARITH_TAC
  >> qpat_x_assum `upper = _` (fn th => once_rewrite_tac [th])
  >> irule (CONJUNCT1 compute_eval_success_add_clock)
  >> first_assum ACCEPT_TAC
QED

val _ = export_theory ();
