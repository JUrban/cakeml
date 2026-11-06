(*****************************************************************************
 * Successful compute evaluations are preserved when lower-priority         *
 * equations are appended.                                                   *
 *                                                                            *
 * A successful evaluation can only call names already present in the        *
 * original equation environment.  ALOOKUP therefore continues to select     *
 * exactly the same equations after an arbitrary suffix is appended.          *
 *****************************************************************************)
Theory compute_evalCeqsAppendSuccess
Ancestors
  compute_eval
Libs
  bossLib preamble

Theorem compute_eval_append_success:
  (!clock ceqs expression result state state' extra_ceqs.
     compute_eval clock ceqs expression state =
       (M_success result,state') ==>
     compute_eval clock (ceqs ++ extra_ceqs) expression state =
       (M_success result,state')) /\
  (!clock ceqs expressions results state state' extra_ceqs.
     compute_eval_list clock ceqs expressions state =
       (M_success results,state') ==>
     compute_eval_list clock (ceqs ++ extra_ceqs) expressions state =
       (M_success results,state'))
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
           `!result state state' extra_ceqs.
              compute_eval clock ceqs expression state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`extra_ceqs`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> qpat_x_assum
           `!result state state' extra_ceqs.
              compute_eval clock ceqs expression' state = _ ==> _`
           (mp_tac o Q.SPECL [`a'`,`r`,`final_refs`,`extra_ceqs`])
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
           `!result state state' extra_ceqs. _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`extra_ceqs`])
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
           `!result state state' extra_ceqs.
              compute_eval clock ceqs expression state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`extra_ceqs`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> qpat_x_assum
           `!result state state' extra_ceqs.
              compute_eval clock ceqs expression' state = _ ==> _`
           (mp_tac o Q.SPECL [`a'`,`r`,`r'`,`extra_ceqs`])
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
           `!results state state' extra_ceqs.
              compute_eval_list clock ceqs expressions state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`extra_ceqs`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> qpat_x_assum
           `!args cs' exp result state state' extra_ceqs. _`
           (mp_tac o
              Q.SPECL [`x0`,`a`,`x1`,`result`,`r`,`final_refs`,
                       `extra_ceqs`])
      >> asm_rewrite_tac [ALOOKUP_APPEND]
      >> simp [ALOOKUP_APPEND])
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
           `!result state state' extra_ceqs.
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
           `!result state state' extra_ceqs.
              compute_eval clock ceqs expression state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`extra_ceqs`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> qpat_x_assum
           `!x result state state' extra_ceqs. _`
           (mp_tac o Q.SPECL [`a`,`result`,`r`,`final_refs`,
                              `extra_ceqs`])
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
           `!result state state' extra_ceqs.
              compute_eval clock ceqs expression state = _ ==> _`
           (mp_tac o Q.SPECL [`a`,`refs`,`r`,`extra_ceqs`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> qpat_x_assum
           `!results state state' extra_ceqs.
              compute_eval_list clock ceqs expressions state = _ ==> _`
           (mp_tac o Q.SPECL [`a'`,`r`,`final_refs`,`extra_ceqs`])
      >> asm_rewrite_tac []
      >> strip_tac
      >> simp [Once compute_evalTheory.compute_eval_def,
               ml_monadBaseTheory.st_ex_bind_def,
               ml_monadBaseTheory.st_ex_return_def])
QED

val _ = export_theory ();
