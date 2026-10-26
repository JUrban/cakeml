(*****************************************************************************
 * Evaluator congruence on a statically closed set of reachable functions.
 * This permits an authenticated equation environment to change outside the
 * call graph of an expression without replaying the expression's proof.
 *****************************************************************************)
Theory compute_evalRestrictedCongruence
Ancestors
  compute_evalProof
Libs
  bossLib preamble

Definition compute_exp_uses_only_def:
  compute_exp_uses_only allowed (Var name) = T /\
  compute_exp_uses_only allowed (Num value) = T /\
  compute_exp_uses_only allowed (Pair left right) =
    (compute_exp_uses_only allowed left /\
     compute_exp_uses_only allowed right) /\
  compute_exp_uses_only allowed (Uop operation argument) =
    compute_exp_uses_only allowed argument /\
  compute_exp_uses_only allowed (Binop operation left right) =
    (compute_exp_uses_only allowed left /\
     compute_exp_uses_only allowed right) /\
  compute_exp_uses_only allowed (App function arguments) =
    (MEM function allowed /\
     EVERY (compute_exp_uses_only allowed) arguments) /\
  compute_exp_uses_only allowed (If condition yes_branch no_branch) =
    (compute_exp_uses_only allowed condition /\
     compute_exp_uses_only allowed yes_branch /\
     compute_exp_uses_only allowed no_branch) /\
  compute_exp_uses_only allowed (Let name argument body) =
    (compute_exp_uses_only allowed argument /\
     compute_exp_uses_only allowed body)
Termination
  WF_REL_TAC `measure (compute_exp_size o SND)`
End

Definition compute_ceqs_closed_on_def:
  compute_ceqs_closed_on allowed ceqs <=>
    !function arguments body.
      MEM function allowed /\
      ALOOKUP ceqs function = SOME (arguments,body) ==>
      compute_exp_uses_only allowed body
End

Definition compute_ceqs_agree_on_def:
  compute_ceqs_agree_on allowed left_ceqs right_ceqs <=>
    !function.
      MEM function allowed ==>
      ALOOKUP left_ceqs function = ALOOKUP right_ceqs function
End

Theorem compute_exp_uses_only_subst:
  !env expression.
    compute_exp_uses_only allowed expression /\
    EVERY (compute_exp_uses_only allowed) (MAP SND env) ==>
    compute_exp_uses_only allowed (subst env expression)
Proof
  ho_match_mp_tac compute_evalTheory.subst_ind
  >> rw []
  >> gs [compute_exp_uses_only_def, compute_evalTheory.subst_def]
  >- (gs [EVERY_MEM, MEM_MAP, EXISTS_PROD, PULL_EXISTS]
      >> CASE_TAC
      >> gs [compute_exp_uses_only_def]
      >> drule_then assume_tac ALOOKUP_MEM
      >> gs [SF SFY_ss])
  >> gs [EVERY_MAP, EVERY_MEM, EXISTS_PROD, PULL_EXISTS, MEM_FILTER]
QED

Theorem cexp_value_compute_exp_uses_only:
  !expression.
    cexp_value expression ==>
    compute_exp_uses_only allowed expression
Proof
  Induct
  >> simp [compute_exp_uses_only_def]
QED

Theorem compute_ceqs_closed_on_from_every:
  EVERY
    (\(function,(arguments,body)).
       MEM function allowed ==> compute_exp_uses_only allowed body)
    ceqs ==>
  compute_ceqs_closed_on allowed ceqs
Proof
  rw [compute_ceqs_closed_on_def, EVERY_MEM]
  >> drule ALOOKUP_MEM
  >> strip_tac
  >> res_tac
  >> fs []
QED

Theorem compute_ceqs_agree_on_from_every:
  EVERY
    (\function.
       ALOOKUP left_ceqs function = ALOOKUP right_ceqs function)
    allowed ==>
  compute_ceqs_agree_on allowed left_ceqs right_ceqs
Proof
  simp [compute_ceqs_agree_on_def, EVERY_MEM]
QED

Theorem compute_eval_list_success_length:
  !expressions values clock ceqs state state'.
    compute_eval_list clock ceqs expressions state =
      (M_success values,state') ==>
    LENGTH values = LENGTH expressions
Proof
  Induct
  >> fs
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_return_def,
        ml_monadBaseTheory.st_ex_bind_def]
  >> rw []
  >> gvs [AllCaseEqs()]
  >> res_tac
  >> fs []
QED

Theorem compute_eval_restricted_cong:
  (!clock left_ceqs expression right_ceqs allowed state.
    compute_exp_uses_only allowed expression /\
    compute_ceqs_closed_on allowed left_ceqs /\
    compute_ceqs_closed_on allowed right_ceqs /\
    compute_ceqs_agree_on allowed left_ceqs right_ceqs ==>
    compute_eval clock left_ceqs expression state =
      compute_eval clock right_ceqs expression state) /\
  (!clock left_ceqs expressions right_ceqs allowed state.
    EVERY (compute_exp_uses_only allowed) expressions /\
    compute_ceqs_closed_on allowed left_ceqs /\
    compute_ceqs_closed_on allowed right_ceqs /\
    compute_ceqs_agree_on allowed left_ceqs right_ceqs ==>
    compute_eval_list clock left_ceqs expressions state =
      compute_eval_list clock right_ceqs expressions state)
Proof
  ho_match_mp_tac compute_evalTheory.compute_eval_ind
  >> rpt conj_tac
  >- (rpt gen_tac
      >> strip_tac
      >> simp [compute_evalTheory.compute_eval_def])
  >- (rpt gen_tac
      >> strip_tac
      >> simp [compute_evalTheory.compute_eval_def])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> strip_tac
      >> fs [compute_exp_uses_only_def]
      >> `!s. compute_eval clock left_ceqs expression s =
                compute_eval clock right_ceqs expression s` by metis_tac []
      >> `!s. compute_eval clock left_ceqs expression' s =
                compute_eval clock right_ceqs expression' s` by metis_tac []
      >> simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_bind_def])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> strip_tac
      >> fs [compute_exp_uses_only_def]
      >> `!s. compute_eval clock left_ceqs expression s =
                compute_eval clock right_ceqs expression s` by metis_tac []
      >> simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_bind_def])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> strip_tac
      >> fs [compute_exp_uses_only_def]
      >> `!s. compute_eval clock left_ceqs expression s =
                compute_eval clock right_ceqs expression s` by metis_tac []
      >> `!s. compute_eval clock left_ceqs expression' s =
                compute_eval clock right_ceqs expression' s` by metis_tac []
      >> simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_bind_def])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> strip_tac
      >> fs [compute_exp_uses_only_def]
      >> Cases_on `clock = 0`
      >> simp [compute_evalTheory.compute_eval_def]
      >> `ALOOKUP left_ceqs f = ALOOKUP right_ceqs f` by
           fs [compute_ceqs_agree_on_def]
      >> `!s. compute_eval_list clock left_ceqs expressions s =
                compute_eval_list clock right_ceqs expressions s` by
           metis_tac []
      >> simp
           [Once compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_ignore_bind_def,
            ml_monadBaseTheory.st_ex_return_def,
            compute_evalTheory.check_def,
            compute_evalTheory.option_def,
            holKernelTheory.raise_Failure_def]
      >> Cases_on `ALOOKUP right_ceqs f`
      >> simp []
      >> Cases_on `x`
      >> simp []
      >> Cases_on `LENGTH q = LENGTH expressions`
      >> simp []
      >> TOP_CASE_TAC
      >> gs []
      >> Cases_on `q'`
      >> simp []
      >> `compute_exp_uses_only allowed r` by
           metis_tac [compute_ceqs_closed_on_def]
      >> imp_res_tac
           (CONJUNCT2 compute_evalProofTheory.compute_eval_value)
      >> imp_res_tac compute_eval_list_success_length
      >> `EVERY (compute_exp_uses_only allowed) a` by
           (fs [EVERY_MEM]
            >> metis_tac [cexp_value_compute_exp_uses_only])
      >> `MAP SND (ZIP (q,a)) = a` by fs [MAP_ZIP]
      >> `compute_exp_uses_only allowed (subst (ZIP (q,a)) r)` by
           metis_tac [compute_exp_uses_only_subst]
      >> metis_tac [])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> strip_tac
      >> fs [compute_exp_uses_only_def]
      >> `!s. compute_eval clock left_ceqs expression s =
                compute_eval clock right_ceqs expression s` by metis_tac []
      >> `!s. compute_eval clock left_ceqs expression' s =
                compute_eval clock right_ceqs expression' s` by metis_tac []
      >> `!s. compute_eval clock left_ceqs expression'' s =
                compute_eval clock right_ceqs expression'' s` by metis_tac []
      >> simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_bind_def]
      >> TOP_CASE_TAC
      >> gs []
      >> Cases_on `q`
      >> simp []
      >> Cases_on `a`
      >> simp []
      >> Cases_on `n`
      >> simp [])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> strip_tac
      >> fs [compute_exp_uses_only_def]
      >> Cases_on `clock = 0`
      >> simp [compute_evalTheory.compute_eval_def]
      >> `!s. compute_eval clock left_ceqs expression s =
                compute_eval clock right_ceqs expression s` by metis_tac []
      >> simp
           [Once compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_bind_def]
      >> TOP_CASE_TAC
      >> gs []
      >> Cases_on `q'`
      >> simp []
      >> imp_res_tac
           (CONJUNCT1 compute_evalProofTheory.compute_eval_value)
      >> `compute_exp_uses_only allowed a` by
           metis_tac [cexp_value_compute_exp_uses_only]
      >> `compute_exp_uses_only allowed (subst [(s,a)] q)` by
           (irule compute_exp_uses_only_subst
            >> simp [])
      >> metis_tac [])
  >- (rpt gen_tac
      >> strip_tac
      >> simp [compute_evalTheory.compute_eval_def])
  >- (rpt gen_tac
      >> strip_tac
      >> rpt gen_tac
      >> strip_tac
      >> fs []
      >> `!s. compute_eval clock left_ceqs expression s =
                compute_eval clock right_ceqs expression s` by metis_tac []
      >> `!s. compute_eval_list clock left_ceqs expressions s =
                compute_eval_list clock right_ceqs expressions s` by
           metis_tac []
      >> simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_bind_def])
QED

val _ = export_theory ();
