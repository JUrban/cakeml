(*****************************************************************************
 * First-order, proof-producing evaluation route for registered compute calls.
 *
 * The existing compute_eval returns a state-exception monad and is therefore
 * higher-order from cv_compute's perspective.  This evaluator preserves its
 * first-order expression/result semantics with option denoting failure.  It
 * is intended for reusable offline refinement proofs, not as a new kernel
 * authority.
 *****************************************************************************)
Theory compute_evalPure
Ancestors
  compute_eval cv_std
Libs
  preamble cv_transLib

Definition compute_pure_to_num_def:
  compute_pure_to_num (Num n : compute_exp) = n /\
  compute_pure_to_num _ = 0
End

Definition compute_pure_uop_def:
  compute_pure_uop Fst (Pair p q : compute_exp) = SOME p /\
  compute_pure_uop Fst _ = SOME (Num 0) /\
  compute_pure_uop Snd (Pair p q : compute_exp) = SOME q /\
  compute_pure_uop Snd _ = SOME (Num 0) /\
  compute_pure_uop Ispair (Pair p q : compute_exp) = SOME (Num 1) /\
  compute_pure_uop Ispair _ = SOME (Num 0)
End

Definition compute_pure_binop_def:
  compute_pure_binop Add p q =
    SOME (Num (compute_pure_to_num p + compute_pure_to_num q)) /\
  compute_pure_binop Sub p q =
    SOME (Num (compute_pure_to_num p - compute_pure_to_num q)) /\
  compute_pure_binop Mul p q =
    SOME (Num (compute_pure_to_num p * compute_pure_to_num q)) /\
  compute_pure_binop Div p q =
    SOME (Num (let denominator = compute_pure_to_num q in
               if denominator = 0 then 0
               else compute_pure_to_num p DIV denominator)) /\
  compute_pure_binop Mod p q =
    SOME (Num (let denominator = compute_pure_to_num q in
               if denominator = 0 then compute_pure_to_num p
               else compute_pure_to_num p MOD denominator)) /\
  compute_pure_binop Eq p q = SOME (Num (if p = q then 1 else 0)) /\
  compute_pure_binop Less (Num p) (Num q) =
    SOME (Num (if p < q then 1 else 0)) /\
  compute_pure_binop Less _ _ = SOME (Num 0)
End

Definition compute_pure_remove_binding_def:
  compute_pure_remove_binding name [] = [] /\
  compute_pure_remove_binding name ((candidate,value)::remaining) =
    if candidate = name then compute_pure_remove_binding name remaining
    else (candidate,value)::compute_pure_remove_binding name remaining
End

Definition compute_pure_subst_def:
  compute_pure_subst env (Var name) =
    (case ALOOKUP env name of
     | NONE => Var name
     | SOME value => value) /\
  compute_pure_subst env (Num n) = Num n /\
  compute_pure_subst env (Pair p q) =
    Pair (compute_pure_subst env p) (compute_pure_subst env q) /\
  compute_pure_subst env (Uop uop p) =
    Uop uop (compute_pure_subst env p) /\
  compute_pure_subst env (Binop binop p q) =
    Binop binop (compute_pure_subst env p) (compute_pure_subst env q) /\
  compute_pure_subst env (App name arguments) =
    App name (compute_pure_subst_list env arguments) /\
  compute_pure_subst env (If p q r) =
    If (compute_pure_subst env p) (compute_pure_subst env q)
      (compute_pure_subst env r) /\
  compute_pure_subst env (Let name argument body) =
    Let name (compute_pure_subst env argument)
      (compute_pure_subst (compute_pure_remove_binding name env) body) /\
  compute_pure_subst_list env [] = [] /\
  compute_pure_subst_list env (argument::arguments) =
    compute_pure_subst env argument ::
      compute_pure_subst_list env arguments
Termination
  WF_REL_TAC ‘measure $ λx.
    case x of
    | INL (_,expression) => compute_exp_size expression
    | INR (_,expressions) => list_size compute_exp_size expressions’
  \\ rw [] \\ fs [list_size_def]
End

Theorem compute_pure_remove_binding_eq:
  !name env.
    compute_pure_remove_binding name env =
      FILTER (\(candidate,value). candidate <> name) env
Proof
  gen_tac >> Induct
  >- rw [compute_pure_remove_binding_def]
  >> gen_tac >> PairCases_on `h`
  >> rw [compute_pure_remove_binding_def]
QED

Theorem compute_pure_subst_eq:
  (!expression env.
     compute_pure_subst env expression = subst env expression) /\
  (!expressions env.
     compute_pure_subst_list env expressions = MAP (subst env) expressions)
Proof
  ho_match_mp_tac compute_syntaxTheory.compute_exp_induction
  >> rw [compute_pure_subst_def, subst_def,
         compute_pure_remove_binding_eq]
  >> metis_tac [ETA_AX]
QED

Theorem compute_pure_uop_refines:
  !uop input result state.
    compute_pure_uop uop input = SOME result ==>
    do_uop uop input state = (M_success result,state)
Proof
  Cases >> Cases_on `input`
  >> rw [compute_pure_uop_def, do_uop_def, do_fst_def, do_snd_def,
         do_ispair_def, ml_monadBaseTheory.st_ex_return_def]
QED

Theorem compute_pure_binop_refines:
  !binop left right result state.
    compute_pure_binop binop left right = SOME result ==>
    do_binop binop left right state = (M_success result,state)
Proof
  Cases >> Cases_on `left` >> Cases_on `right`
  >> rw [compute_pure_binop_def, compute_pure_to_num_def,
         do_binop_def, do_arith_def, do_reln_def, do_eq_def,
         ml_monadBaseTheory.st_ex_return_def,
         compute_syntaxTheory.SAFEDIV_def,
         compute_syntaxTheory.SAFEMOD_def]
QED

Definition compute_eval_pure_def:
  compute_eval_pure 0 ceqs expression = NONE /\
  compute_eval_pure (SUC ck) ceqs (Var s) = NONE /\
  compute_eval_pure (SUC ck) ceqs (Num n) = SOME (Num n) /\
  compute_eval_pure (SUC ck) ceqs (Pair p q) =
    (case compute_eval_pure ck ceqs p of
     | NONE => NONE
     | SOME x =>
       case compute_eval_pure ck ceqs q of
       | NONE => NONE
       | SOME y => SOME (Pair x y)) /\
  compute_eval_pure (SUC ck) ceqs (Uop uop p) =
    (case compute_eval_pure ck ceqs p of
     | NONE => NONE
     | SOME x => compute_pure_uop uop x) /\
  compute_eval_pure (SUC ck) ceqs (Binop bop p q) =
    (case compute_eval_pure ck ceqs p of
     | NONE => NONE
     | SOME x =>
       case compute_eval_pure ck ceqs q of
       | NONE => NONE
       | SOME y => compute_pure_binop bop x y) /\
  compute_eval_pure (SUC ck) ceqs (App f cs) =
    (case ALOOKUP ceqs f of
       | NONE => NONE
       | SOME (args,exp) =>
         if LENGTH args <> LENGTH cs then NONE
         else
           case compute_eval_pure_list ck ceqs cs of
           | NONE => NONE
           | SOME values =>
               compute_eval_pure ck ceqs
                 (compute_pure_subst (ZIP (args,values)) exp)) /\
  compute_eval_pure (SUC ck) ceqs (If p q r) =
    (case compute_eval_pure ck ceqs p of
     | NONE => NONE
     | SOME (Num 0) => compute_eval_pure ck ceqs r
     | SOME (Num n) => compute_eval_pure ck ceqs q
     | SOME (Pair _ _) => compute_eval_pure ck ceqs r
     | SOME _ => NONE) /\
  compute_eval_pure (SUC ck) ceqs (Let s p q) =
    (case compute_eval_pure ck ceqs p of
       | NONE => NONE
       | SOME x =>
           compute_eval_pure ck ceqs
             (compute_pure_subst [(s,x)] q)) /\
  compute_eval_pure_list 0 ceqs expressions = NONE /\
  compute_eval_pure_list (SUC ck) ceqs [] = SOME [] /\
  compute_eval_pure_list (SUC ck) ceqs (c::cs) =
    (case compute_eval_pure ck ceqs c of
     | NONE => NONE
     | SOME x =>
       case compute_eval_pure_list ck ceqs cs of
       | NONE => NONE
       | SOME xs => SOME (x::xs))
Termination
  WF_REL_TAC ‘measure $ λx.
    case x of
    | INL (ck,_,_) => ck
    | INR (ck,_,_) => ck’
End

Theorem compute_eval_pure_refines_both:
  (!fuel ceqs expression result clock state.
     fuel <= clock /\
     compute_eval_pure fuel ceqs expression = SOME result ==>
     compute_eval clock ceqs expression state =
       (M_success result,state)) /\
  (!fuel ceqs expressions results clock state.
     fuel <= clock /\
     compute_eval_pure_list fuel ceqs expressions = SOME results ==>
     compute_eval_list clock ceqs expressions state =
       (M_success results,state))
Proof
  ho_match_mp_tac compute_eval_pure_ind
  >> rpt conj_tac
  >- simp [compute_eval_pure_def]
  >- simp [compute_eval_pure_def]
  >- simp [compute_eval_pure_def, compute_eval_def,
           ml_monadBaseTheory.st_ex_return_def]
  >- (rw [compute_eval_pure_def]
      >> Cases_on `compute_eval_pure fuel ceqs expression` >> gvs []
      >> Cases_on `compute_eval_pure fuel ceqs expression'` >> gvs []
      >> rw [Once compute_eval_def]
      >> sg `fuel <= clock`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def])
  >- (rw [compute_eval_pure_def]
      >> Cases_on `compute_eval_pure fuel ceqs expression` >> gvs []
      >> rw [Once compute_eval_def]
      >> sg `fuel <= clock`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> metis_tac [compute_pure_uop_refines])
  >- (rw [compute_eval_pure_def]
      >> Cases_on `compute_eval_pure fuel ceqs expression` >> gvs []
      >> Cases_on `compute_eval_pure fuel ceqs expression'` >> gvs []
      >> rw [Once compute_eval_def]
      >> sg `fuel <= clock`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def]
      >> metis_tac [compute_pure_binop_refines])
  >- (rw [compute_eval_pure_def]
      >> Cases_on `ALOOKUP ceqs f` >> gvs []
      >> PairCases_on `x` >> gvs []
      >> Cases_on `compute_eval_pure_list fuel ceqs expressions` >> gvs []
      >> rw [Once compute_eval_def]
      >> sg `fuel <= clock`
      >> gvs [compute_pure_subst_eq, option_def, check_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def]
      >> simp [ml_monadBaseTheory.st_ex_ignore_bind_def,
               ml_monadBaseTheory.st_ex_bind_def])
  >- (rw [compute_eval_pure_def]
      >> Cases_on `compute_eval_pure fuel ceqs expression` >> gvs []
      >> Cases_on `x` >> gvs []
      >> TRY (Cases_on `n` >> gvs [])
      >> rw [Once compute_eval_def]
      >> sg `fuel <= clock`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def])
  >- (rw [compute_eval_pure_def]
      >> Cases_on `compute_eval_pure fuel ceqs expression` >> gvs []
      >> rw [Once compute_eval_def]
      >> sg `fuel <= clock`
      >> gvs [compute_pure_subst_eq,
              ml_monadBaseTheory.st_ex_bind_def])
  >- simp [compute_eval_pure_def]
  >- simp [compute_eval_pure_def, compute_eval_def,
           ml_monadBaseTheory.st_ex_return_def]
  >- (rw [compute_eval_pure_def]
      >> Cases_on `compute_eval_pure fuel ceqs expression` >> gvs []
      >> Cases_on `compute_eval_pure_list fuel ceqs expressions` >> gvs []
      >> rw [Once compute_eval_def]
      >> sg `fuel <= clock`
      >> gvs [ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def])
QED

Theorem compute_eval_pure_refines:
  !fuel ceqs expression result clock (state:hol_refs).
    fuel <= clock /\
    compute_eval_pure fuel ceqs expression = SOME result ==>
    compute_eval clock ceqs expression state = (M_success result,state)
Proof
  metis_tac [compute_eval_pure_refines_both]
QED

val _ = cv_trans compute_pure_to_num_def;
val _ = cv_trans compute_pure_uop_def;
val _ = cv_trans compute_pure_binop_def;
val _ = cv_trans compute_pure_remove_binding_def;
val _ = cv_trans compute_pure_subst_def;
val compute_eval_pure_pre_def =
  cv_auto_trans_pre "" (compute_eval_pure_def |> measure_args [0,0]);

Theorem compute_eval_pure_pre_both:
  !ck.
    (!ceqs expression. compute_eval_pure_pre ck ceqs expression) /\
    (!ceqs expressions. compute_eval_pure_list_pre ck ceqs expressions)
Proof
  Induct
  >- (rw [Once compute_eval_pure_pre_def]
      >> rw [Once compute_eval_pure_pre_def])
  >> conj_tac
  >- (rpt gen_tac >> Cases_on `expression`
      >> rw [Once compute_eval_pure_pre_def])
  >> rpt gen_tac >> Cases_on `expressions`
  >> rw [Once compute_eval_pure_pre_def]
QED

Theorem compute_eval_pure_pre[cv_pre]:
  (!ck ceqs expression. compute_eval_pure_pre ck ceqs expression) /\
  (!ck ceqs expressions. compute_eval_pure_list_pre ck ceqs expressions)
Proof
  metis_tac [compute_eval_pure_pre_both]
QED

val _ = export_theory ();
