(*****************************************************************************
 * Exact evaluator result for the first genuine inverse second derivative.
 *****************************************************************************)
Theory compute_boundedCase16594FirstInverseSecondEval
Ancestors
  compute_boundedCase16594FirstInverseDerivativeEval
Libs
  bossLib preamble

Definition bounded_case16594_first_inverse_second_cv_def:
  bounded_case16594_first_inverse_second_cv =
    Pair
      (Pair
        (Pair
          (Num
            65879273652768836518521130352467265338102560565947116697886797590429696)
          (Num 0))
        (Num
          27606985387162255149739023449108101809804435888681546220650096895197183))
      (Pair
        (Pair
          (Num
            1029527435316286236633705440249645280235356285960595099323727872000000)
          (Num 0))
        (Num
          431359146674410236714672241392314090778194310760649159697657763987455))
End

Theorem bounded_case16594_first_inverse_second_pure_eval:
  compute_eval_pure 64 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_inverse_second»
        [from_cv bounded_case16594_first_inverse_reciprocal_cv]) =
    SOME (from_cv bounded_case16594_first_inverse_second_cv)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_first_inverse_second_eval:
  64 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_inverse_second»
        [from_cv bounded_case16594_first_inverse_reciprocal_cv])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_first_inverse_second_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `64`
  >> asm_rewrite_tac [bounded_case16594_first_inverse_second_pure_eval]
QED

val _ = export_theory ();
