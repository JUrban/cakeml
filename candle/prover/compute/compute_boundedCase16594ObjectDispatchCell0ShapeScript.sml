(*****************************************************************************
 * Authenticated evaluator shapes for the genuine case-16594 cell-0 call.
 *
 * The data theory is mechanically exported from Candle's exact 175-equation
 * closure.  These lookup theorems pin the four control functions used by the
 * whole-call evaluator proof; numerical instruction bodies remain behind the
 * exact one-step premises of the subsequent trace theorem.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchCell0Shape
Ancestors
  compute_boundedCase16594ObjectDispatchCell0Data
Libs
  bossLib preamble

Definition bounded_case16594_object_dispatch_step_body_def:
  bounded_case16594_object_dispatch_step_body =
    If (Binop Eq (Var «code») (Num 0))
      (App «candle_cv_q_packed_object_ordinary_step»
        [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
         Var «source»;Var «certificates»;Var «stack»])
      (App «candle_cv_q_packed_object_specialized_step»
        [Var «center_boxes»;Var «outer_boxes»;Var «radii»;Var «code»;
         Var «source»;Var «certificates»;Var «stack»])
End

Definition bounded_case16594_object_dispatch_program_body_def:
  bounded_case16594_object_dispatch_program_body =
    If (Uop Ispair (Var «codes»))
      (If (Uop Ispair (Var «sources»))
        (Let «step»
          (App «candle_cv_q_packed_object_dispatch_step»
            [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
             Uop Fst (Var «codes»);Uop Fst (Var «sources»);
             Var «certificates»;Var «stack»])
          (If (Binop Eq (Uop Fst (Var «step»)) (Num 1))
            (App «candle_cv_q_packed_object_dispatch_program»
              [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
               Uop Snd (Var «codes»);Uop Snd (Var «sources»);
               Uop Snd (Uop Snd (Var «step»));
               Uop Fst (Uop Snd (Var «step»))])
            (Pair (Num 0) (Pair (Var «stack») (Var «certificates»)))))
        (Pair (Num 0) (Pair (Var «stack») (Var «certificates»))))
      (If (Uop Ispair (Var «sources»))
        (Pair (Num 0) (Pair (Var «stack») (Var «certificates»)))
        (Pair (Num 1) (Pair (Var «stack») (Var «certificates»))))
End

Definition bounded_case16594_object_dispatch_entry_body_def:
  bounded_case16594_object_dispatch_entry_body =
    Let «execution»
      (App «candle_cv_q_packed_object_dispatch_program»
        [Var «center_boxes»;Var «outer_boxes»;Var «radii»;Var «codes»;
         Var «sources»;Var «certificates»;Num 0])
      (Let «stack» (Uop Fst (Uop Snd (Var «execution»)))
        (Let «certificate_rest» (Uop Snd (Uop Snd (Var «execution»)))
          (If (Binop Eq (Uop Fst (Var «execution»)) (Num 1))
            (If (Uop Ispair (Var «stack»))
              (If (Binop Eq (Uop Snd (Var «stack»)) (Num 0))
                (If (Binop Eq (Var «certificate_rest») (Num 0))
                  (App «candle_cv_q_packed_object_state_accept6»
                    [Var «radii»;Uop Fst (Var «stack»)])
                  (Num 0))
                (Num 0))
              (Num 0))
            (Num 0))))
End

Definition bounded_case16594_object_state_accept6_body_def:
  bounded_case16594_object_state_accept6_body =
    App «candle_cv_q_packed_object_accept6»
      [App «candle_cv_q_packed_object_state_domain» [Var «state»];
       Var «radii»;
       App «candle_cv_q_packed_object_state_center_value» [Var «state»];
       App «candle_cv_q_packed_object_state_center_gradient» [Var «state»];
       App «candle_cv_q_packed_object_state_packed_hessian» [Var «state»]]
End

Theorem bounded_case16594_object_dispatch_step_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_dispatch_step» =
    SOME
      ([«center_boxes»;«outer_boxes»;«radii»;«code»;«source»;
        «certificates»;«stack»],
       bounded_case16594_object_dispatch_step_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_dispatch_program_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_dispatch_program» =
    SOME
      ([«center_boxes»;«outer_boxes»;«radii»;«codes»;«sources»;
        «certificates»;«stack»],
       bounded_case16594_object_dispatch_program_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_dispatch_entry_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_dispatch_entry» =
    SOME
      ([«center_boxes»;«outer_boxes»;«radii»;«codes»;«sources»;
        «certificates»],
       bounded_case16594_object_dispatch_entry_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_state_accept6_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_accept6» =
    SOME
      ([«radii»;«state»],bounded_case16594_object_state_accept6_body)
Proof
  EVAL_TAC
QED

val _ = export_theory ();
