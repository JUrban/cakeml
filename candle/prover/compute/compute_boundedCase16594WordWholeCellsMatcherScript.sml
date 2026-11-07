(*****************************************************************************
 * Streaming matcher for the complete case-16594 packed-cell/job lists.      *
 *                                                                           *
 * The recursion consumes one authenticated external certificate cell, one   *
 * packed ordinary-call cell, and one ordinary-call job in lockstep.  It      *
 * fails closed on parser failure, malformed cv lists, early termination,     *
 * trailing bytes, or unequal list lengths.                                  *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeCellsMatcher
Ancestors
  compute_boundedCase16594WordWholeCellMatcher
  compute_boundedCase16594WordWholeJobsProducer
  compute_boundedPackedAnalyticCheck
Libs
  bossLib preamble intLib

Definition bounded_case16594_word_whole_cells_match_def:
  bounded_case16594_word_whole_cells_match 0 bytes packed_cells jobs =
    (if bytes = [] /\ packed_cells = Num 0 /\ jobs = Num 0
     then SOME (Num 1)
     else NONE) /\
  bounded_case16594_word_whole_cells_match (SUC remaining) bytes
      packed_cells jobs =
    case bounded_packed_chars_analytic_cell 6 31 bytes of
    | NONE => NONE
    | SOME (cell,rest) =>
        case packed_cells of
        | Pair packed_cell packed_cells_tail =>
            (case jobs of
             | Pair job jobs_tail =>
                 (case bounded_case16594_word_whole_cell_match
                         cell packed_cell job of
                  | NONE => NONE
                  | SOME source_box =>
                      bounded_case16594_word_whole_cells_match remaining
                        rest packed_cells_tail jobs_tail)
             | _ => NONE)
        | _ => NONE
End

Theorem bounded_case16594_word_whole_cells_match_eval_clock:
  !remaining bytes packed_cells jobs clock.
    bounded_case16594_word_whole_cells_match remaining bytes
        packed_cells jobs = SOME (Num 1) /\
    524405 +
        2 * bounded_case16594_object_cv_list_length
          bounded_case16594_generic_prefix167_codes_cv +
        remaining + 12 < clock ==>
    compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_q_packed_object_whole_jobs_check»
        [from_cv bounded_case16594_generic_prefix167_codes_cv;
         from_cv bounded_case16594_generic_prefix167_sources_cv;
         from_cv packed_cells;from_cv jobs])
      (refs:hol_refs) = (M_success (from_cv (Num 1)),refs)
Proof
  Induct
  >- (rpt gen_tac
      >> rw [bounded_case16594_word_whole_cells_match_def]
      >> irule
           (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
             compute_boundedCase16594WordWholeJobsProducerTheory.bounded_case16594_word_whole_jobs_empty_eval)
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> strip_tac
  >> fs [bounded_case16594_word_whole_cells_match_def]
  >> every_case_tac
  >> gvs []
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         compute_boundedCase16594WordWholeJobsProducerTheory.bounded_case16594_word_whole_jobs_cons_eval)
  >> rpt conj_tac
  >- intLib.ARITH_TAC
  >- (irule
        (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          compute_boundedCase16594WordWholeCellMatcherTheory.bounded_case16594_word_whole_cell_match_eval_clock)
      >> PairCases_on `q`
      >> conj_tac >- intLib.ARITH_TAC
      >> MAP_EVERY qexists_tac [`x`,`q1`,`q3`,`q0`,`q2`]
      >> asm_rewrite_tac [])
  >> qpat_x_assum `!bytes' packed_cells' jobs' clock'. _`
       (qspecl_then [`r`,`c0'`,`c0`,`clock - 1`] mp_tac)
  >> impl_tac
  >- (conj_tac >- asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> simp []
QED

Theorem bounded_case16594_word_whole_cells_match_zero_contract:
  bounded_case16594_word_whole_cells_match 0 bytes packed_cells jobs =
      SOME (Num 1) ==>
  bytes = [] /\ packed_cells = Num 0 /\ jobs = Num 0
Proof
  simp [bounded_case16594_word_whole_cells_match_def]
  >> every_case_tac
  >> simp []
QED

Theorem bounded_case16594_word_whole_cells_match_rejects_short_cells:
  bounded_case16594_word_whole_cells_match (SUC remaining) bytes
      (Num value) jobs = NONE
Proof
  simp [bounded_case16594_word_whole_cells_match_def]
  >> every_case_tac
  >> simp []
QED

Theorem bounded_case16594_word_whole_cells_match_rejects_short_jobs:
  bounded_case16594_word_whole_cells_match (SUC remaining) bytes
      (Pair packed_cell packed_cells) (Num value) = NONE
Proof
  simp [bounded_case16594_word_whole_cells_match_def]
  >> every_case_tac
  >> simp []
QED

val _ = export_theory ();
