(*****************************************************************************
 * Complete registered evaluator semantics for the historical three-variable
 * u calculation after its gradient prefix.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalUThreeEval
Ancestors
  compute_registeredCase10173HistoricalUValueObjectEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_u_point_elements_def:
  registered_case10173_fs_hist_u_point_elements lower upper
      lower_nonnegative upper_nonpositive =
    let lower_point = Pair lower lower;
        upper_point = Pair upper upper
    in
      if lower_nonnegative then
        [upper_point;upper_point;lower_point;lower_point]
      else if upper_nonpositive then
        [lower_point;lower_point;upper_point;upper_point]
      else
        [lower_point;upper_point;upper_point;lower_point]
End

Theorem registered_case10173_fs_hist_u_points_object_as_elements:
  registered_case10173_fs_hist_u_points_object lower upper
      lower_nonnegative upper_nonpositive =
    registered_case10173_cv_list
      (registered_case10173_fs_hist_u_point_elements lower upper
        lower_nonnegative upper_nonpositive)
Proof
  Cases_on `lower_nonnegative`
  >> Cases_on `upper_nonpositive`
  >> simp
    [compute_registeredCase10173HistoricalUPointsEvalTheory.registered_case10173_fs_hist_u_points_object_def,
     registered_case10173_fs_hist_u_point_elements_def]
QED

Definition registered_case10173_fs_hist_u_after_gradients_object_def:
  registered_case10173_fs_hist_u_after_gradients_object x0 x1 x2 g0 g1 g2 =
    case x0 of
    | Num _ => NONE
    | Pair x0_lower x0_upper =>
      case x1 of
      | Num _ => NONE
      | Pair x1_lower x1_upper =>
        case x2 of
        | Num _ => NONE
        | Pair x2_lower x2_upper =>
          case g0 of
          | Num _ => NONE
          | Pair g0_lower g0_upper =>
            case g1 of
            | Num _ => NONE
            | Pair g1_lower g1_upper =>
              case g2 of
              | Num _ => NONE
              | Pair g2_lower g2_upper =>
                case bounded_object_fs_raw_le
                    (Pair (Num 0) (Num 0)) g0_lower of
                | NONE => NONE
                | SOME g0_lower_nonnegative =>
                  case bounded_object_fs_raw_le g0_upper
                      (Pair (Num 0) (Num 0)) of
                  | NONE => NONE
                  | SOME g0_upper_nonpositive =>
                    case bounded_object_fs_raw_le
                        (Pair (Num 0) (Num 0)) g1_lower of
                    | NONE => NONE
                    | SOME g1_lower_nonnegative =>
                      case bounded_object_fs_raw_le g1_upper
                          (Pair (Num 0) (Num 0)) of
                      | NONE => NONE
                      | SOME g1_upper_nonpositive =>
                        case bounded_object_fs_raw_le
                            (Pair (Num 0) (Num 0)) g2_lower of
                        | NONE => NONE
                        | SOME g2_lower_nonnegative =>
                          case bounded_object_fs_raw_le g2_upper
                              (Pair (Num 0) (Num 0)) of
                          | NONE => NONE
                          | SOME g2_upper_nonpositive =>
                            let points0 =
                                  registered_case10173_fs_hist_u_point_elements
                                    x0_lower x0_upper g0_lower_nonnegative
                                    g0_upper_nonpositive;
                                points1 =
                                  registered_case10173_fs_hist_u_point_elements
                                    x1_lower x1_upper g1_lower_nonnegative
                                    g1_upper_nonpositive;
                                points2 =
                                  registered_case10173_fs_hist_u_point_elements
                                    x2_lower x2_upper g2_lower_nonnegative
                                    g2_upper_nonpositive
                            in
                              case
                                registered_case10173_fs_hist_u_value_formula_object
                                  2 points0 points1 points2 of
                              | NONE => NONE
                              | SOME lower =>
                                case
                                  registered_case10173_fs_hist_u_value_formula_object
                                    0 points0 points1 points2 of
                                | NONE => NONE
                                | SOME upper =>
                                  case lower of
                                  | Num _ => NONE
                                  | Pair lower_endpoint _ =>
                                    case upper of
                                    | Num _ => NONE
                                    | Pair _ upper_endpoint =>
                                      SOME
                                        (Pair
                                          (Pair lower_endpoint upper_endpoint)
                                          (registered_case10173_cv_list
                                            [g0;g1;g2]))
End

Definition registered_case10173_fs_hist_u_three_object_def:
  registered_case10173_fs_hist_u_three_object x0 x1 x2 =
    case bounded_object_fs_interval_neg x0 of
    | NONE => NONE
    | SOME negative_x0 =>
      case registered_case10173_fs_interval_sum_object
          [negative_x0;x1;x2] of
      | NONE => NONE
      | SOME g0_half =>
        case registered_case10173_fs_interval_raw_scale_object 2 g0_half of
        | NONE => NONE
        | SOME g0 =>
          case bounded_object_fs_interval_neg x1 of
          | NONE => NONE
          | SOME negative_x1 =>
            case registered_case10173_fs_interval_sum_object
                [x0;negative_x1;x2] of
            | NONE => NONE
            | SOME g1_half =>
              case registered_case10173_fs_interval_raw_scale_object
                  2 g1_half of
              | NONE => NONE
              | SOME g1 =>
                case bounded_object_fs_interval_neg x2 of
                | NONE => NONE
                | SOME negative_x2 =>
                  case registered_case10173_fs_interval_sum_object
                      [x0;x1;negative_x2] of
                  | NONE => NONE
                  | SOME g2_half =>
                    case registered_case10173_fs_interval_raw_scale_object
                        2 g2_half of
                    | NONE => NONE
                    | SOME g2 =>
                      registered_case10173_fs_hist_u_after_gradients_object
                        x0 x1 x2 g0 g1 g2
End

Theorem registered_case10173_fs_hist_u_after_gradients_trace_eval:
  bounded_object_fs_raw_le (Pair (Num 0) (Num 0)) g0_lower =
      SOME g0_lower_nonnegative /\
  bounded_object_fs_raw_le g0_upper (Pair (Num 0) (Num 0)) =
      SOME g0_upper_nonpositive /\
  bounded_object_fs_raw_le (Pair (Num 0) (Num 0)) g1_lower =
      SOME g1_lower_nonnegative /\
  bounded_object_fs_raw_le g1_upper (Pair (Num 0) (Num 0)) =
      SOME g1_upper_nonpositive /\
  bounded_object_fs_raw_le (Pair (Num 0) (Num 0)) g2_lower =
      SOME g2_lower_nonnegative /\
  bounded_object_fs_raw_le g2_upper (Pair (Num 0) (Num 0)) =
      SOME g2_upper_nonpositive /\
  registered_case10173_fs_hist_u_value_formula_object 2
      (registered_case10173_fs_hist_u_point_elements x0_lower x0_upper
        g0_lower_nonnegative g0_upper_nonpositive)
      (registered_case10173_fs_hist_u_point_elements x1_lower x1_upper
        g1_lower_nonnegative g1_upper_nonpositive)
      (registered_case10173_fs_hist_u_point_elements x2_lower x2_upper
        g2_lower_nonnegative g2_upper_nonpositive) =
    SOME (Pair lower_endpoint lower_other) /\
  registered_case10173_fs_hist_u_value_formula_object 0
      (registered_case10173_fs_hist_u_point_elements x0_lower x0_upper
        g0_lower_nonnegative g0_upper_nonpositive)
      (registered_case10173_fs_hist_u_point_elements x1_lower x1_upper
        g1_lower_nonnegative g1_upper_nonpositive)
      (registered_case10173_fs_hist_u_point_elements x2_lower x2_upper
        g2_lower_nonnegative g2_upper_nonpositive) =
    SOME (Pair upper_other upper_endpoint) /\
  70 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«x0»,from_cv (Pair x0_lower x0_upper));
         («x1»,from_cv (Pair x1_lower x1_upper));
         («x2»,from_cv (Pair x2_lower x2_upper));
         («g0»,from_cv (Pair g0_lower g0_upper));
         («g1»,from_cv (Pair g1_lower g1_upper));
         («g2»,from_cv (Pair g2_lower g2_upper))]
        registered_case10173_fs_hist_u_three_after_gradients_body)
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Pair lower_endpoint upper_endpoint)
          (registered_case10173_cv_list
            [Pair g0_lower g0_upper;Pair g1_lower g1_upper;
             Pair g2_lower g2_upper]))),refs)
Proof
  rpt strip_tac
  >> simp
       [compute_registeredCase10173HistoricalUThreeGradientEvalTheory.registered_case10173_fs_hist_u_three_after_gradients_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (registered_case10173_cv_list
            (registered_case10173_fs_hist_u_point_elements
              x0_lower x0_upper g0_lower_nonnegative
              g0_upper_nonpositive))`
  >> conj_tac
  >- (simp [GSYM registered_case10173_fs_hist_u_points_object_as_elements]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173HistoricalUPointsEvalTheory.registered_case10173_fs_hist_u_points_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (registered_case10173_cv_list
            (registered_case10173_fs_hist_u_point_elements
              x1_lower x1_upper g1_lower_nonnegative
              g1_upper_nonpositive))`
  >> conj_tac
  >- (simp [GSYM registered_case10173_fs_hist_u_points_object_as_elements]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173HistoricalUPointsEvalTheory.registered_case10173_fs_hist_u_points_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (registered_case10173_cv_list
            (registered_case10173_fs_hist_u_point_elements
              x2_lower x2_upper g2_lower_nonnegative
              g2_upper_nonpositive))`
  >> conj_tac
  >- (simp [GSYM registered_case10173_fs_hist_u_points_object_as_elements]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173HistoricalUPointsEvalTheory.registered_case10173_fs_hist_u_points_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (Pair lower_endpoint lower_other)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_hist_u_value_formula_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (Pair upper_other upper_endpoint)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_hist_u_value_formula_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |-> `Pair lower_endpoint upper_endpoint`,
            `right_result` |->
              `registered_case10173_cv_list
                [Pair g0_lower g0_upper;Pair g1_lower g1_upper;
                 Pair g2_lower g2_upper]`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`left_result` |-> `lower_endpoint`,
             `right_result` |-> `upper_endpoint`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> PURE_REWRITE_TAC [GSYM compute_execTheory.from_cv_def]
  >> irule
       compute_registeredCase10173HistoricalTupleEvalTheory.registered_case10173_fs_hist_three_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_u_after_gradients_object_eval:
  registered_case10173_fs_hist_u_after_gradients_object
      (Pair x0_lower x0_upper) (Pair x1_lower x1_upper)
      (Pair x2_lower x2_upper) (Pair g0_lower g0_upper)
      (Pair g1_lower g1_upper) (Pair g2_lower g2_upper) = SOME result /\
  70 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«x0»,from_cv (Pair x0_lower x0_upper));
         («x1»,from_cv (Pair x1_lower x1_upper));
         («x2»,from_cv (Pair x2_lower x2_upper));
         («g0»,from_cv (Pair g0_lower g0_upper));
         («g1»,from_cv (Pair g1_lower g1_upper));
         («g2»,from_cv (Pair g2_lower g2_upper))]
        registered_case10173_fs_hist_u_three_after_gradients_body)
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> fs [registered_case10173_fs_hist_u_after_gradients_object_def]
  >> every_case_tac
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_u_after_gradients_trace_eval)
  >> simp []
QED

Theorem registered_case10173_fs_hist_u_after_gradients_any_object_eval:
  registered_case10173_fs_hist_u_after_gradients_object
      x0 x1 x2 g0 g1 g2 = SOME result /\
  70 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«x0»,from_cv x0);(«x1»,from_cv x1);(«x2»,from_cv x2);
         («g0»,from_cv g0);(«g1»,from_cv g1);(«g2»,from_cv g2)]
        registered_case10173_fs_hist_u_three_after_gradients_body)
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> Cases_on `x0` >- fs [registered_case10173_fs_hist_u_after_gradients_object_def]
  >> Cases_on `x1` >- fs [registered_case10173_fs_hist_u_after_gradients_object_def]
  >> Cases_on `x2` >- fs [registered_case10173_fs_hist_u_after_gradients_object_def]
  >> Cases_on `g0` >- fs [registered_case10173_fs_hist_u_after_gradients_object_def]
  >> Cases_on `g1` >- fs [registered_case10173_fs_hist_u_after_gradients_object_def]
  >> Cases_on `g2` >- fs [registered_case10173_fs_hist_u_after_gradients_object_def]
  >> irule registered_case10173_fs_hist_u_after_gradients_object_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_u_three_object_eval:
  bounded_object_fs_interval_neg x0 = SOME negative_x0 /\
  registered_case10173_fs_interval_sum_object [negative_x0;x1;x2] =
      SOME g0_half /\
  registered_case10173_fs_interval_raw_scale_object 2 g0_half = SOME g0 /\
  bounded_object_fs_interval_neg x1 = SOME negative_x1 /\
  registered_case10173_fs_interval_sum_object [x0;negative_x1;x2] =
      SOME g1_half /\
  registered_case10173_fs_interval_raw_scale_object 2 g1_half = SOME g1 /\
  bounded_object_fs_interval_neg x2 = SOME negative_x2 /\
  registered_case10173_fs_interval_sum_object [x0;x1;negative_x2] =
      SOME g2_half /\
  registered_case10173_fs_interval_raw_scale_object 2 g2_half = SOME g2 /\
  registered_case10173_fs_hist_u_after_gradients_object
      x0 x1 x2 g0 g1 g2 = SOME result /\
  80 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u_three»
        [from_cv x0;from_cv x1;from_cv x2]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 4)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«x0»,from_cv x0);(«x1»,from_cv x1);(«x2»,from_cv x2);
             («g0»,from_cv g0);(«g1»,from_cv g1);(«g2»,from_cv g2)]
            registered_case10173_fs_hist_u_three_after_gradients_body) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalUThreeGradientEvalTheory.registered_case10173_fs_hist_u_three_gradient_prefix_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule registered_case10173_fs_hist_u_after_gradients_any_object_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_u_three_compact_object_eval:
  registered_case10173_fs_hist_u_three_object x0 x1 x2 = SOME result /\
  80 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u_three»
        [from_cv x0;from_cv x1;from_cv x2]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> fs [registered_case10173_fs_hist_u_three_object_def]
  >> every_case_tac
  >> gvs []
  >> irule registered_case10173_fs_hist_u_three_object_eval
  >> simp []
QED

val _ = export_theory ();
