(*****************************************************************************
 * A compact object contract for the registered historical u value formula.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalUValueObjectEval
Ancestors
  compute_registeredCase10173HistoricalUValueEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_u_value_formula_object_def:
  registered_case10173_fs_hist_u_value_formula_object selector
      points0 points1 points2 =
    if selector + 1 < LENGTH points0 /\
       selector + 1 < LENGTH points1 /\
       selector + 1 < LENGTH points2 then
      let n0 = EL selector points0;
          n1 = EL selector points1;
          n2 = EL selector points2;
          p0 = EL (selector + 1) points0;
          p1 = EL (selector + 1) points1;
          p2 = EL (selector + 1) points2
      in
        case bounded_object_fs_raw_interval_mul n0 n0 of
        | NONE => NONE
        | SOME n0_square =>
          case bounded_object_fs_interval_neg n0_square of
          | NONE => NONE
          | SOME negative_n0_square =>
            case bounded_object_fs_raw_interval_mul n1 n1 of
            | NONE => NONE
            | SOME n1_square =>
              case bounded_object_fs_interval_neg n1_square of
              | NONE => NONE
              | SOME negative_n1_square =>
                case bounded_object_fs_raw_interval_mul n2 n2 of
                | NONE => NONE
                | SOME n2_square =>
                  case bounded_object_fs_interval_neg n2_square of
                  | NONE => NONE
                  | SOME negative_n2_square =>
                    case bounded_object_fs_raw_interval_mul p0 p1 of
                    | NONE => NONE
                    | SOME p01 =>
                      case registered_case10173_fs_interval_raw_scale_object
                          2 p01 of
                      | NONE => NONE
                      | SOME twice_p01 =>
                        case bounded_object_fs_raw_interval_mul p1 p2 of
                        | NONE => NONE
                        | SOME p12 =>
                          case registered_case10173_fs_interval_raw_scale_object
                              2 p12 of
                          | NONE => NONE
                          | SOME twice_p12 =>
                            case bounded_object_fs_raw_interval_mul p2 p0 of
                            | NONE => NONE
                            | SOME p20 =>
                              case registered_case10173_fs_interval_raw_scale_object
                                  2 p20 of
                              | NONE => NONE
                              | SOME twice_p20 =>
                                case registered_case10173_fs_interval_sum_object
                                    [negative_n0_square;negative_n1_square;
                                     negative_n2_square;twice_p01;twice_p12;
                                     twice_p20] of
                                | NONE => NONE
                                | SOME raw =>
                                    bounded_object_fs_raw_interval_round
                                      1000000000000 raw
    else NONE
End

Theorem registered_case10173_fs_hist_u_value_formula_object_eval:
  registered_case10173_fs_hist_u_value_formula_object selector
      points0 points1 points2 = SOME result /\
  selector + 40 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u_value_formula»
        [from_cv (Num selector);
         from_cv (registered_case10173_cv_list points0);
         from_cv (registered_case10173_cv_list points1);
         from_cv (registered_case10173_cv_list points2)]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> fs [registered_case10173_fs_hist_u_value_formula_object_def]
  >> every_case_tac
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_u_value_formula_trace_eval)
  >> simp []
QED

val _ = export_theory ();
