(*****************************************************************************
 * Exact Candle guard contract for the first atan packet emitted by the
 * authenticated fixed-word cell-0 trace.
 *
 * This is a bounded representation discriminator.  It does not replay the
 * analytic program: the eight interval fields are projected from the already
 * authenticated 134-item runtime packet stream, converted exactly to object-q
 * values, and checked by the six production Candle guards.  Theory creation
 * fails unless every guard returns true.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WordAtan0PureContract
Ancestors
  compute_boundedCase16594Cell0AuthenticatedWordRuntimeTrace
  compute_boundedCase16594ObjectCertifiedAtanDispatchInvariant
Libs
  bossLib preamble cv_transLib

val runtime_packets_tm =
  rhs
    (concl
      compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_packets_def);
val (runtime_packets,_) = listSyntax.dest_list runtime_packets_tm;
val _ =
  if List.length runtime_packets = 134 then ()
  else raise Fail "unexpected authenticated runtime-packet length";

(* The first three typed certificates are sqrt (5 fields), inverse (2), and
   atan (8), so the first atan packet occupies offsets 7 through 14. *)
val first_atan_word_fields = List.take (List.drop (runtime_packets,7),8);
val interval_to_object_q =
  prim_mk_const
    {Name="bounded_interval64_object_q_cv",
     Thy="compute_boundedAnalyticObjectCertificateRefinement"};
fun interval_object_q_literal interval =
  rhs (concl (EVAL (mk_comb (interval_to_object_q,interval))));
val first_atan_object_fields = map interval_object_q_literal first_atan_word_fields;

fun define_literal name tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,``:cv``),tm));

val field_names =
  ["bounded_case16594_cell0_word_atan0_center_input_cv",
   "bounded_case16594_cell0_word_atan0_box_input_cv",
   "bounded_case16594_cell0_word_atan0_center_result_cv",
   "bounded_case16594_cell0_word_atan0_center_square_cv",
   "bounded_case16594_cell0_word_atan0_center_derivative_cv",
   "bounded_case16594_cell0_word_atan0_box_square_cv",
   "bounded_case16594_cell0_word_atan0_box_derivative_cv",
   "bounded_case16594_cell0_word_atan0_box_derivative_square_cv"];
val field_defs =
  ListPair.map
    (fn (name,tm) => define_literal name tm)
    (field_names,first_atan_object_fields);
val _ = List.app cv_trans field_defs;

fun evaluate_guard name tm =
  let
    val result = time cv_eval tm
    val _ =
      print
        (name ^ " => " ^
         term_to_string (rhs (concl result)) ^ "\n")
  in
    save_thm (name,result)
  end;

val bounded_case16594_cell0_word_atan0_center_result_pure_eval =
  evaluate_guard "bounded_case16594_cell0_word_atan0_center_result_pure_eval"
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_atn_certificate»
          [from_cv bounded_case16594_cell0_word_atan0_center_input_cv;
           from_cv bounded_case16594_cell0_word_atan0_center_result_cv])``;

val bounded_case16594_cell0_word_atan0_center_square_pure_eval =
  evaluate_guard "bounded_case16594_cell0_word_atan0_center_square_pure_eval"
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_encloses»
          [from_cv bounded_case16594_cell0_word_atan0_center_square_cv;
           App «candle_cv_q_interval_normalize»
             [App «candle_cv_q_interval_square»
               [from_cv bounded_case16594_cell0_word_atan0_center_input_cv]]])``;

val bounded_case16594_cell0_word_atan0_center_inverse_pure_eval =
  evaluate_guard "bounded_case16594_cell0_word_atan0_center_inverse_pure_eval"
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_inv_certificate»
          [App «candle_cv_q_packed_object_atn_denominator»
             [from_cv bounded_case16594_cell0_word_atan0_center_square_cv];
           from_cv bounded_case16594_cell0_word_atan0_center_derivative_cv])``;

val bounded_case16594_cell0_word_atan0_box_square_pure_eval =
  evaluate_guard "bounded_case16594_cell0_word_atan0_box_square_pure_eval"
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_encloses»
          [from_cv bounded_case16594_cell0_word_atan0_box_square_cv;
           App «candle_cv_q_interval_normalize»
             [App «candle_cv_q_interval_square»
               [from_cv bounded_case16594_cell0_word_atan0_box_input_cv]]])``;

val bounded_case16594_cell0_word_atan0_box_inverse_pure_eval =
  evaluate_guard "bounded_case16594_cell0_word_atan0_box_inverse_pure_eval"
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_inv_certificate»
          [App «candle_cv_q_packed_object_atn_denominator»
             [from_cv bounded_case16594_cell0_word_atan0_box_square_cv];
           from_cv bounded_case16594_cell0_word_atan0_box_derivative_cv])``;

val bounded_case16594_cell0_word_atan0_derivative_square_pure_eval =
  evaluate_guard "bounded_case16594_cell0_word_atan0_derivative_square_pure_eval"
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_square_outer_certificate»
          [from_cv bounded_case16594_cell0_word_atan0_box_derivative_cv;
           from_cv bounded_case16594_cell0_word_atan0_box_derivative_cv;
           from_cv
             bounded_case16594_cell0_word_atan0_box_derivative_square_cv])``;

(* This final theorem is also the fail-closed assertion: if any recorded
   evaluation above is not true, the conjunction cannot be discharged and
   the theory does not export. *)
Theorem bounded_case16594_cell0_word_atan0_fixed_pure_contract:
  bounded_case16594_object_atan_fixed_pure_contract
    bounded_case16594_cell0_word_atan0_center_input_cv
    bounded_case16594_cell0_word_atan0_box_input_cv
    bounded_case16594_cell0_word_atan0_center_result_cv
    bounded_case16594_cell0_word_atan0_center_square_cv
    bounded_case16594_cell0_word_atan0_center_derivative_cv
    bounded_case16594_cell0_word_atan0_box_square_cv
    bounded_case16594_cell0_word_atan0_box_derivative_cv
    bounded_case16594_cell0_word_atan0_box_derivative_square_cv
Proof
  simp
    [compute_boundedCase16594ObjectCertifiedAtanDispatchInvariantTheory.bounded_case16594_object_atan_fixed_pure_contract_def,
     bounded_case16594_cell0_word_atan0_center_result_pure_eval,
     bounded_case16594_cell0_word_atan0_center_square_pure_eval,
     bounded_case16594_cell0_word_atan0_center_inverse_pure_eval,
     bounded_case16594_cell0_word_atan0_box_square_pure_eval,
     bounded_case16594_cell0_word_atan0_box_inverse_pure_eval,
     bounded_case16594_cell0_word_atan0_derivative_square_pure_eval]
QED

val _ = export_theory ();
