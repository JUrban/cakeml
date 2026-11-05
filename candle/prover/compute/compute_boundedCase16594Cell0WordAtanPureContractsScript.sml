(*****************************************************************************
 * Exact Candle guard contracts for every atan packet emitted by the
 * authenticated fixed-word cell-0 trace.
 *
 * Packet boundaries are derived from the typed certificate stream rather
 * than guessed from the flat runtime payload.  Each eight-field atan packet
 * is converted exactly to object-q values and checked by the six production
 * Candle guards.  Theory creation fails closed if the certificate topology,
 * packet length, or any guard result changes.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WordAtanPureContracts
Ancestors
  compute_boundedCase16594Cell0WordAtan0PureContract
Libs
  bossLib preamble cv_transLib

val source_certificates_tm =
  rhs
    (concl
      compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_certificates_def);
val (source_certificates,_) = listSyntax.dest_list source_certificates_tm;

fun certificate_constructor_name certificate =
  fst (dest_const (fst (strip_comb certificate)));

fun certificate_packet_length "BoundedAnalytic64SqrtCertificate" = 5
  | certificate_packet_length "BoundedAnalytic64InverseCertificate" = 2
  | certificate_packet_length "BoundedAnalytic64AtanCertificate" = 8
  | certificate_packet_length constructor =
      raise Fail ("unexpected analytic certificate constructor: " ^ constructor);

fun scan_certificate_packets [] offset atan_offsets =
      (offset,List.rev atan_offsets)
  | scan_certificate_packets (certificate::certificates) offset atan_offsets =
      let
        val constructor = certificate_constructor_name certificate;
        val next_atan_offsets =
          if constructor = "BoundedAnalytic64AtanCertificate" then
            offset::atan_offsets
          else atan_offsets;
      in
        scan_certificate_packets certificates
          (offset + certificate_packet_length constructor) next_atan_offsets
      end;

val (certificate_packet_total,atan_packet_offsets) =
  scan_certificate_packets source_certificates 0 [];
val _ =
  if certificate_packet_total = 134 andalso
     atan_packet_offsets = [7,31,46,70,85,109,124] then ()
  else raise Fail "unexpected authenticated certificate-packet topology";

val runtime_packets_tm =
  rhs
    (concl
      compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_packets_def);
val (runtime_packets,_) = listSyntax.dest_list runtime_packets_tm;
val _ =
  if List.length runtime_packets = certificate_packet_total then ()
  else raise Fail "authenticated runtime packets do not match typed topology";

val interval_to_object_q =
  prim_mk_const
    {Name="bounded_interval64_object_q_cv",
     Thy="compute_boundedAnalyticObjectCertificateRefinement"};
fun interval_object_q_literal interval =
  rhs (concl (EVAL (mk_comb (interval_to_object_q,interval))));

fun define_literal name tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,``:cv``),tm));

val field_suffixes =
  ["center_input_cv", "box_input_cv", "center_result_cv",
   "center_square_cv", "center_derivative_cv", "box_square_cv",
   "box_derivative_cv", "box_derivative_square_cv"];

val field_variables =
  [``center_input:cv``, ``box_input:cv``, ``center_result:cv``,
   ``center_square:cv``, ``center_derivative:cv``, ``box_square:cv``,
   ``box_derivative:cv``, ``box_derivative_square:cv``];

val guard_templates =
  [("center_result",
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_atn_certificate»
          [from_cv (center_input:cv); from_cv (center_result:cv)])``),
   ("center_square",
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_encloses»
          [from_cv (center_square:cv);
           App «candle_cv_q_interval_normalize»
             [App «candle_cv_q_interval_square»
               [from_cv (center_input:cv)]]])``),
   ("center_inverse",
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_inv_certificate»
          [App «candle_cv_q_packed_object_atn_denominator»
             [from_cv (center_square:cv)];
           from_cv (center_derivative:cv)])``),
   ("box_square",
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_encloses»
          [from_cv (box_square:cv);
           App «candle_cv_q_interval_normalize»
             [App «candle_cv_q_interval_square»
               [from_cv (box_input:cv)]]])``),
   ("box_inverse",
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_inv_certificate»
          [App «candle_cv_q_packed_object_atn_denominator»
             [from_cv (box_square:cv)];
           from_cv (box_derivative:cv)])``),
   ("derivative_square",
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_square_outer_certificate»
          [from_cv (box_derivative:cv); from_cv (box_derivative:cv);
           from_cv (box_derivative_square:cv)])``)];

val atan_contract_constant =
  prim_mk_const
    {Name="bounded_case16594_object_atan_fixed_pure_contract",
     Thy="compute_boundedCase16594ObjectCertifiedAtanDispatchInvariant"};

fun instantiate_fields fields tm =
  Term.subst
    (ListPair.map
      (fn (variable,field) => {redex=variable,residue=field})
      (field_variables,fields)) tm;

fun evaluate_guard packet_prefix fields (guard_name,guard_template) =
  let
    val theorem_name = packet_prefix ^ "_" ^ guard_name ^ "_pure_eval";
    val result = time cv_eval (instantiate_fields fields guard_template);
    val _ =
      print
        (theorem_name ^ " => " ^
         term_to_string (rhs (concl result)) ^ "\n");
  in
    save_thm (theorem_name,result)
  end;

fun prove_atan_packet_contract (packet_index,packet_offset) =
  let
    val packet_prefix =
      "bounded_case16594_cell0_word_atan" ^ Int.toString packet_index;
    val word_fields = List.take (List.drop (runtime_packets,packet_offset),8);
    val object_fields = map interval_object_q_literal word_fields;
    val field_names =
      map (fn suffix => packet_prefix ^ "_" ^ suffix) field_suffixes;
    val field_defs =
      ListPair.map
        (fn (name,tm) => define_literal name tm)
        (field_names,object_fields);
    val _ = List.app cv_trans field_defs;
    val field_constants = map (lhs o concl) field_defs;
    val guard_theorems =
      map (evaluate_guard packet_prefix field_constants) guard_templates;
    val contract_tm = list_mk_comb (atan_contract_constant,field_constants);
    val contract_theorem =
      prove
        (contract_tm,
         simp
           (compute_boundedCase16594ObjectCertifiedAtanDispatchInvariantTheory.bounded_case16594_object_atan_fixed_pure_contract_def::
            guard_theorems));
  in
    save_thm (packet_prefix ^ "_fixed_pure_contract",contract_theorem)
  end;

val additional_atan_contracts =
  ListPair.map prove_atan_packet_contract
    ([1,2,3,4,5,6],List.tl atan_packet_offsets);

val all_atan_contracts =
  compute_boundedCase16594Cell0WordAtan0PureContractTheory.bounded_case16594_cell0_word_atan0_fixed_pure_contract::
  additional_atan_contracts;

fun conjoin_theorems [theorem] = theorem
  | conjoin_theorems (theorem::theorems) =
      CONJ theorem (conjoin_theorems theorems)
  | conjoin_theorems [] = raise Fail "no atan contracts to conjoin";

val bounded_case16594_cell0_word_all_atan_fixed_pure_contracts =
  save_thm
    ("bounded_case16594_cell0_word_all_atan_fixed_pure_contracts",
     conjoin_theorems all_atan_contracts);

val _ = export_theory ();
