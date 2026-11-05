(*****************************************************************************
 * Fail-closed contract ledger for the authenticated fixed-word certificate
 * stream and its 134 flat runtime packet fields.
 *
 * The recursive relation is keyed by typed certificates.  It records the
 * exact 5/2/8 field topology, the positive reciprocal branch used by every
 * genuine inverse packet, and the six production guards for every atan
 * packet.  Ordinary analytic instructions consume neither list and are
 * handled later by the joint trace induction.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WordDispatchPacketContracts
Ancestors
  compute_boundedCase16594Cell0WordAtanPureContracts
Libs
  bossLib preamble wordsLib

Definition bounded_case16594_word_dispatch_packet_contracts_def:
  (bounded_case16594_word_dispatch_packet_contracts [] [] = T) /\
  (bounded_case16594_word_dispatch_packet_contracts
      (BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
         center_derivative box_derivative box_second_reciprocal::
       certificate_rest)
      (packet_center_sqrt::packet_box_sqrt::packet_center_derivative::
       packet_box_derivative::packet_box_second_reciprocal::packet_rest) =
    (packet_center_sqrt = center_sqrt /\
     packet_box_sqrt = box_sqrt /\
     packet_center_derivative = center_derivative /\
     packet_box_derivative = box_derivative /\
     packet_box_second_reciprocal = box_second_reciprocal /\
     bounded_case16594_word_dispatch_packet_contracts
       certificate_rest packet_rest)) /\
  (bounded_case16594_word_dispatch_packet_contracts
      (BoundedAnalytic64InverseCertificate center_reciprocal
         box_reciprocal::certificate_rest)
      (packet_center_reciprocal::packet_box_reciprocal::packet_rest) =
    (packet_center_reciprocal = center_reciprocal /\
     packet_box_reciprocal = box_reciprocal /\
     bounded_signed64_strict_positive
       (bounded_interval64_lower packet_center_reciprocal) /\
     bounded_signed64_strict_positive
       (bounded_interval64_lower packet_box_reciprocal) /\
     bounded_case16594_word_dispatch_packet_contracts
       certificate_rest packet_rest)) /\
  (bounded_case16594_word_dispatch_packet_contracts
      (BoundedAnalytic64AtanCertificate lower_reciprocal upper_reciprocal
         center_derivative box_derivative::certificate_rest)
      (center_input::box_input::center_result::center_square::
       packet_center_derivative::box_square::packet_box_derivative::
       box_derivative_square::packet_rest) =
    (packet_center_derivative = center_derivative /\
     packet_box_derivative = box_derivative /\
     bounded_case16594_object_atan_fixed_pure_contract
       (bounded_interval64_object_q_cv center_input)
       (bounded_interval64_object_q_cv box_input)
       (bounded_interval64_object_q_cv center_result)
       (bounded_interval64_object_q_cv center_square)
       (bounded_interval64_object_q_cv packet_center_derivative)
       (bounded_interval64_object_q_cv box_square)
       (bounded_interval64_object_q_cv packet_box_derivative)
       (bounded_interval64_object_q_cv box_derivative_square) /\
     bounded_case16594_word_dispatch_packet_contracts
       certificate_rest packet_rest)) /\
  (bounded_case16594_word_dispatch_packet_contracts _ _ = F)
End

val atan_field_suffixes =
  ["center_input_cv", "box_input_cv", "center_result_cv",
   "center_square_cv", "center_derivative_cv", "box_square_cv",
   "box_derivative_cv", "box_derivative_square_cv"];

fun atan_field_definition packet_index suffix =
  let
    val packet_name =
      "bounded_case16594_cell0_word_atan" ^ Int.toString packet_index ^
      "_" ^ suffix ^ "_def";
    val theory_name =
      if packet_index = 0 then
        "compute_boundedCase16594Cell0WordAtan0PureContract"
      else
        "compute_boundedCase16594Cell0WordAtanPureContracts";
  in
    DB.fetch theory_name packet_name
  end;

val all_atan_field_definitions =
  List.concat
    (List.tabulate
      (7,fn packet_index =>
        map (atan_field_definition packet_index) atan_field_suffixes));

(* Convert exactly the 56 authenticated atan packet fields to the named
   object-q constants used by the already checked guard contracts.  Several
   genuine fields happen to have identical values, so simplification may
   choose an earlier name for such a value.  The final contracts are therefore
   also normalized to their literal object-q values below. *)
val runtime_packets_tm =
  rhs
    (concl
      compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_packets_def);
val (runtime_packets,_) = listSyntax.dest_list runtime_packets_tm;
val atan_packet_offsets = [7,31,46,70,85,109,124];
val atan_word_fields =
  List.concat
    (map
      (fn offset => List.take (List.drop (runtime_packets,offset),8))
      atan_packet_offsets);
val interval_to_object_q =
  prim_mk_const
    {Name="bounded_interval64_object_q_cv",
     Thy="compute_boundedAnalyticObjectCertificateRefinement"};
fun field_conversion_identity (word_field,field_definition) =
  TRANS
    (EVAL (mk_comb (interval_to_object_q,word_field)))
    (SYM field_definition);
val all_atan_field_conversion_identities =
  ListPair.map field_conversion_identity
    (atan_word_fields,all_atan_field_definitions);

val all_atan_contract_theorems =
  CONJUNCTS
    compute_boundedCase16594Cell0WordAtanPureContractsTheory.bounded_case16594_cell0_word_all_atan_fixed_pure_contracts;
val all_atan_concrete_contracts =
  map
    (REWRITE_RULE all_atan_field_definitions)
    all_atan_contract_theorems;

Theorem bounded_case16594_cell0_word_dispatch_packet_contracts:
  bounded_case16594_word_dispatch_packet_contracts
    bounded_case16594_cell0_source_word_certificates
    bounded_case16594_cell0_authenticated_word_runtime_packets
Proof
  simp
    ([bounded_case16594_word_dispatch_packet_contracts_def,
      compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_certificates_def,
      compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_packets_def,
      compute_boundedIntervalTheory.bounded_interval64_lower_def,
      compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
      compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
      compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
      compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def] @
     all_atan_field_conversion_identities)
  >> simp all_atan_field_definitions
  >> simp all_atan_concrete_contracts
QED

val _ = export_theory ();
