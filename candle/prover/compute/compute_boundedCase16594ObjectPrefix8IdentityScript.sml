(*****************************************************************************
 * Authenticated instruction inventory for the genuine cell-0 prefix eight.
 *
 * Raw source descriptors are extracted from the production payload at
 * theory-construction time.  The compact semantic programs below are then
 * checked against the shared fail-closed decoder.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPrefix8Identity
Ancestors
  compute_boundedCase16594ObjectFirstPolyDispatchBridge
  compute_boundedAnalyticProgramCV
Libs
  bossLib preamble

fun authenticated_cv_list_elements tm =
  let
    val (head,arguments) = strip_comb tm;
    val constructor = fst (dest_const head)
  in
    case (constructor,arguments) of
      ("Num",[number]) =>
        if aconv number numSyntax.zero_tm then []
        else raise Fail "nonzero authenticated list terminator"
    | ("Pair",[item,items]) =>
        item :: authenticated_cv_list_elements items
    | _ => raise Fail "non-list authenticated prefix payload"
  end;

val prefix8_sources =
  authenticated_cv_list_elements
    (rhs
      (concl
        compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_prefix8_sources_cv_def));

val _ =
  if List.length prefix8_sources = 8 then ()
  else raise Fail "authenticated prefix does not contain eight sources";

fun define_source index =
  let
    val name =
      "bounded_case16594_object_cell0_source" ^ Int.toString index ^ "_cv";
  in
    new_definition
      (name ^ "_def",
       mk_eq (mk_var (name,``:cv``),List.nth (prefix8_sources,index)))
  end;

val bounded_case16594_object_cell0_source1_cv_def = define_source 1;
val bounded_case16594_object_cell0_source2_cv_def = define_source 2;
val bounded_case16594_object_cell0_source3_cv_def = define_source 3;
val bounded_case16594_object_cell0_source4_cv_def = define_source 4;
val bounded_case16594_object_cell0_source5_cv_def = define_source 5;
val bounded_case16594_object_cell0_source6_cv_def = define_source 6;
val bounded_case16594_object_cell0_source7_cv_def = define_source 7;

Definition bounded_case16594_object_source1_poly_program_def:
  bounded_case16594_object_source1_poly_program =
    [BoundedPolyConstant 1 0 0]
End

Definition bounded_case16594_object_source2_poly_program_def:
  bounded_case16594_object_source2_poly_program =
    [BoundedPolyConstant 3 0 0]
End

Definition bounded_case16594_object_source4_poly_program_def:
  bounded_case16594_object_source4_poly_program =
    [BoundedPolyConstant 1 0 2]
End

Definition bounded_case16594_object_source5_poly_program_def:
  bounded_case16594_object_source5_poly_program =
    [BoundedPolyConstant 1 0 0;
     BoundedPolyConstant 1 0 2;
     BoundedPolySquare;
     BoundedPolyNeg;
     BoundedPolyAdd]
End

Theorem bounded_case16594_object_cell0_prefix8_sources_identity:
  bounded_case16594_object_cell0_prefix8_sources_cv =
    bounded_object_q_cv_list
      [bounded_case16594_object_cell0_source0_cv;
       bounded_case16594_object_cell0_source1_cv;
       bounded_case16594_object_cell0_source2_cv;
       bounded_case16594_object_cell0_source3_cv;
       bounded_case16594_object_cell0_source4_cv;
       bounded_case16594_object_cell0_source5_cv;
       bounded_case16594_object_cell0_source6_cv;
       bounded_case16594_object_cell0_source7_cv]
Proof
  simp
    [compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_prefix8_sources_cv_def,
     compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_source0_cv_def,
     bounded_case16594_object_cell0_source1_cv_def,
     bounded_case16594_object_cell0_source2_cv_def,
     bounded_case16594_object_cell0_source3_cv_def,
     bounded_case16594_object_cell0_source4_cv_def,
     bounded_case16594_object_cell0_source5_cv_def,
     bounded_case16594_object_cell0_source6_cv_def,
     bounded_case16594_object_cell0_source7_cv_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

Theorem bounded_case16594_object_cell0_prefix8_codes_identity:
  bounded_case16594_object_cell0_prefix8_codes_cv =
    bounded_object_q_cv_list
      [Num 0;Num 0;Num 0;Num 0;Num 0;Num 0;Num 0;Num 0]
Proof
  simp
    [compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_prefix8_codes_cv_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

Theorem bounded_case16594_object_source1_decodes:
  bounded_analytic_instruction_of_cv
      bounded_case16594_object_cell0_source1_cv =
    SOME
      (BoundedAnalyticPolynomial
        bounded_case16594_object_source1_poly_program)
Proof
  simp
    [bounded_case16594_object_cell0_source1_cv_def,
     bounded_case16594_object_source1_poly_program_def,
     bounded_analytic_instruction_of_cv_def,
     bounded_poly_program_of_cv_def,
     bounded_poly_instruction_of_cv_def,
     bounded_rational_of_cv_def]
QED

Theorem bounded_case16594_object_source2_decodes:
  bounded_analytic_instruction_of_cv
      bounded_case16594_object_cell0_source2_cv =
    SOME
      (BoundedAnalyticPolynomial
        bounded_case16594_object_source2_poly_program)
Proof
  simp
    [bounded_case16594_object_cell0_source2_cv_def,
     bounded_case16594_object_source2_poly_program_def,
     bounded_analytic_instruction_of_cv_def,
     bounded_poly_program_of_cv_def,
     bounded_poly_instruction_of_cv_def,
     bounded_rational_of_cv_def]
QED

Theorem bounded_case16594_object_source3_decodes:
  bounded_analytic_instruction_of_cv
      bounded_case16594_object_cell0_source3_cv =
    SOME BoundedAnalyticPiHalf
Proof
  simp
    [bounded_case16594_object_cell0_source3_cv_def,
     bounded_analytic_instruction_of_cv_def]
QED

Theorem bounded_case16594_object_source4_decodes:
  bounded_analytic_instruction_of_cv
      bounded_case16594_object_cell0_source4_cv =
    SOME
      (BoundedAnalyticPolynomial
        bounded_case16594_object_source4_poly_program)
Proof
  simp
    [bounded_case16594_object_cell0_source4_cv_def,
     bounded_case16594_object_source4_poly_program_def,
     bounded_analytic_instruction_of_cv_def,
     bounded_poly_program_of_cv_def,
     bounded_poly_instruction_of_cv_def,
     bounded_rational_of_cv_def]
QED

Theorem bounded_case16594_object_source5_decodes:
  bounded_analytic_instruction_of_cv
      bounded_case16594_object_cell0_source5_cv =
    SOME
      (BoundedAnalyticPolynomial
        bounded_case16594_object_source5_poly_program)
Proof
  simp
    [bounded_case16594_object_cell0_source5_cv_def,
     bounded_case16594_object_source5_poly_program_def,
     bounded_analytic_instruction_of_cv_def,
     bounded_poly_program_of_cv_def,
     bounded_poly_instruction_of_cv_def,
     bounded_rational_of_cv_def]
QED

Theorem bounded_case16594_object_source6_decodes:
  bounded_analytic_instruction_of_cv
      bounded_case16594_object_cell0_source6_cv =
    SOME BoundedAnalyticSqrt
Proof
  simp
    [bounded_case16594_object_cell0_source6_cv_def,
     bounded_analytic_instruction_of_cv_def,
     bounded_sqrt_placeholder_cv_def]
QED

Theorem bounded_case16594_object_source7_decodes:
  bounded_analytic_instruction_of_cv
      bounded_case16594_object_cell0_source7_cv =
    SOME BoundedAnalyticInverse
Proof
  simp
    [bounded_case16594_object_cell0_source7_cv_def,
     bounded_analytic_instruction_of_cv_def]
QED

val _ = export_theory ();
