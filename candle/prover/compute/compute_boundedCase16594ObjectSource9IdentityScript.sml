(*****************************************************************************
 * Authenticated identity of genuine case-16594 source/code nine.
 *
 * Source nine is extracted as the second element of the complete production
 * suffix after source seven.  No descriptor is copied into the proof fixture.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSource9Identity
Ancestors
  compute_boundedCase16594ObjectSource8Identity
Libs
  bossLib preamble

fun cv_list_elements tm =
  let
    val (head,arguments) = strip_comb tm;
    val constructor = fst (dest_const head)
  in
    case (constructor,arguments) of
      ("Num",[number]) =>
        if aconv number numSyntax.zero_tm then []
        else raise Fail "nonzero authenticated instruction-list terminator"
    | ("Pair",[item,items]) => item :: cv_list_elements items
    | _ => raise Fail "malformed authenticated instruction list"
  end;

fun define_cv_constant name tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,``:cv``),tm));

val after8_sources =
  cv_list_elements
    (rhs
      (concl
        compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_after8_sources_cv_def));
val after8_codes =
  cv_list_elements
    (rhs
      (concl
        compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_after8_codes_cv_def));

val _ =
  if List.length after8_sources = 159 andalso
     List.length after8_codes = 159 then ()
  else raise Fail "unexpected authenticated suffix length at source nine";

val bounded_case16594_object_cell0_source9_cv_def =
  define_cv_constant "bounded_case16594_object_cell0_source9_cv"
    (List.nth (after8_sources,1));
val bounded_case16594_object_cell0_code9_cv_def =
  define_cv_constant "bounded_case16594_object_cell0_code9_cv"
    (List.nth (after8_codes,1));

Theorem bounded_case16594_object_cell0_source9_identity:
  bounded_case16594_object_cell0_source9_cv = Num 7
Proof
  simp [bounded_case16594_object_cell0_source9_cv_def]
QED

Theorem bounded_case16594_object_cell0_code9_identity:
  bounded_case16594_object_cell0_code9_cv = Num 0
Proof
  simp [bounded_case16594_object_cell0_code9_cv_def]
QED

Theorem bounded_case16594_object_source9_decodes:
  bounded_analytic_instruction_of_cv
      bounded_case16594_object_cell0_source9_cv =
    SOME BoundedAnalyticAtan
Proof
  simp
    [bounded_case16594_object_cell0_source9_identity,
     compute_boundedAnalyticProgramCVTheory.bounded_analytic_instruction_of_cv_def]
QED

val _ = export_theory ();

