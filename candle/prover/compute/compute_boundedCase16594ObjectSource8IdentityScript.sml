(*****************************************************************************
 * Authenticated identity of genuine case-16594 source/code eight.
 *
 * The values are extracted from the suffix of the complete production
 * payload, rather than copied into a fixture.  This is the first instruction
 * beyond the previously authenticated prefix-eight inventory.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSource8Identity
Ancestors
  compute_boundedCase16594ObjectPrefix8Identity
Libs
  bossLib preamble

fun cv_pair_components tm =
  let
    val (head,arguments) = strip_comb tm;
    val constructor = fst (dest_const head)
  in
    case (constructor,arguments) of
      ("Pair",[left,right]) => (left,right)
    | _ => raise Fail "empty authenticated source-8 suffix"
  end;

fun define_cv_constant name tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,``:cv``),tm));

val after8_sources_tm =
  rhs
    (concl
      compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_after8_sources_cv_def);
val after8_codes_tm =
  rhs
    (concl
      compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_after8_codes_cv_def);

val (source8_tm,_) = cv_pair_components after8_sources_tm;
val (code8_tm,_) = cv_pair_components after8_codes_tm;

val bounded_case16594_object_cell0_source8_cv_def =
  define_cv_constant "bounded_case16594_object_cell0_source8_cv" source8_tm;
val bounded_case16594_object_cell0_code8_cv_def =
  define_cv_constant "bounded_case16594_object_cell0_code8_cv" code8_tm;

Theorem bounded_case16594_object_cell0_source8_identity:
  bounded_case16594_object_cell0_source8_cv = Num 4
Proof
  simp [bounded_case16594_object_cell0_source8_cv_def]
QED

Theorem bounded_case16594_object_cell0_code8_identity:
  bounded_case16594_object_cell0_code8_cv = Num 0
Proof
  simp [bounded_case16594_object_cell0_code8_cv_def]
QED

Theorem bounded_case16594_object_source8_decodes:
  bounded_analytic_instruction_of_cv
      bounded_case16594_object_cell0_source8_cv =
    SOME BoundedAnalyticMul
Proof
  simp
    [bounded_case16594_object_cell0_source8_identity,
     compute_boundedAnalyticProgramCVTheory.bounded_analytic_instruction_of_cv_def]
QED

val _ = export_theory ();
