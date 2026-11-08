(*****************************************************************************
 * Authenticated exact-rational certificates for the first genuine sqrt.
 *
 * The five interval records and the remaining certificate stream are split
 * mechanically from the complete production payload.  No scale conversion
 * or separately copied fixture is used: the resulting closed contract is
 * stated directly over the exact object-q source-5 Taylor result.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSqrtCertificateIdentity
Ancestors
  compute_boundedCase16594ObjectPrefixPolynomialInvariant
  compute_boundedAnalyticObjectSqrtRefinement
  compute_boundedAnalyticObjectReciprocalRefinement
Libs
  bossLib preamble intLib

val full_certificates_tm =
  rhs
    (concl
      compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_full_certificates_cv_def);

fun cv_list_elements tm =
  let
    val (head,arguments) = strip_comb tm;
    val constructor = fst (dest_const head)
  in
    case (constructor,arguments) of
      ("Num",[number]) =>
        if aconv number numSyntax.zero_tm then []
        else raise Fail "nonzero authenticated certificate-list terminator"
    | ("Pair",[item,items]) => item :: cv_list_elements items
    | _ => raise Fail "malformed authenticated certificate list"
  end;

val certificate_elements = cv_list_elements full_certificates_tm;

val _ =
  if List.length certificate_elements = 134 then ()
  else raise Fail "unexpected authenticated certificate count";

val [center_root_tm,box_root_tm,center_derivative_tm,box_derivative_tm,
     box_second_reciprocal_tm] = List.take (certificate_elements,5);
val certificate_rest_elements = List.drop (certificate_elements,5);

val cv_num_tm = prim_mk_const {Name="Num",Thy="compute_exec"};
val cv_pair_tm = prim_mk_const {Name="Pair",Thy="compute_exec"};
val cv_nil_tm = mk_comb (cv_num_tm,numSyntax.zero_tm);

fun cv_list_tm [] = cv_nil_tm
  | cv_list_tm (item::items) =
      mk_comb (mk_comb (cv_pair_tm,item),cv_list_tm items);

fun define_cv name tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,``:cv``),tm));

val bounded_case16594_object_cell0_sqrt_center_root_cv_def =
  define_cv "bounded_case16594_object_cell0_sqrt_center_root_cv"
    center_root_tm;
val bounded_case16594_object_cell0_sqrt_box_root_cv_def =
  define_cv "bounded_case16594_object_cell0_sqrt_box_root_cv"
    box_root_tm;
val bounded_case16594_object_cell0_sqrt_center_derivative_cv_def =
  define_cv "bounded_case16594_object_cell0_sqrt_center_derivative_cv"
    center_derivative_tm;
val bounded_case16594_object_cell0_sqrt_box_derivative_cv_def =
  define_cv "bounded_case16594_object_cell0_sqrt_box_derivative_cv"
    box_derivative_tm;
val bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv_def =
  define_cv "bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv"
    box_second_reciprocal_tm;
val bounded_case16594_object_cell0_after_sqrt_certificates_cv_def =
  define_cv "bounded_case16594_object_cell0_after_sqrt_certificates_cv"
    (cv_list_tm certificate_rest_elements);

Theorem bounded_case16594_object_cell0_certificates_sqrt_split:
  bounded_case16594_object_cell0_full_certificates_cv =
    Pair bounded_case16594_object_cell0_sqrt_center_root_cv
      (Pair bounded_case16594_object_cell0_sqrt_box_root_cv
        (Pair bounded_case16594_object_cell0_sqrt_center_derivative_cv
          (Pair bounded_case16594_object_cell0_sqrt_box_derivative_cv
            (Pair
              bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv
              bounded_case16594_object_cell0_after_sqrt_certificates_cv))))
Proof
  simp
    [compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_full_certificates_cv_def,
     bounded_case16594_object_cell0_sqrt_center_root_cv_def,
     bounded_case16594_object_cell0_sqrt_box_root_cv_def,
     bounded_case16594_object_cell0_sqrt_center_derivative_cv_def,
     bounded_case16594_object_cell0_sqrt_box_derivative_cv_def,
     bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv_def,
     bounded_case16594_object_cell0_after_sqrt_certificates_cv_def]
QED

val _ = export_theory ();
