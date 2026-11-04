(*****************************************************************************
 * Authenticated exact-rational certificates for the first genuine inverse.
 *
 * The two interval records and remaining stream are split mechanically from
 * the already authenticated post-sqrt production payload.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectInverseCertificateIdentity
Ancestors
  compute_boundedCase16594ObjectSqrtCertificateIdentity
Libs
  bossLib preamble intLib

val after_sqrt_certificates_tm =
  rhs
    (concl
      compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_after_sqrt_certificates_cv_def);

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

val certificate_elements = cv_list_elements after_sqrt_certificates_tm;

val _ =
  if List.length certificate_elements = 129 then ()
  else raise Fail "unexpected authenticated post-sqrt certificate count";

val [center_reciprocal_tm,box_reciprocal_tm] =
  List.take (certificate_elements,2);
val certificate_rest_elements = List.drop (certificate_elements,2);

val cv_num_tm = prim_mk_const {Name="Num",Thy="compute_exec"};
val cv_pair_tm = prim_mk_const {Name="Pair",Thy="compute_exec"};
val cv_nil_tm = mk_comb (cv_num_tm,numSyntax.zero_tm);

fun cv_list_tm [] = cv_nil_tm
  | cv_list_tm (item::items) =
      mk_comb (mk_comb (cv_pair_tm,item),cv_list_tm items);

fun define_cv name tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,``:cv``),tm));

val bounded_case16594_object_cell0_inverse_center_reciprocal_cv_def =
  define_cv "bounded_case16594_object_cell0_inverse_center_reciprocal_cv"
    center_reciprocal_tm;
val bounded_case16594_object_cell0_inverse_box_reciprocal_cv_def =
  define_cv "bounded_case16594_object_cell0_inverse_box_reciprocal_cv"
    box_reciprocal_tm;
val bounded_case16594_object_cell0_after_inverse_certificates_cv_def =
  define_cv "bounded_case16594_object_cell0_after_inverse_certificates_cv"
    (cv_list_tm certificate_rest_elements);

Theorem bounded_case16594_object_cell0_inverse_reciprocals_identical:
  bounded_case16594_object_cell0_inverse_box_reciprocal_cv =
    bounded_case16594_object_cell0_inverse_center_reciprocal_cv
Proof
  simp
    [bounded_case16594_object_cell0_inverse_box_reciprocal_cv_def,
     bounded_case16594_object_cell0_inverse_center_reciprocal_cv_def]
QED

Theorem bounded_case16594_object_cell0_certificates_inverse_split:
  bounded_case16594_object_cell0_after_sqrt_certificates_cv =
    Pair bounded_case16594_object_cell0_inverse_center_reciprocal_cv
      (Pair bounded_case16594_object_cell0_inverse_box_reciprocal_cv
        bounded_case16594_object_cell0_after_inverse_certificates_cv)
Proof
  simp
    [compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_after_sqrt_certificates_cv_def,
     bounded_case16594_object_cell0_inverse_center_reciprocal_cv_def,
     bounded_case16594_object_cell0_inverse_box_reciprocal_cv_def,
     bounded_case16594_object_cell0_after_inverse_certificates_cv_def]
QED

val _ = export_theory ();
