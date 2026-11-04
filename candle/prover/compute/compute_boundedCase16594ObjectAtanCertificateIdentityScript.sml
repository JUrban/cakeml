(*****************************************************************************
 * Authenticated certificate packet for the first genuine atan instruction.
 *
 * Eight interval records and the remaining stream are split mechanically from
 * the authenticated post-inverse production payload.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAtanCertificateIdentity
Ancestors
  compute_boundedCase16594ObjectSource9Identity
  compute_boundedCase16594ObjectInverseCertificateIdentity
Libs
  bossLib preamble

val after_inverse_certificates_tm =
  rhs
    (concl
      compute_boundedCase16594ObjectInverseCertificateIdentityTheory.bounded_case16594_object_cell0_after_inverse_certificates_cv_def);

fun cv_list_elements tm =
  let
    val (head,arguments) = strip_comb tm;
    val constructor = fst (dest_const head)
  in
    case (constructor,arguments) of
      ("Num",[number]) =>
        if aconv number numSyntax.zero_tm then []
        else raise Fail "nonzero authenticated atan-certificate terminator"
    | ("Pair",[item,items]) => item :: cv_list_elements items
    | _ => raise Fail "malformed authenticated atan certificate list"
  end;

val certificate_elements = cv_list_elements after_inverse_certificates_tm;

val _ =
  if List.length certificate_elements = 127 then ()
  else raise Fail "unexpected authenticated post-inverse certificate count";

val [center_input_tm,box_input_tm,center_result_tm,center_square_tm,
     center_derivative_tm,box_square_tm,box_derivative_tm,
     box_derivative_square_tm] =
  List.take (certificate_elements,8);
val certificate_rest_elements = List.drop (certificate_elements,8);

val cv_num_tm = prim_mk_const {Name="Num",Thy="compute_exec"};
val cv_pair_tm = prim_mk_const {Name="Pair",Thy="compute_exec"};
val cv_nil_tm = mk_comb (cv_num_tm,numSyntax.zero_tm);

fun cv_list_tm [] = cv_nil_tm
  | cv_list_tm (item::items) =
      mk_comb (mk_comb (cv_pair_tm,item),cv_list_tm items);

fun define_cv name tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,``:cv``),tm));

val bounded_case16594_object_cell0_atan_center_input_cv_def =
  define_cv "bounded_case16594_object_cell0_atan_center_input_cv"
    center_input_tm;
val bounded_case16594_object_cell0_atan_box_input_cv_def =
  define_cv "bounded_case16594_object_cell0_atan_box_input_cv"
    box_input_tm;
val bounded_case16594_object_cell0_atan_center_result_cv_def =
  define_cv "bounded_case16594_object_cell0_atan_center_result_cv"
    center_result_tm;
val bounded_case16594_object_cell0_atan_center_square_cv_def =
  define_cv "bounded_case16594_object_cell0_atan_center_square_cv"
    center_square_tm;
val bounded_case16594_object_cell0_atan_center_derivative_cv_def =
  define_cv "bounded_case16594_object_cell0_atan_center_derivative_cv"
    center_derivative_tm;
val bounded_case16594_object_cell0_atan_box_square_cv_def =
  define_cv "bounded_case16594_object_cell0_atan_box_square_cv"
    box_square_tm;
val bounded_case16594_object_cell0_atan_box_derivative_cv_def =
  define_cv "bounded_case16594_object_cell0_atan_box_derivative_cv"
    box_derivative_tm;
val bounded_case16594_object_cell0_atan_box_derivative_square_cv_def =
  define_cv "bounded_case16594_object_cell0_atan_box_derivative_square_cv"
    box_derivative_square_tm;
val bounded_case16594_object_cell0_after_atan_certificates_cv_def =
  define_cv "bounded_case16594_object_cell0_after_atan_certificates_cv"
    (cv_list_tm certificate_rest_elements);

Theorem bounded_case16594_object_cell0_certificates_atan_split:
  bounded_case16594_object_cell0_after_inverse_certificates_cv =
    Pair bounded_case16594_object_cell0_atan_center_input_cv
      (Pair bounded_case16594_object_cell0_atan_box_input_cv
        (Pair bounded_case16594_object_cell0_atan_center_result_cv
          (Pair bounded_case16594_object_cell0_atan_center_square_cv
            (Pair bounded_case16594_object_cell0_atan_center_derivative_cv
              (Pair bounded_case16594_object_cell0_atan_box_square_cv
                (Pair bounded_case16594_object_cell0_atan_box_derivative_cv
                  (Pair
                    bounded_case16594_object_cell0_atan_box_derivative_square_cv
                    bounded_case16594_object_cell0_after_atan_certificates_cv)))))))
Proof
  simp
    [compute_boundedCase16594ObjectInverseCertificateIdentityTheory.bounded_case16594_object_cell0_after_inverse_certificates_cv_def,
     bounded_case16594_object_cell0_atan_center_input_cv_def,
     bounded_case16594_object_cell0_atan_box_input_cv_def,
     bounded_case16594_object_cell0_atan_center_result_cv_def,
     bounded_case16594_object_cell0_atan_center_square_cv_def,
     bounded_case16594_object_cell0_atan_center_derivative_cv_def,
     bounded_case16594_object_cell0_atan_box_square_cv_def,
     bounded_case16594_object_cell0_atan_box_derivative_cv_def,
     bounded_case16594_object_cell0_atan_box_derivative_square_cv_def,
     bounded_case16594_object_cell0_after_atan_certificates_cv_def]
QED

val _ = export_theory ();

