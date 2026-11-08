(*****************************************************************************
 * Exact proof-producing evaluation of the genuine cell-0 object prefix 0--7.
 *
 * The prefix and its suffix witnesses are extracted mechanically from the
 * six arguments of the authenticated complete entry.  The HOL split
 * theorems below therefore connect this bounded computation to the complete
 * production payload rather than to a separately copied instruction fixture.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchPrefix8Eval
Ancestors
  compute_boundedCase16594FirstInverseStateEval
Libs
  bossLib preamble cv_transLib

val full_entry_tm =
  rhs
    (concl
      compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_cexp_def);

val (_,full_entry_constructor_arguments) = strip_comb full_entry_tm;
val [full_entry_name_tm,full_entry_arguments_tm] =
  full_entry_constructor_arguments;
val (full_entry_arguments,_) =
  listSyntax.dest_list full_entry_arguments_tm;

val [center_boxes_exp_tm,outer_boxes_exp_tm,radii_exp_tm,codes_exp_tm,
     sources_exp_tm,certificates_exp_tm] = full_entry_arguments;

val compute_exec_cv_num_tm =
  prim_mk_const {Name="Num",Thy="compute_exec"};
val compute_exec_cv_pair_tm =
  prim_mk_const {Name="Pair",Thy="compute_exec"};

fun mk_compute_exec_cv_num number =
  mk_comb (compute_exec_cv_num_tm,number);

fun mk_compute_exec_cv_pair (left,right) =
  mk_comb (mk_comb (compute_exec_cv_pair_tm,left),right);

fun compute_exp_value_to_cv tm =
  let
    val (head,arguments) = strip_comb tm
    val constructor = fst (dest_const head)
  in
    case (constructor,arguments) of
      ("Num",[number]) => mk_compute_exec_cv_num number
    | ("Pair",[left,right]) =>
        mk_compute_exec_cv_pair
          (compute_exp_value_to_cv left,compute_exp_value_to_cv right)
    | _ => raise Fail "non-value in authenticated object-dispatch entry"
  end;

val cv_zero_tm = mk_compute_exec_cv_num numSyntax.zero_tm;

fun cv_list_take 0 _ = cv_zero_tm
  | cv_list_take count tm =
      let
        val (head,arguments) = strip_comb tm
        val constructor = fst (dest_const head)
      in
        case (constructor,arguments) of
          ("Pair",[item,items]) =>
            mk_compute_exec_cv_pair
              (item,cv_list_take (count - 1) items)
        | _ => raise Fail "short authenticated object-dispatch list"
      end;

fun cv_list_drop 0 tm = tm
  | cv_list_drop count tm =
      let
        val (head,arguments) = strip_comb tm
        val constructor = fst (dest_const head)
      in
        case (constructor,arguments) of
          ("Pair",[_,items]) => cv_list_drop (count - 1) items
        | _ => raise Fail "short authenticated object-dispatch list"
      end;

fun define_cv_constant name tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,``:cv``),tm));

val center_boxes_cv_tm = compute_exp_value_to_cv center_boxes_exp_tm;
val outer_boxes_cv_tm = compute_exp_value_to_cv outer_boxes_exp_tm;
val radii_cv_tm = compute_exp_value_to_cv radii_exp_tm;
val full_codes_cv_tm = compute_exp_value_to_cv codes_exp_tm;
val full_sources_cv_tm = compute_exp_value_to_cv sources_exp_tm;
val full_certificates_cv_tm =
  compute_exp_value_to_cv certificates_exp_tm;
val prefix8_codes_cv_tm = cv_list_take 8 full_codes_cv_tm;
val after8_codes_cv_tm = cv_list_drop 8 full_codes_cv_tm;
val prefix8_sources_cv_tm = cv_list_take 8 full_sources_cv_tm;
val after8_sources_cv_tm = cv_list_drop 8 full_sources_cv_tm;

fun cv_pair_components tm =
  let
    val (head,arguments) = strip_comb tm
    val constructor = fst (dest_const head)
  in
    case (constructor,arguments) of
      ("Pair",[left,right]) => (left,right)
    | _ => raise Fail "expected pair in authenticated object-dispatch list"
  end;

val (code0_cv_tm,_) = cv_pair_components prefix8_codes_cv_tm;
val (source0_cv_tm,_) = cv_pair_components prefix8_sources_cv_tm;

val bounded_case16594_object_cell0_center_boxes_cv_def =
  define_cv_constant
    "bounded_case16594_object_cell0_center_boxes_cv" center_boxes_cv_tm;
val bounded_case16594_object_cell0_outer_boxes_cv_def =
  define_cv_constant
    "bounded_case16594_object_cell0_outer_boxes_cv" outer_boxes_cv_tm;
val bounded_case16594_object_cell0_radii_cv_def =
  define_cv_constant
    "bounded_case16594_object_cell0_radii_cv" radii_cv_tm;
val bounded_case16594_object_cell0_full_codes_cv_def =
  define_cv_constant
    "bounded_case16594_object_cell0_full_codes_cv" full_codes_cv_tm;
val bounded_case16594_object_cell0_full_sources_cv_def =
  define_cv_constant
    "bounded_case16594_object_cell0_full_sources_cv" full_sources_cv_tm;
val bounded_case16594_object_cell0_full_certificates_cv_def =
  define_cv_constant
    "bounded_case16594_object_cell0_full_certificates_cv"
    full_certificates_cv_tm;
val bounded_case16594_object_cell0_prefix8_codes_cv_def =
  define_cv_constant
    "bounded_case16594_object_cell0_prefix8_codes_cv" prefix8_codes_cv_tm;
val bounded_case16594_object_cell0_after8_codes_cv_def =
  define_cv_constant
    "bounded_case16594_object_cell0_after8_codes_cv" after8_codes_cv_tm;
val bounded_case16594_object_cell0_prefix8_sources_cv_def =
  define_cv_constant
    "bounded_case16594_object_cell0_prefix8_sources_cv" prefix8_sources_cv_tm;
val bounded_case16594_object_cell0_after8_sources_cv_def =
  define_cv_constant
    "bounded_case16594_object_cell0_after8_sources_cv" after8_sources_cv_tm;
val bounded_case16594_object_cell0_code0_cv_def =
  define_cv_constant
    "bounded_case16594_object_cell0_code0_cv" code0_cv_tm;
val bounded_case16594_object_cell0_source0_cv_def =
  define_cv_constant
    "bounded_case16594_object_cell0_source0_cv" source0_cv_tm;

Definition bounded_case16594_object_cv_list_append_def:
  bounded_case16594_object_cv_list_append (Num nil) right = right /\
  bounded_case16594_object_cv_list_append (Pair item items) right =
    Pair item (bounded_case16594_object_cv_list_append items right)
End

Theorem bounded_case16594_object_cell0_codes_prefix8_split:
  bounded_case16594_object_cell0_full_codes_cv =
    bounded_case16594_object_cv_list_append
      bounded_case16594_object_cell0_prefix8_codes_cv
      bounded_case16594_object_cell0_after8_codes_cv
Proof
  simp
    [bounded_case16594_object_cell0_full_codes_cv_def,
     bounded_case16594_object_cell0_prefix8_codes_cv_def,
     bounded_case16594_object_cell0_after8_codes_cv_def,
     bounded_case16594_object_cv_list_append_def]
QED

Theorem bounded_case16594_object_cell0_sources_prefix8_split:
  bounded_case16594_object_cell0_full_sources_cv =
    bounded_case16594_object_cv_list_append
      bounded_case16594_object_cell0_prefix8_sources_cv
      bounded_case16594_object_cell0_after8_sources_cv
Proof
  simp
    [bounded_case16594_object_cell0_full_sources_cv_def,
     bounded_case16594_object_cell0_prefix8_sources_cv_def,
     bounded_case16594_object_cell0_after8_sources_cv_def,
     bounded_case16594_object_cv_list_append_def]
QED

Theorem bounded_case16594_object_cell0_entry_payload_identity:
  bounded_case16594_object_dispatch_cell0_cexp =
    App «candle_cv_q_packed_object_dispatch_entry»
      [from_cv bounded_case16594_object_cell0_center_boxes_cv;
       from_cv bounded_case16594_object_cell0_outer_boxes_cv;
       from_cv bounded_case16594_object_cell0_radii_cv;
       from_cv bounded_case16594_object_cell0_full_codes_cv;
       from_cv bounded_case16594_object_cell0_full_sources_cv;
       from_cv bounded_case16594_object_cell0_full_certificates_cv]
Proof
  simp
    [compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_cexp_def,
     bounded_case16594_object_cell0_center_boxes_cv_def,
     bounded_case16594_object_cell0_outer_boxes_cv_def,
     bounded_case16594_object_cell0_radii_cv_def,
     bounded_case16594_object_cell0_full_codes_cv_def,
     bounded_case16594_object_cell0_full_sources_cv_def,
     bounded_case16594_object_cell0_full_certificates_cv_def,
     compute_execTheory.from_cv_def]
QED

Definition bounded_case16594_object_cell0_prefix8_cexp_def:
  bounded_case16594_object_cell0_prefix8_cexp =
    App «candle_cv_q_packed_object_dispatch_program»
      [from_cv bounded_case16594_object_cell0_center_boxes_cv;
       from_cv bounded_case16594_object_cell0_outer_boxes_cv;
       from_cv bounded_case16594_object_cell0_radii_cv;
       from_cv bounded_case16594_object_cell0_prefix8_codes_cv;
       from_cv bounded_case16594_object_cell0_prefix8_sources_cv;
       from_cv bounded_case16594_object_cell0_full_certificates_cv;
       from_cv (Num 0)]
End

val _ = export_theory ();
