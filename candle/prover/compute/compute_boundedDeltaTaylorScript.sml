(*****************************************************************************
 * Direct compact Taylor evaluators for the two authenticated delta families.
 *
 * These functions implement the shared numerical identities used by the six
 * pinned case16594 specialization roles.  They are independent of instruction
 * positions: the enclosing plan compiler remains responsible for proving an
 * exact source-program/role match before dispatching here.
 *****************************************************************************)
Theory compute_boundedDeltaTaylor
Ancestors
  compute_boundedTaylorBase compute_boundedDeltaSpecialization
Libs
  bossLib preamble

Definition bounded_interval64_sum_aux_def:
  bounded_interval64_sum_aux [] accumulator = SOME accumulator ∧
  bounded_interval64_sum_aux (value::rest) accumulator =
    case bounded_interval64_add accumulator value of
    | NONE => NONE
    | SOME next => bounded_interval64_sum_aux rest next
End

Definition bounded_interval64_sum_def:
  bounded_interval64_sum values =
    bounded_interval64_sum_aux values bounded_interval64_zero
End

Definition bounded_interval64_scale4_def:
  bounded_interval64_scale4 value =
    case bounded_interval64_add value value of
    | NONE => NONE
    | SOME twice => bounded_interval64_add twice twice
End

Definition bounded_interval64_list_scale4_def:
  bounded_interval64_list_scale4 [] = SOME [] ∧
  bounded_interval64_list_scale4 (value::rest) =
    case bounded_interval64_scale4 value of
    | NONE => NONE
    | SOME scaled =>
      case bounded_interval64_list_scale4 rest of
      | NONE => NONE
      | SOME scaled_rest => SOME (scaled::scaled_rest)
End

Definition bounded_interval64_mul3_def:
  bounded_interval64_mul3 first second third =
    case bounded_interval64_mul first second of
    | NONE => NONE
    | SOME product => bounded_interval64_mul product third
End

Definition bounded_interval64_sums_def:
  bounded_interval64_sums [] = SOME [] ∧
  bounded_interval64_sums (values::rest) =
    case bounded_interval64_sum values of
    | NONE => NONE
    | SOME value =>
      case bounded_interval64_sums rest of
      | NONE => NONE
      | SOME values_rest => SOME (value::values_rest)
End

Definition bounded_delta64_pair_products_def:
  bounded_delta64_pair_products environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      bounded_interval64_list_pairwise_mul
        [x0;x0;x0;x0;x0;x0;
         x1;x1;x1;x1;x1;
         x2;x2;x2;x2;
         x3;x3;x3;
         x4;x4;
         x5]
        [x0;x1;x2;x3;x4;x5;
         x1;x2;x3;x4;x5;
         x2;x3;x4;x5;
         x3;x4;x5;
         x4;x5;
         x5]
    | _ => NONE
End

Definition bounded_delta64_gradient_component_from_products_def:
  bounded_delta64_gradient_component_from_products (coordinate:num) products =
    case products of
    | p00::p01::p02::p03::p04::p05::
      p11::p12::p13::p14::p15::
      p22::p23::p24::p25::
      p33::p34::p35::
      p44::p45::
      p55::[] =>
      if coordinate = 0 then
        bounded_interval64_sum
          [bounded_interval64_neg p03; bounded_interval64_neg p03;
           p13;p14;bounded_interval64_neg p15;p23;
           bounded_interval64_neg p24;p25;
           bounded_interval64_neg p33;p34;p35]
      else if coordinate = 1 then
        bounded_interval64_sum
          [p03;p04;bounded_interval64_neg p05;
           bounded_interval64_neg p14;bounded_interval64_neg p14;
           bounded_interval64_neg p23;p24;p25;p34;
           bounded_interval64_neg p44;p45]
      else if coordinate = 2 then
        bounded_interval64_sum
          [p03;bounded_interval64_neg p04;p05;
           bounded_interval64_neg p13;p14;p15;
           bounded_interval64_neg p25;bounded_interval64_neg p25;
           p35;p45;bounded_interval64_neg p55]
      else if coordinate = 3 then
        bounded_interval64_sum
          [bounded_interval64_neg p00;p01;p02;
           bounded_interval64_neg p03;bounded_interval64_neg p03;
           p04;p05;bounded_interval64_neg p12;p14;p25;
           bounded_interval64_neg p45]
      else if coordinate = 4 then
        bounded_interval64_sum
          [p01;bounded_interval64_neg p02;p03;
           bounded_interval64_neg p11;p12;p13;
           bounded_interval64_neg p14;bounded_interval64_neg p14;
           p15;p25;bounded_interval64_neg p35]
      else if coordinate = 5 then
        bounded_interval64_sum
          [bounded_interval64_neg p01;p02;p03;p12;p14;
           bounded_interval64_neg p22;p23;p24;
           bounded_interval64_neg p25;bounded_interval64_neg p25;
           bounded_interval64_neg p34]
      else NONE
    | _ => NONE
End

Definition bounded_delta64_gradient_components_def:
  bounded_delta64_gradient_components [] products = SOME [] ∧
  bounded_delta64_gradient_components (coordinate::coordinates) products =
    case bounded_delta64_gradient_component_from_products coordinate products of
    | NONE => NONE
    | SOME entry =>
      case bounded_delta64_gradient_components coordinates products of
      | NONE => NONE
      | SOME rest => SOME (entry::rest)
End

Definition bounded_delta64_gradient_from_products_def:
  bounded_delta64_gradient_from_products products =
    bounded_delta64_gradient_components [0;1;2;3;4;5] products
End

Definition bounded_delta64_hessian_def:
  bounded_delta64_hessian environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      let n0 = bounded_interval64_neg x0;
          n1 = bounded_interval64_neg x1;
          n2 = bounded_interval64_neg x2;
          n3 = bounded_interval64_neg x3;
          n4 = bounded_interval64_neg x4;
          n5 = bounded_interval64_neg x5
      in
        bounded_interval64_sums
          [[n3;n3];
           [x3;x4;n5];
           [x3;n4;x5];
           [n0;n0;x1;x2;n3;n3;x4;x5];
           [x1;n2;x3];
           [n1;x2;x3];
           [n4;n4];
           [n3;x4;x5];
           [x0;n2;x4];
           [x0;n1;n1;x2;x3;n4;n4;x5];
           [n0;x2;x4];
           [n5;n5];
           [x0;n1;x5];
           [n0;x1;x5];
           [x0;x1;n2;n2;x3;x4;n5;n5];
           [n0;n0];
           [x0;x1;n5];
           [x0;x2;n4];
           [n1;n1];
           [x1;x2;n3];
           [n2;n2]]
    | _ => NONE
End

Definition bounded_delta64_value_six_def:
  bounded_delta64_value_six x0 x1 x2 x3 x4 x5 =
    case bounded_interval64_sum
      [bounded_interval64_neg x0;x1;x2;bounded_interval64_neg x3;x4;x5] of
    | NONE => NONE
    | SOME first_linear =>
      case bounded_interval64_sum
        [x0;bounded_interval64_neg x1;x2;x3;
         bounded_interval64_neg x4;x5] of
      | NONE => NONE
      | SOME second_linear =>
        case bounded_interval64_sum
          [x0;x1;bounded_interval64_neg x2;x3;x4;
           bounded_interval64_neg x5] of
        | NONE => NONE
        | SOME third_linear =>
          case bounded_interval64_mul3 x0 x3 first_linear of
          | NONE => NONE
          | SOME first =>
            case bounded_interval64_mul3 x1 x4 second_linear of
            | NONE => NONE
            | SOME second =>
              case bounded_interval64_mul3 x2 x5 third_linear of
              | NONE => NONE
              | SOME third =>
                case bounded_interval64_mul3 x1 x2 x3 of
                | NONE => NONE
                | SOME fourth =>
                  case bounded_interval64_mul3 x0 x2 x4 of
                  | NONE => NONE
                  | SOME fifth =>
                    case bounded_interval64_mul3 x0 x1 x5 of
                    | NONE => NONE
                    | SOME sixth =>
                      case bounded_interval64_mul3 x3 x4 x5 of
                      | NONE => NONE
                      | SOME seventh =>
                        bounded_interval64_sum
                          [first;second;third;
                           bounded_interval64_neg fourth;
                           bounded_interval64_neg fifth;
                           bounded_interval64_neg sixth;
                           bounded_interval64_neg seventh]
End

Definition bounded_delta64_value_def:
  bounded_delta64_value environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      bounded_delta64_value_six x0 x1 x2 x3 x4 x5
    | _ => NONE
End

Definition bounded_interval64_list_add_at_def:
  bounded_interval64_list_add_at value 0 [] = NONE ∧
  bounded_interval64_list_add_at value 0 (entry::rest) =
    (case bounded_interval64_add entry value of
     | NONE => NONE
     | SOME updated => SOME (updated::rest)) ∧
  bounded_interval64_list_add_at value (SUC index) [] = NONE ∧
  bounded_interval64_list_add_at value (SUC index) (entry::rest) =
    (case bounded_interval64_list_add_at value index rest of
     | NONE => NONE
     | SOME updated => SOME (entry::updated))
End

Definition bounded_delta64_neg_derivative_def:
  bounded_delta64_neg_derivative radii center_environment (coordinate:num) =
    if coordinate < 3 ∨ 5 < coordinate then NONE
    else
      case bounded_delta64_pair_products center_environment of
      | NONE => NONE
      | SOME products =>
        case bounded_delta64_gradient_component_from_products
          coordinate products of
        | NONE => NONE
        | SOME center_value =>
          case bounded_delta64_hessian center_environment of
          | NONE => NONE
          | SOME center_hessian =>
            case bounded_hessian64_rows center_hessian of
            | NONE => NONE
            | SOME center_rows =>
              case bounded_interval64_nth center_rows coordinate of
              | NONE => NONE
              | SOME center_gradient =>
                case bounded_interval64_unit_vector coordinate of
                | NONE => NONE
                | SOME basis =>
                  case bounded_delta64_hessian basis of
                  | NONE => NONE
                  | SOME result_hessian =>
                    bounded_taylor64_complete radii T
                      (bounded_interval64_neg center_value)
                      (bounded_interval64_list_neg center_gradient)
                      (bounded_interval64_list_neg result_hessian)
End

Definition bounded_delta64_hessian_indices_def:
  bounded_delta64_hessian_indices =
    ([(0,0);(0,1);(0,2);(0,3);(0,4);(0,5);
     (1,1);(1,2);(1,3);(1,4);(1,5);
     (2,2);(2,3);(2,4);(2,5);
     (3,3);(3,4);(3,5);
     (4,4);(4,5);
     (5,5)] : (num # num) list)
End

Definition bounded_delta64_product_hessian_entry_def:
  bounded_delta64_product_hessian_entry (coordinate:num) box_coordinate
      delta_gradient (row:num) (column:num) delta_hessian =
    case bounded_interval64_mul box_coordinate delta_hessian of
    | NONE => NONE
    | SOME base =>
      case
        (if row = coordinate then
           case bounded_interval64_nth delta_gradient column of
           | NONE => NONE
           | SOME contribution => bounded_interval64_add base contribution
         else SOME base) of
      | NONE => NONE
      | SOME with_row =>
        case
          (if column = coordinate then
             case bounded_interval64_nth delta_gradient row of
             | NONE => NONE
             | SOME contribution =>
                 bounded_interval64_add with_row contribution
           else SOME with_row) of
        | NONE => NONE
        | SOME complete => bounded_interval64_scale4 complete
End

Definition bounded_delta64_product_hessian_def:
  bounded_delta64_product_hessian (coordinate:num) box_coordinate delta_gradient
      [] [] = SOME [] ∧
  bounded_delta64_product_hessian coordinate box_coordinate delta_gradient
      [] (_::_) = NONE ∧
  bounded_delta64_product_hessian coordinate box_coordinate delta_gradient
      (_::_) [] = NONE ∧
  bounded_delta64_product_hessian coordinate box_coordinate delta_gradient
      ((row,column)::indices) (entry::entries) =
    case bounded_delta64_product_hessian_entry coordinate box_coordinate
      delta_gradient row column entry of
    | NONE => NONE
    | SOME result =>
      case bounded_delta64_product_hessian coordinate box_coordinate
        delta_gradient indices entries of
      | NONE => NONE
      | SOME rest => SOME (result::rest)
End

Definition bounded_delta64_four_coordinate_def:
  bounded_delta64_four_coordinate radii center_environment box_environment
      (coordinate:num) =
    if 2 < coordinate then NONE
    else
      case bounded_delta64_value center_environment of
      | NONE => NONE
      | SOME center_delta =>
        case bounded_delta64_pair_products center_environment of
        | NONE => NONE
        | SOME center_products =>
          case bounded_delta64_gradient_from_products center_products of
          | NONE => NONE
          | SOME center_delta_gradient =>
            case bounded_delta64_hessian box_environment of
            | NONE => NONE
            | SOME box_delta_hessian =>
              case bounded_taylor_gradient_complete radii
                center_delta_gradient box_delta_hessian of
              | NONE => NONE
              | SOME box_delta_gradient =>
                case bounded_interval64_nth center_environment coordinate of
                | NONE => NONE
                | SOME center_coordinate =>
                  case bounded_interval64_nth box_environment coordinate of
                  | NONE => NONE
                  | SOME box_coordinate =>
                    case bounded_interval64_mul
                      center_coordinate center_delta of
                    | NONE => NONE
                    | SOME center_product =>
                      case bounded_interval64_scale4 center_product of
                      | NONE => NONE
                      | SOME center_value =>
                        case bounded_interval64_list_scale center_coordinate
                          center_delta_gradient of
                        | NONE => NONE
                        | SOME center_gradient_base =>
                          case bounded_interval64_list_add_at center_delta
                            coordinate center_gradient_base of
                          | NONE => NONE
                          | SOME center_gradient_unscaled =>
                            case bounded_interval64_list_scale4
                              center_gradient_unscaled of
                            | NONE => NONE
                            | SOME center_gradient =>
                              case bounded_delta64_product_hessian coordinate
                                box_coordinate box_delta_gradient
                                bounded_delta64_hessian_indices
                                box_delta_hessian of
                              | NONE => NONE
                              | SOME result_hessian =>
                                bounded_taylor64_complete radii T center_value
                                  center_gradient result_hessian
End

Theorem bounded_interval64_mul3_contains_scaled_int:
  bounded_interval64_contains_int first first_value ∧
  bounded_interval64_contains_int second second_value ∧
  bounded_interval64_contains_int third third_value ∧
  bounded_interval64_mul3 first second third = SOME result ⇒
  bounded_interval64_contains_scaled_int result
    ((&1099511627776:int) * &1099511627776)
    ((first_value * second_value) * third_value)
Proof
  rw [bounded_interval64_mul3_def]
  >> every_case_tac
  >> gvs []
  >> drule_all
       compute_boundedIntervalTheory.bounded_interval64_mul_contains_scaled_product
  >> disch_tac
  >> drule_all
       compute_boundedIntervalTheory.bounded_interval64_mul_contains_left_scaled_product
  >> simp []
QED

Theorem bounded_interval64_sum_aux_contains_scaled_int:
  ∀values real_values accumulator accumulator_value result scale.
    LIST_REL
      (λinterval value.
         bounded_interval64_contains_scaled_int interval scale value)
      values real_values ∧
    bounded_interval64_contains_scaled_int
      accumulator scale accumulator_value ∧
    bounded_interval64_sum_aux values accumulator = SOME result ⇒
    bounded_interval64_contains_scaled_int result scale
      (FOLDL (λtotal value:int. total + value)
        accumulator_value real_values)
Proof
  Induct
  >> Cases_on `real_values`
  >> rw [bounded_interval64_sum_aux_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> drule_all
       compute_boundedIntervalAddTheory.bounded_interval64_add_contains_scaled_int
  >> disch_tac
  >> first_x_assum drule_all
  >> simp []
QED

Theorem bounded_interval64_sum_contains_scaled_int:
  LIST_REL
    (λinterval value.
       bounded_interval64_contains_scaled_int interval scale value)
    values real_values ∧
  bounded_interval64_sum values = SOME result ⇒
  bounded_interval64_contains_scaled_int result scale
    (FOLDL (λtotal value:int. total + value) 0 real_values)
Proof
  rw [bounded_interval64_sum_def]
  >> irule bounded_interval64_sum_aux_contains_scaled_int
  >> qexists_tac `bounded_interval64_zero`
  >> qexists_tac `values`
  >> simp
       [compute_boundedIntervalListTheory.bounded_interval64_zero_def,
        compute_boundedIntervalTheory.bounded_interval64_contains_scaled_int_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
QED

Theorem bounded_interval64_scale4_contains_scaled_int:
  bounded_interval64_contains_scaled_int source scale value ∧
  bounded_interval64_scale4 source = SOME result ⇒
  bounded_interval64_contains_scaled_int result scale (4 * value)
Proof
  rw [bounded_interval64_scale4_def]
  >> every_case_tac
  >> gvs []
  >> drule_all
       compute_boundedIntervalAddTheory.bounded_interval64_add_contains_scaled_int
  >> disch_tac
  >> drule_all
       compute_boundedIntervalAddTheory.bounded_interval64_add_contains_scaled_int
  >> disch_tac
  >> qsuff_tac
       `(4:int) * value = value + value + (value + value)`
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_list_scale4_contains_scaled_int:
  ∀values real_values result scale.
    LIST_REL
      (λinterval value.
         bounded_interval64_contains_scaled_int interval scale value)
      values real_values ∧
    bounded_interval64_list_scale4 values = SOME result ⇒
    LIST_REL
      (λinterval value.
         bounded_interval64_contains_scaled_int interval scale value)
      result (MAP (λvalue:int. 4 * value) real_values)
Proof
  Induct
  >> Cases_on `real_values`
  >> rw [bounded_interval64_list_scale4_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> res_tac
  >> fs []
  >> metis_tac [bounded_interval64_scale4_contains_scaled_int]
QED

Theorem bounded_interval64_sums_contains_scaled_int:
  ∀values real_values result scale.
    LIST_REL
      (LIST_REL
        (λinterval value.
           bounded_interval64_contains_scaled_int interval scale value))
      values real_values ∧
    bounded_interval64_sums values = SOME result ⇒
    LIST_REL
      (λinterval value.
         bounded_interval64_contains_scaled_int interval scale value)
      result
      (MAP (FOLDL (λtotal value:int. total + value) 0) real_values)
Proof
  Induct
  >> Cases_on `real_values`
  >> rw [bounded_interval64_sums_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> res_tac
  >> fs []
  >> metis_tac [bounded_interval64_sum_contains_scaled_int]
QED

Theorem bounded_interval64_list_add_at_contains_scaled_int:
  ∀index values real_values result value real_value scale.
    LIST_REL
      (λinterval entry_value.
         bounded_interval64_contains_scaled_int
           interval scale entry_value)
      values real_values ∧
    bounded_interval64_contains_scaled_int value scale real_value ∧
    bounded_interval64_list_add_at value index values = SOME result ⇒
    LIST_REL
      (λinterval entry_value.
         bounded_interval64_contains_scaled_int
           interval scale entry_value)
      result
      (LUPDATE (EL index real_values + real_value) index real_values)
Proof
  Induct
  >> Cases_on `values`
  >> Cases_on `real_values`
  >> rw [bounded_interval64_list_add_at_def, LIST_REL_def,
         listTheory.LUPDATE_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> res_tac
  >> fs []
  >> metis_tac
       [compute_boundedIntervalAddTheory.bounded_interval64_add_contains_scaled_int]
QED

Theorem bounded_delta64_neg_derivative_some:
  bounded_delta64_neg_derivative radii center_environment coordinate =
    SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_delta64_neg_derivative_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorUnaryTheory.bounded_taylor64_complete_some
QED

Theorem bounded_delta64_four_coordinate_some:
  bounded_delta64_four_coordinate radii center_environment box_environment
      coordinate = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_delta64_four_coordinate_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorUnaryTheory.bounded_taylor64_complete_some
QED

val _ = export_theory ();
