(*****************************************************************************
 * Fixed-width execution of the literal case-10173 source expression.
 *
 * The optimized cell checker postpones Taylor completion across additions.
 * That is useful numerically, but the original Flyspeck source evaluates six
 * coordinate products, one historical item, and thirteen additions in a
 * fixed stack order.  This development executes that exact source-shaped
 * calculation on the bounded decimal carrier.  It is intended to provide a
 * small refinement boundary to the unchanged source evaluator without
 * falling back to the generic rational interpreter.
 *****************************************************************************)
Theory compute_boundedCase10173LiteralSourceDecimal
Ancestors
  compute_boundedCase10173ActualSqrtOperand
  compute_boundedCase10173HistoricalCellDecimal
Libs
  bossLib preamble

Definition bounded_case10173_literal_term0_decimal_def:
  bounded_case10173_literal_term0_decimal =
    BoundedInterval64
      (BoundedSigned64 F 1277000000000w)
      (BoundedSigned64 F 1277000000000w)
End

Definition bounded_case10173_literal_term1_decimal_def:
  bounded_case10173_literal_term1_decimal =
    BoundedInterval64
      (BoundedSigned64 T 595789640000w)
      (BoundedSigned64 T 595789640000w)
End

Definition bounded_case10173_literal_term23_decimal_def:
  bounded_case10173_literal_term23_decimal =
    BoundedInterval64
      (BoundedSigned64 F 547706000000w)
      (BoundedSigned64 F 547706000000w)
End

Definition bounded_case10173_literal_term4_decimal_def:
  bounded_case10173_literal_term4_decimal =
    BoundedInterval64
      (BoundedSigned64 T 1417636000000w)
      (BoundedSigned64 T 1417636000000w)
End

Definition bounded_case10173_literal_term56_decimal_def:
  bounded_case10173_literal_term56_decimal =
    BoundedInterval64
      (BoundedSigned64 F 627976000000w)
      (BoundedSigned64 F 627976000000w)
End

Definition bounded_case10173_literal_negative_one_decimal_def:
  bounded_case10173_literal_negative_one_decimal =
    BoundedInterval64
      (BoundedSigned64 T 1000000000000w)
      (BoundedSigned64 T 1000000000000w)
End

(* Products are returned in source execution order, coordinate 0 through 5.
 * The actual source operand is the Taylor-completed variable value_bound, not
 * the original input-box coordinate. *)
Definition bounded_case10173_literal_products_decimal_def:
  bounded_case10173_literal_products_decimal
      0 index radii center_environment certificates = SOME [] /\
  bounded_case10173_literal_products_decimal
      (SUC remaining) index radii center_environment
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
        center_derivative box_derivative box_second_reciprocal::certificates) =
    (if 6 <= index then NONE
     else
       case bounded_case10173_actual_variable_decimal
         radii center_environment index of
       | NONE => NONE
       | SOME variable =>
         case bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
           center_derivative box_derivative box_second_reciprocal variable of
         | NONE => NONE
         | SOME root =>
           case bounded_interval64_nth
             bounded_case10173_root_coefficients_decimal index of
           | NONE => NONE
           | SOME coefficient =>
             case bounded_taylor64_constant coefficient of
             | NONE => NONE
             | SOME coefficient_state =>
               case bounded_taylor64_mul_decimal radii root
                 coefficient_state of
               | NONE => NONE
               | SOME product =>
                 case bounded_case10173_literal_products_decimal
                   remaining (SUC index) radii center_environment
                   certificates of
                 | NONE => NONE
                 | SOME products => SOME (product::products)) /\
  bounded_case10173_literal_products_decimal
      (SUC remaining) index radii center_environment _ = NONE
End

Definition bounded_case10173_literal_constants_decimal_def:
  bounded_case10173_literal_constants_decimal =
    case bounded_taylor64_constant
      bounded_case10173_literal_term0_decimal of
    | NONE => NONE
    | SOME term0 =>
      case bounded_taylor64_constant
        bounded_case10173_literal_term1_decimal of
      | NONE => NONE
      | SOME term1 =>
        case bounded_taylor64_constant
          bounded_case10173_literal_term23_decimal of
        | NONE => NONE
        | SOME term23 =>
          case bounded_taylor64_constant
            bounded_case10173_literal_term4_decimal of
          | NONE => NONE
          | SOME term4 =>
            case bounded_taylor64_constant
              bounded_case10173_literal_term56_decimal of
            | NONE => NONE
            | SOME term56 =>
                SOME [term0;term1;term23;term23;term4;term56;term56]
End

(* This is the top-to-bottom stack left by the 31-instruction prefix. *)
Definition bounded_case10173_literal_summands_decimal_def:
  bounded_case10173_literal_summands_decimal
      [product0;product1;product2;product3;product4;product5]
      [term0;term1;term2;term3;term4;term5;term6] =
    SOME
      [term6;product5;term5;product4;term4;product3;term3;
       product2;term2;product1;term1;product0;term0] /\
  bounded_case10173_literal_summands_decimal _ _ = NONE
End

(* [fs_result_add] discards the incoming whole-box bounds after adding the
 * center jet and Hessian, then Taylor-completes the sum. *)
Definition bounded_case10173_literal_add_decimal_def:
  bounded_case10173_literal_add_decimal radii left right =
    case bounded_taylor64_add left right of
    | NONE => NONE
    | SOME
        (BoundedTaylor64 domain_flag center_value center_gradient
          value_bound gradient_bounds hessian) =>
        bounded_taylor64_complete_decimal radii domain_flag center_value
          center_gradient hessian
End

Definition bounded_case10173_literal_add_stack_decimal_def:
  bounded_case10173_literal_add_stack_decimal radii [] accumulator =
    SOME accumulator /\
  bounded_case10173_literal_add_stack_decimal radii
      (summand::summands) accumulator =
    case bounded_case10173_literal_add_decimal radii summand accumulator of
    | NONE => NONE
    | SOME next =>
        bounded_case10173_literal_add_stack_decimal radii summands next
End

Definition bounded_case10173_literal_historical_item_decimal_def:
  bounded_case10173_literal_historical_item_decimal radii
      center_environment box_environment center_root_delta
      center_root_four_x0 center_reciprocals box_root_delta
      box_root_four_x0 box_reciprocals =
    case bounded_historical_dihedral_first64_decimal center_environment
      center_root_delta center_root_four_x0 center_reciprocals of
    | NONE => NONE
    | SOME (center_value,center_gradient) =>
      case bounded_historical_dihedral_second64_decimal box_environment
        box_root_delta box_root_four_x0 box_reciprocals of
      | NONE => NONE
      | SOME (box_value,box_gradient,hessian) =>
          bounded_taylor64_complete_decimal radii T center_value
            center_gradient hessian
End

Definition bounded_case10173_literal_source_decimal_def:
  bounded_case10173_literal_source_decimal
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) =
    case bounded_case10173_literal_products_decimal 6 0 radii
      center_environment coordinate_sqrt_certificates of
    | NONE => NONE
    | SOME products =>
      case bounded_case10173_literal_constants_decimal of
      | NONE => NONE
      | SOME literal_states =>
        case bounded_case10173_literal_summands_decimal products
          literal_states of
        | NONE => NONE
        | SOME summands =>
          case bounded_case10173_literal_historical_item_decimal radii
            center_environment box_environment center_root_delta
            center_root_four_x0 center_reciprocals box_root_delta
            box_root_four_x0 box_reciprocals of
          | NONE => NONE
          | SOME historical_item =>
            case bounded_taylor64_constant
              bounded_case10173_literal_negative_one_decimal of
            | NONE => NONE
            | SOME negative_one =>
              case bounded_taylor64_mul_decimal radii historical_item
                negative_one of
              | NONE => NONE
              | SOME scaled_historical =>
                  bounded_case10173_literal_add_stack_decimal radii summands
                    scaled_historical
End

Definition bounded_case10173_literal_source_accepts_decimal_def:
  bounded_case10173_literal_source_accepts_decimal packet <=>
    case bounded_case10173_literal_source_decimal packet of
    | NONE => F
    | SOME
        (BoundedTaylor64 domain_flag center_value center_gradient
          value_bound gradient_bounds hessian) =>
        domain_flag /\
        bounded_signed64_strict_negative
          (bounded_interval64_upper value_bound)
End

Theorem bounded_case10173_literal_add_decimal_some:
  bounded_case10173_literal_add_decimal radii left right = SOME result ==>
  bounded_taylor64_well_formed result
Proof
  rw [bounded_case10173_literal_add_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_some
QED

Theorem bounded_case10173_literal_add_stack_decimal_some:
  !summands accumulator result.
    bounded_case10173_literal_add_stack_decimal radii summands accumulator =
      SOME result /\
    bounded_taylor64_well_formed accumulator ==>
    bounded_taylor64_well_formed result
Proof
  Induct
  >> rw [bounded_case10173_literal_add_stack_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_case10173_literal_add_decimal_some
  >> res_tac
QED

Theorem bounded_case10173_literal_source_accepts_contract:
  bounded_case10173_literal_source_accepts_decimal packet ==>
  ?center_value center_gradient value_bound gradient_bounds hessian.
    bounded_case10173_literal_source_decimal packet =
      SOME
        (BoundedTaylor64 T center_value center_gradient value_bound
          gradient_bounds hessian) /\
    bounded_signed64_strict_negative
      (bounded_interval64_upper value_bound)
Proof
  rw [bounded_case10173_literal_source_accepts_decimal_def]
  >> every_case_tac
  >> gvs []
QED

val _ = export_theory ();
