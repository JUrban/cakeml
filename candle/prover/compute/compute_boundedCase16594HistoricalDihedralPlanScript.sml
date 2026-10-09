(*****************************************************************************
 * Source-authenticated historical-dihedral motif recognition.
 *
 * DEVELOPMENT / NON-RELEASE.  A motif is authorized by the exact source
 * instruction sequence together with the already authenticated polynomial
 * specialization roles.  Positions are observations of the pinned program,
 * never authority: changing either polynomial bytes, either coordinate role,
 * or any scalar operation makes recognition fail closed.
 *****************************************************************************)
Theory compute_boundedCase16594HistoricalDihedralPlan
Ancestors
  compute_boundedCase16594ProgramData
  compute_boundedCase16594SourceDagPlan
Libs
  bossLib preamble

Datatype:
  bounded_historical_dihedral_motif =
    BoundedHistoricalDihedralMotif num num num
End

Definition bounded_historical_dihedral_prefix_def:
  bounded_historical_dihedral_prefix instructions roles =
    case (instructions,roles) of
    | (BoundedAnalyticPiHalf::
       derivative_instruction::
       radicand_instruction::
       BoundedAnalyticSqrt::
       BoundedAnalyticInverse::
       BoundedAnalyticMul::
       BoundedAnalyticAtan::
       BoundedAnalyticAdd::instruction_rest,
       BoundedAnalyticGeneral::
       BoundedNegDeltaDerivative derivative_coordinate::
       BoundedFourCoordinateDelta radicand_coordinate::
       BoundedAnalyticGeneral::
       BoundedAnalyticGeneral::
       BoundedAnalyticGeneral::
       BoundedAnalyticGeneral::
       BoundedAnalyticGeneral::role_rest) =>
         if radicand_coordinate < 3 /\
            derivative_coordinate = radicand_coordinate + 3 /\
            bounded_analytic_specialization_ok derivative_instruction
              (BoundedNegDeltaDerivative derivative_coordinate) /\
            bounded_analytic_specialization_ok radicand_instruction
              (BoundedFourCoordinateDelta radicand_coordinate)
         then SOME (radicand_coordinate,derivative_coordinate)
         else NONE
    | _ => NONE
End

Definition bounded_historical_dihedral_scan_def:
  bounded_historical_dihedral_scan [] roles index = [] /\
  bounded_historical_dihedral_scan (instruction::instructions) [] index = [] /\
  bounded_historical_dihedral_scan
      (instruction::instructions) (role::roles) index =
    case bounded_historical_dihedral_prefix
      (instruction::instructions) (role::roles) of
    | NONE =>
        bounded_historical_dihedral_scan instructions roles (SUC index)
    | SOME (radicand_coordinate,derivative_coordinate) =>
        BoundedHistoricalDihedralMotif index radicand_coordinate
          derivative_coordinate::
        bounded_historical_dihedral_scan instructions roles (SUC index)
End

Definition bounded_case16594_historical_dihedral_motifs_def:
  bounded_case16594_historical_dihedral_motifs =
    bounded_historical_dihedral_scan bounded_case16594_program
      bounded_case16594_specializations 0
End

Definition bounded_historical_dihedral_root_identity_def:
  bounded_historical_dihedral_root_identity
      (BoundedHistoricalDihedralMotif start radicand_coordinate
        derivative_coordinate) identities =
    oEL (start + 7) identities
End

Definition bounded_historical_dihedral_permutation_def:
  bounded_historical_dihedral_permutation coordinate =
    if coordinate = 0 then SOME [0;1;2;3;4;5]
    else if coordinate = 1 then SOME [1;0;2;4;3;5]
    else if coordinate = 2 then SOME [2;1;0;5;4;3]
    else NONE
End

Theorem bounded_case16594_historical_dihedral_motifs_value:
  bounded_case16594_historical_dihedral_motifs =
    [BoundedHistoricalDihedralMotif 33 0 3;
     BoundedHistoricalDihedralMotif 76 1 4;
     BoundedHistoricalDihedralMotif 119 2 5]
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_historical_dihedral_root_identities:
  MAP (\motif. bounded_historical_dihedral_root_identity motif
        bounded_case16594_source_dag_identities)
      bounded_case16594_historical_dihedral_motifs =
    [SOME 34;SOME 50;SOME 65]
Proof
  EVAL_TAC
QED

Theorem bounded_historical_dihedral_permutations_value:
  bounded_historical_dihedral_permutation 0 = SOME [0;1;2;3;4;5] /\
  bounded_historical_dihedral_permutation 1 = SOME [1;0;2;4;3;5] /\
  bounded_historical_dihedral_permutation 2 = SOME [2;1;0;5;4;3] /\
  bounded_historical_dihedral_permutation 3 = NONE
Proof
  EVAL_TAC
QED

Theorem bounded_historical_dihedral_permutations_ok:
  EVERY
    (\coordinate.
      case bounded_historical_dihedral_permutation coordinate of
      | NONE => F
      | SOME permutation =>
          LENGTH permutation = 6 /\
          ALL_DISTINCT permutation /\
          EVERY (\index. index < 6) permutation /\
          EL 0 permutation = coordinate /\
          EL 3 permutation = coordinate + 3 /\
          MAP (\index. EL (EL index permutation) permutation)
            [0;1;2;3;4;5] = [0;1;2;3;4;5])
    [0;1;2]
Proof
  EVAL_TAC
QED

Theorem bounded_historical_dihedral_prefix_rejects_aliases:
  let derivative = BoundedAnalyticPolynomial
    (THE (bounded_analytic_specialization_program
      (BoundedNegDeltaDerivative 3))) in
  let radicand = BoundedAnalyticPolynomial
    (THE (bounded_analytic_specialization_program
      (BoundedFourCoordinateDelta 0))) in
  let instructions =
    [BoundedAnalyticPiHalf;derivative;radicand;BoundedAnalyticSqrt;
     BoundedAnalyticInverse;BoundedAnalyticMul;BoundedAnalyticAtan;
     BoundedAnalyticAdd] in
  let roles =
    [BoundedAnalyticGeneral;BoundedNegDeltaDerivative 3;
     BoundedFourCoordinateDelta 0;BoundedAnalyticGeneral;
     BoundedAnalyticGeneral;BoundedAnalyticGeneral;
     BoundedAnalyticGeneral;BoundedAnalyticGeneral] in
    bounded_historical_dihedral_prefix instructions roles = SOME (0,3) /\
    bounded_historical_dihedral_prefix
      (LUPDATE (BoundedAnalyticPolynomial (REPLICATE 39 BoundedPolyNeg))
        1 instructions) roles = NONE /\
    bounded_historical_dihedral_prefix instructions
      (LUPDATE (BoundedFourCoordinateDelta 1) 2 roles) = NONE /\
    bounded_historical_dihedral_prefix
      (LUPDATE BoundedAnalyticSquare 6 instructions) roles = NONE /\
    bounded_historical_dihedral_prefix (TL instructions) (TL roles) = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
