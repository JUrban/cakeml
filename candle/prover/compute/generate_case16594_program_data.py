#!/usr/bin/env python3
"""Generate the typed bounded case16594 analytic-program fixture.

The input is the exact cval program exported by the proved HOL Light source
reifier.  This generator is untrusted preparation: it accepts only the pinned
payload, parses every constructor, checks both postfix stacks, and emits a
HOL4 datatype constant plus executable fail-closed shape checks.  The eventual
source-correspondence theorem remains the authority for specialization roles.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
from pathlib import Path
from typing import TypeAlias


EXPECTED_PROGRAM_SHA256 = (
    "82f5c7f81b7a6ec292b6426caddaddb1ce7fde5dfbd83c2900a072f679a28dcb"
)
EXPECTED_OUTER_INSTRUCTIONS = 167

SPECIALIZATION_ROLES = {
    34: "BoundedNegDeltaDerivative 3",
    35: "BoundedFourCoordinateDelta 0",
    77: "BoundedNegDeltaDerivative 4",
    78: "BoundedFourCoordinateDelta 1",
    120: "BoundedNegDeltaDerivative 5",
    121: "BoundedFourCoordinateDelta 2",
}

Node: TypeAlias = int | tuple["Node", "Node"]


class Parser:
    def __init__(self, text: str) -> None:
        self.text = text
        self.position = 0

    def parse(self) -> Node:
        result = self._node()
        if self.position != len(self.text):
            raise ValueError(f"trailing cval data at byte {self.position}")
        return result

    def _node(self) -> Node:
        if self.position >= len(self.text):
            raise ValueError("unexpected end of cval")
        if self.text[self.position] == "n":
            self.position += 1
            begin = self.position
            while (
                self.position < len(self.text)
                and self.text[self.position].isdigit()
            ):
                self.position += 1
            if begin == self.position:
                raise ValueError(f"empty numeral at byte {begin}")
            return int(self.text[begin : self.position])
        if not self.text.startswith("p(", self.position):
            raise ValueError(f"expected cval node at byte {self.position}")
        self.position += 2
        left = self._node()
        self._expect(",")
        right = self._node()
        self._expect(")")
        return left, right

    def _expect(self, character: str) -> None:
        if (
            self.position >= len(self.text)
            or self.text[self.position] != character
        ):
            raise ValueError(
                f"expected {character!r} at byte {self.position}"
            )
        self.position += 1


def decode_list(node: Node, context: str) -> list[Node]:
    result: list[Node] = []
    while isinstance(node, tuple):
        head, node = node
        result.append(head)
    if node != 0:
        raise ValueError(f"{context}: nonzero list tail {node}")
    return result


@dataclass(frozen=True)
class PolyInstruction:
    kind: str
    arguments: tuple[int, ...] = ()


@dataclass(frozen=True)
class AnalyticInstruction:
    kind: str
    polynomial: tuple[PolyInstruction, ...] = ()


def require_numeral(node: Node, context: str) -> int:
    if isinstance(node, tuple):
        raise ValueError(f"{context}: expected numeral")
    return node


def decode_rational(node: Node, context: str) -> tuple[int, int, int]:
    if not isinstance(node, tuple) or not isinstance(node[0], tuple):
        raise ValueError(f"{context}: malformed rational")
    (positive, negative), denominator_predecessor = node
    return (
        require_numeral(positive, f"{context} positive"),
        require_numeral(negative, f"{context} negative"),
        require_numeral(denominator_predecessor, f"{context} denominator"),
    )


def decode_polynomial(node: Node, outer_index: int) -> tuple[PolyInstruction, ...]:
    result: list[PolyInstruction] = []
    depth = 0
    for inner_index, instruction in enumerate(
        decode_list(node, f"outer {outer_index} polynomial")
    ):
        context = f"outer {outer_index} polynomial {inner_index}"
        if isinstance(instruction, tuple):
            tag, payload = instruction
            tag = require_numeral(tag, f"{context} tag")
            if tag == 0:
                result.append(
                    PolyInstruction("constant", decode_rational(payload, context))
                )
            elif tag == 1:
                variable = require_numeral(payload, f"{context} variable")
                if not 0 <= variable < 6:
                    raise ValueError(f"{context}: variable out of range")
                result.append(PolyInstruction("variable", (variable,)))
            else:
                raise ValueError(f"{context}: unknown pair tag {tag}")
            depth += 1
            continue

        names = {2: "neg", 3: "add", 4: "mul", 5: "square"}
        if instruction not in names:
            raise ValueError(f"{context}: unknown opcode {instruction}")
        kind = names[instruction]
        needed = 1 if kind in ("neg", "square") else 2
        if depth < needed:
            raise ValueError(f"{context}: postfix stack underflow")
        if needed == 2:
            depth -= 1
        result.append(PolyInstruction(kind))
    if depth != 1 or not result:
        raise ValueError(f"outer {outer_index}: polynomial final stack {depth}")
    return tuple(result)


def is_placeholder_sqrt(payload: Node) -> bool:
    return payload == (((0, 0), 0), ((100, 0), 0))


def decode_program(root: Node) -> list[AnalyticInstruction]:
    result: list[AnalyticInstruction] = []
    depth = 0
    sqrt_count = 0
    names = {
        2: "neg",
        3: "add",
        4: "mul",
        5: "square",
        6: "inverse",
        7: "atan",
        8: "pi_half",
    }
    for outer_index, instruction in enumerate(
        decode_list(root, "analytic program")
    ):
        context = f"outer {outer_index}"
        if isinstance(instruction, tuple):
            tag, payload = instruction
            tag = require_numeral(tag, f"{context} tag")
            if tag == 0:
                result.append(
                    AnalyticInstruction(
                        "polynomial", decode_polynomial(payload, outer_index)
                    )
                )
                depth += 1
            elif tag == 1:
                if not is_placeholder_sqrt(payload):
                    raise ValueError(f"{context}: sqrt placeholder drift")
                if depth < 1:
                    raise ValueError(f"{context}: sqrt stack underflow")
                result.append(AnalyticInstruction("sqrt"))
                sqrt_count += 1
            else:
                raise ValueError(f"{context}: unknown pair tag {tag}")
            continue

        if instruction not in names:
            raise ValueError(f"{context}: unknown opcode {instruction}")
        kind = names[instruction]
        if kind == "pi_half":
            depth += 1
        elif kind in ("add", "mul"):
            if depth < 2:
                raise ValueError(f"{context}: binary stack underflow")
            depth -= 1
        elif depth < 1:
            raise ValueError(f"{context}: unary stack underflow")
        result.append(AnalyticInstruction(kind))

    if len(result) != EXPECTED_OUTER_INSTRUCTIONS:
        raise ValueError(f"analytic instruction count drift: {len(result)}")
    if depth != 1 or sqrt_count != 10:
        raise ValueError(
            f"analytic final shape drift: depth={depth} sqrt={sqrt_count}"
        )
    return result


def role_for(index: int) -> str:
    return SPECIALIZATION_ROLES.get(index, "BoundedAnalyticGeneral")


def render_poly(instruction: PolyInstruction) -> str:
    constructors = {
        "constant": "BoundedPolyConstant",
        "variable": "BoundedPolyVariable",
        "neg": "BoundedPolyNeg",
        "add": "BoundedPolyAdd",
        "mul": "BoundedPolyMul",
        "square": "BoundedPolySquare",
    }
    constructor = constructors[instruction.kind]
    if not instruction.arguments:
        return constructor
    return constructor + " " + " ".join(map(str, instruction.arguments))


def render_analytic(instruction: AnalyticInstruction) -> str:
    constructors = {
        "sqrt": "BoundedAnalyticSqrt",
        "neg": "BoundedAnalyticNeg",
        "add": "BoundedAnalyticAdd",
        "mul": "BoundedAnalyticMul",
        "square": "BoundedAnalyticSquare",
        "inverse": "BoundedAnalyticInverse",
        "atan": "BoundedAnalyticAtan",
        "pi_half": "BoundedAnalyticPiHalf",
    }
    if instruction.kind != "polynomial":
        return constructors[instruction.kind]
    body = "; ".join(render_poly(item) for item in instruction.polynomial)
    return f"BoundedAnalyticPolynomial [{body}]"


def render(program: list[AnalyticInstruction]) -> str:
    instructions = "\n".join(
        f"    {render_analytic(instruction)}{';' if index + 1 < len(program) else ''}"
        for index, instruction in enumerate(program)
    )
    roles = "\n".join(
        f"    {role_for(index)}{';' if index + 1 < len(program) else ''}"
        for index in range(len(program))
    )
    derivative_cases = "\n".join(
        (
            f"        if coordinate = {coordinate} then\n"
            f"          SOME [{'; '.join(render_poly(item) for item in program[index].polynomial)}]\n"
            "        else"
        )
        for index, coordinate in ((34, 3), (77, 4), (120, 5))
    )
    radicand_cases = "\n".join(
        (
            f"        if coordinate = {coordinate} then\n"
            f"          SOME [{'; '.join(render_poly(item) for item in program[index].polynomial)}]\n"
            "        else"
        )
        for index, coordinate in ((35, 0), (78, 1), (121, 2))
    )
    return f'''(*
  GENERATED by generate_case16594_program_data.py.
  Source program SHA-256: {EXPECTED_PROGRAM_SHA256}
  DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.

  The six specialization roles are leads authenticated by the current exact
  rational source normalizer.  Their general source-correspondence proof is a
  separate obligation; the closed executor must not infer them from position
  or polynomial length alone.
*)
Theory compute_boundedCase16594ProgramData
Ancestors
  arithmetic
Libs
  bossLib

Datatype:
  bounded_poly_instruction =
    BoundedPolyConstant num num num
  | BoundedPolyVariable num
  | BoundedPolyNeg
  | BoundedPolyAdd
  | BoundedPolyMul
  | BoundedPolySquare
End

Datatype:
  bounded_analytic_instruction =
    BoundedAnalyticPolynomial (bounded_poly_instruction list)
  | BoundedAnalyticSqrt
  | BoundedAnalyticNeg
  | BoundedAnalyticAdd
  | BoundedAnalyticMul
  | BoundedAnalyticSquare
  | BoundedAnalyticInverse
  | BoundedAnalyticAtan
  | BoundedAnalyticPiHalf
End

Datatype:
  bounded_analytic_specialization =
    BoundedAnalyticGeneral
  | BoundedNegDeltaDerivative num
  | BoundedFourCoordinateDelta num
End

Definition bounded_case16594_program_def:
  bounded_case16594_program : bounded_analytic_instruction list =
  [
{instructions}
  ]
End

Definition bounded_case16594_specializations_def:
  bounded_case16594_specializations : bounded_analytic_specialization list =
  [
{roles}
  ]
End

Definition bounded_poly_stack_step_def:
  bounded_poly_stack_step instruction depth =
    case instruction of
    | BoundedPolyConstant positive negative denominator => SOME (SUC depth)
    | BoundedPolyVariable variable =>
        if variable < 6 then SOME (SUC depth) else NONE
    | BoundedPolyNeg => if depth = 0 then NONE else SOME depth
    | BoundedPolySquare => if depth = 0 then NONE else SOME depth
    | BoundedPolyAdd => if depth < 2 then NONE else SOME (PRE depth)
    | BoundedPolyMul => if depth < 2 then NONE else SOME (PRE depth)
End

Definition bounded_poly_stack_def:
  bounded_poly_stack [] depth = SOME depth /\\
  bounded_poly_stack (instruction::rest) depth =
    case bounded_poly_stack_step instruction depth of
    | NONE => NONE
    | SOME next => bounded_poly_stack rest next
End

Definition bounded_poly_program_ok_def:
  bounded_poly_program_ok program =
    (bounded_poly_stack program 0 = SOME 1)
End

Definition bounded_analytic_stack_step_def:
  bounded_analytic_stack_step instruction (depth,sqrt_count) =
    case instruction of
    | BoundedAnalyticPolynomial program =>
        if bounded_poly_program_ok program then
          SOME (SUC depth,sqrt_count)
        else NONE
    | BoundedAnalyticSqrt =>
        if depth = 0 then NONE else SOME (depth,SUC sqrt_count)
    | BoundedAnalyticNeg =>
        if depth = 0 then NONE else SOME (depth,sqrt_count)
    | BoundedAnalyticSquare =>
        if depth = 0 then NONE else SOME (depth,sqrt_count)
    | BoundedAnalyticInverse =>
        if depth = 0 then NONE else SOME (depth,sqrt_count)
    | BoundedAnalyticAtan =>
        if depth = 0 then NONE else SOME (depth,sqrt_count)
    | BoundedAnalyticAdd =>
        if depth < 2 then NONE else SOME (PRE depth,sqrt_count)
    | BoundedAnalyticMul =>
        if depth < 2 then NONE else SOME (PRE depth,sqrt_count)
    | BoundedAnalyticPiHalf => SOME (SUC depth,sqrt_count)
End

Definition bounded_analytic_stack_def:
  bounded_analytic_stack [] state = SOME state /\\
  bounded_analytic_stack (instruction::rest) state =
    case bounded_analytic_stack_step instruction state of
    | NONE => NONE
    | SOME next => bounded_analytic_stack rest next
End

Definition bounded_analytic_specialization_program_def:
  bounded_analytic_specialization_program role =
    case role of
    | BoundedAnalyticGeneral => NONE
    | BoundedNegDeltaDerivative coordinate =>
{derivative_cases}
          NONE
    | BoundedFourCoordinateDelta coordinate =>
{radicand_cases}
          NONE
End

Definition bounded_analytic_specialization_ok_def:
  bounded_analytic_specialization_ok instruction role =
    case bounded_analytic_specialization_program role of
    | NONE => (role = BoundedAnalyticGeneral)
    | SOME expected =>
        (instruction = BoundedAnalyticPolynomial expected)
End

Definition bounded_analytic_specializations_ok_def:
  bounded_analytic_specializations_ok [] [] = T /\\
  bounded_analytic_specializations_ok
      (instruction::instructions) (role::roles) =
    (bounded_analytic_specialization_ok instruction role /\\
     bounded_analytic_specializations_ok instructions roles) /\\
  bounded_analytic_specializations_ok _ _ = F
End

Definition bounded_case16594_program_ok_def:
  bounded_case16594_program_ok =
    (LENGTH bounded_case16594_program = 167 /\\
     bounded_analytic_stack bounded_case16594_program (0,0) =
       SOME (1,10) /\\
     bounded_analytic_specializations_ok bounded_case16594_program
       bounded_case16594_specializations)
End

Theorem bounded_case16594_program_ok_value:
  bounded_case16594_program_ok
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_specialization_aliases_rejected:
  ¬bounded_analytic_specialization_ok
      (BoundedAnalyticPolynomial (REPLICATE 39 BoundedPolyNeg))
      (BoundedNegDeltaDerivative 3) /\\
  ¬bounded_analytic_specialization_ok
      (BoundedAnalyticPolynomial (REPLICATE 85 BoundedPolyMul))
      (BoundedFourCoordinateDelta 0) /\\
  ¬bounded_analytic_specialization_ok
      (BoundedAnalyticPolynomial [])
      (BoundedNegDeltaDerivative 0) /\\
  ¬bounded_analytic_specialization_ok
      (BoundedAnalyticPolynomial [])
      (BoundedFourCoordinateDelta 6)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_specialization_positions:
  MAPi (\\index role. if role = BoundedAnalyticGeneral then NONE
                     else SOME (index,role))
       bounded_case16594_specializations =
  [NONE; NONE; NONE; NONE; NONE; NONE; NONE; NONE; NONE; NONE;
   NONE; NONE; NONE; NONE; NONE; NONE; NONE; NONE; NONE; NONE;
   NONE; NONE; NONE; NONE; NONE; NONE; NONE; NONE; NONE; NONE;
   NONE; NONE; NONE; NONE; SOME (34,BoundedNegDeltaDerivative 3);
   SOME (35,BoundedFourCoordinateDelta 0)] ++
  REPLICATE 41 NONE ++
  [SOME (77,BoundedNegDeltaDerivative 4);
   SOME (78,BoundedFourCoordinateDelta 1)] ++
  REPLICATE 41 NONE ++
  [SOME (120,BoundedNegDeltaDerivative 5);
   SOME (121,BoundedFourCoordinateDelta 2)] ++
  REPLICATE 45 NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("program", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    payload = args.program.read_bytes()
    actual_hash = hashlib.sha256(payload).hexdigest()
    if actual_hash != EXPECTED_PROGRAM_SHA256:
        raise ValueError(f"case16594 program identity drift: {actual_hash}")
    text = payload.decode("ascii")
    if not text.endswith("\n") or "\n" in text[:-1]:
        raise ValueError("case16594 program must be one newline-terminated line")
    program = decode_program(Parser(text[:-1]).parse())
    args.output.write_text(render(program), encoding="utf-8")


if __name__ == "__main__":
    main()
