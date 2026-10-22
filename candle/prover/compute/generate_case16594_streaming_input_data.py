#!/usr/bin/env python3
"""Generate indexed fixed-word inputs for streaming case16594 execution.

The source is the pinned 875-row native-input export.  The generated accessor
stores the box, center, and radius for one cell behind a balanced index test,
so compiled checkers never have to materialize the complete fixture as one
live ML list.  The data is still untrusted input to the checked executor.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
from pathlib import Path


EXPECTED_INPUT_SHA256 = (
    "236c4ffa1773b92c80584defa24beeddfb20b59811bc287a4f4770da87ac8e80"
)
SCALE = 1 << 40
WORD_LIMIT = 1 << 64


@dataclass(frozen=True)
class Cell:
    box: tuple[tuple[int, int], ...]
    centers: tuple[tuple[int, int], ...]
    radii: tuple[int, ...]


def floor_scaled(value: Fraction) -> int:
    return (value.numerator * SCALE) // value.denominator


def ceil_scaled(value: Fraction) -> int:
    return -((-value.numerator * SCALE) // value.denominator)


def checked_word(value: int, context: str) -> int:
    if not 0 <= value < WORD_LIMIT:
        raise ValueError(f"word width/sign drift at {context}: {value}")
    return value


def load_cells(path: Path) -> list[Cell]:
    payload = path.read_bytes()
    actual_hash = hashlib.sha256(payload).hexdigest()
    if actual_hash != EXPECTED_INPUT_SHA256:
        raise ValueError(f"case16594 input identity drift: {actual_hash}")
    rows = payload.decode("ascii").splitlines()
    if len(rows) != 875:
        raise ValueError(f"case16594 row count drift: {len(rows)}")

    cells = []
    for expected_index, row in enumerate(rows):
        fields = row.split("\t")
        if len(fields) != 5 or int(fields[0]) != expected_index:
            raise ValueError(f"malformed case16594 row {expected_index}")
        lower = [Fraction(value) for value in fields[3].split(",")]
        upper = [Fraction(value) for value in fields[4].split(",")]
        if len(lower) != 6 or len(upper) != 6:
            raise ValueError(f"box width drift at row {expected_index}")

        box = []
        centers = []
        radii = []
        for coordinate, (lo, hi) in enumerate(zip(lower, upper)):
            if lo > hi:
                raise ValueError(
                    f"reversed box at row {expected_index}[{coordinate}]"
                )
            midpoint = (lo + hi) / 2
            radius = (hi - lo) / 2
            box.append(
                (
                    checked_word(
                        floor_scaled(lo),
                        f"row {expected_index} box[{coordinate}] lower",
                    ),
                    checked_word(
                        ceil_scaled(hi),
                        f"row {expected_index} box[{coordinate}] upper",
                    ),
                )
            )
            centers.append(
                (
                    checked_word(
                        floor_scaled(midpoint),
                        f"row {expected_index} center[{coordinate}] lower",
                    ),
                    checked_word(
                        ceil_scaled(midpoint),
                        f"row {expected_index} center[{coordinate}] upper",
                    ),
                )
            )
            radii.append(
                checked_word(
                    ceil_scaled(radius),
                    f"row {expected_index} radius[{coordinate}]",
                )
            )
        cells.append(Cell(tuple(box), tuple(centers), tuple(radii)))
    return cells


def render_pairs(values: tuple[tuple[int, int], ...], indent: str) -> str:
    return "\n".join(
        f"{indent}({lower}w,{upper}w){';' if index + 1 != len(values) else ''}"
        for index, (lower, upper) in enumerate(values)
    )


def render_words(values: tuple[int, ...], indent: str) -> str:
    return "\n".join(
        f"{indent}{value}w{';' if index + 1 != len(values) else ''}"
        for index, value in enumerate(values)
    )


def render_cell(cell: Cell, indent: str) -> str:
    child = indent + "  "
    return "\n".join(
        [
            f"{indent}SOME (BoundedCase16594StreamingInput",
            f"{child}[",
            render_pairs(cell.box, child + "  "),
            f"{child}]",
            f"{child}[",
            render_pairs(cell.centers, child + "  "),
            f"{child}]",
            f"{child}[",
            render_words(cell.radii, child + "  "),
            f"{child}])",
        ]
    )


def render_lookup(cells: list[Cell], start: int, stop: int, indent: str) -> str:
    if stop - start == 1:
        value = render_cell(cells[start], indent + "  ")
        return f"{indent}if index = {start} then\n{value}\n{indent}else NONE"
    middle = (start + stop) // 2
    left = render_lookup(cells, start, middle, indent + "  ")
    right = render_lookup(cells, middle, stop, indent + "  ")
    return (
        f"{indent}if index < {middle} then\n{left}\n"
        f"{indent}else\n{right}"
    )


def digest(cells: list[Cell]) -> int:
    result = 0
    for cell in cells:
        for lower, upper in cell.box + cell.centers:
            result ^= lower ^ upper
        for radius in cell.radii:
            result ^= radius
    return result


def render(cells: list[Cell]) -> str:
    lookup = render_lookup(cells, 0, len(cells), "    ")
    return f'''(*
  GENERATED by generate_case16594_streaming_input_data.py.
  Source jobs SHA-256: {EXPECTED_INPUT_SHA256}
  DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.
*)
Theory compute_boundedCase16594StreamingInputData
Ancestors
  compute_bounded
Libs
  bossLib wordsLib

Datatype:
  bounded_case16594_streaming_input =
    BoundedCase16594StreamingInput
      ((word64 # word64) list)
      ((word64 # word64) list)
      (word64 list)
End

Definition bounded_case16594_streaming_input_at_def:
  bounded_case16594_streaming_input_at index =
{lookup}
End

Definition bounded_case16594_streaming_input_digest_def:
  bounded_case16594_streaming_input_digest 0 digest = SOME digest ∧
  bounded_case16594_streaming_input_digest (SUC remaining) digest =
    (case bounded_case16594_streaming_input_at (875 - SUC remaining) of
     | NONE => NONE
     | SOME (BoundedCase16594StreamingInput box centers radii) =>
       bounded_case16594_streaming_input_digest remaining
         (FOLDL word_xor
           (FOLDL (λdigest pair.
             word_xor digest (word_xor (FST pair) (SND pair)))
             (FOLDL (λdigest pair.
               word_xor digest (word_xor (FST pair) (SND pair)))
               digest box)
             centers)
           radii))
End

Theorem bounded_case16594_streaming_input_digest_value:
  bounded_case16594_streaming_input_digest 875 0w = SOME {digest(cells)}w
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_streaming_input_out_of_range:
  bounded_case16594_streaming_input_at 875 = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("jobs", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(render(load_cells(args.jobs)), encoding="utf-8")


if __name__ == "__main__":
    main()
