#!/usr/bin/env python3
"""Generate typed case16594 scalar certificates for the checked executor.

The input is the pinned, repeat-identical DEVELOPMENT capture from the native
fixed-scalar lane.  Every value remains untrusted: the translated Candle
executor checks square-root and reciprocal certificates before it can accept
a cell.  This generator authenticates the capture identity and its exact
31-record-per-cell typed shape, then renders the corresponding HOL data.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
from pathlib import Path


EXPECTED_CERTIFICATE_SHA256 = (
    "bc933fc79ac5ee53aef823e3933f771965caf63465e96023763f5ac8139d8caa"
)
WORD_LIMIT = 1 << 64


@dataclass(frozen=True)
class Record:
    kind: str
    lower_range: bool
    upper_range: bool
    values: tuple[tuple[int, int], ...]


def checked_signed(value: str, context: str) -> int:
    result = int(value)
    if abs(result) >= WORD_LIMIT:
        raise ValueError(f"signed endpoint width drift at {context}: {result}")
    return result


def load_cells(path: Path) -> list[tuple[Record, ...]]:
    payload = path.read_bytes()
    actual_hash = hashlib.sha256(payload).hexdigest()
    if actual_hash != EXPECTED_CERTIFICATE_SHA256:
        raise ValueError(f"case16594 analytic certificate drift: {actual_hash}")

    rows = payload.decode("ascii").splitlines()
    if len(rows) != 875 * 31:
        raise ValueError(f"analytic certificate row count drift: {len(rows)}")

    cells: list[list[Record]] = [[] for _ in range(875)]
    counts = {"sqrt": 0, "inverse": 0, "atan": 0}
    lower_count = 0
    upper_count = 0
    for row_index, row in enumerate(rows):
        fields = row.split("\t")
        if len(fields) != 15:
            raise ValueError(f"analytic certificate row shape drift: {row_index}")
        job = int(fields[0])
        ordinal = int(fields[1])
        if job != row_index // 31 or ordinal != row_index % 31:
            raise ValueError(f"analytic certificate order drift: {row_index}")
        kind = fields[2]
        if kind not in counts:
            raise ValueError(f"unknown analytic certificate kind: {kind}")
        if fields[3] not in {"0", "1"} or fields[4] not in {"0", "1"}:
            raise ValueError(f"malformed atan option flag: {row_index}")
        lower_range = fields[3] == "1"
        upper_range = fields[4] == "1"
        if kind != "atan" and (lower_range or upper_range):
            raise ValueError(f"non-atan option flag at row {row_index}")
        values = tuple(
            (
                checked_signed(fields[5 + 2 * index], f"row {row_index}[{index}] lower"),
                checked_signed(fields[6 + 2 * index], f"row {row_index}[{index}] upper"),
            )
            for index in range(5)
        )
        if any(lower > upper for lower, upper in values):
            raise ValueError(f"reversed certificate interval at row {row_index}")
        counts[kind] += 1
        lower_count += int(lower_range)
        upper_count += int(upper_range)
        cells[job].append(Record(kind, lower_range, upper_range, values))

    if counts != {"sqrt": 8750, "inverse": 12250, "atan": 6125}:
        raise ValueError(f"analytic certificate kind count drift: {counts}")
    if (lower_count, upper_count) != (107, 107):
        raise ValueError(
            f"analytic range option count drift: {lower_count}, {upper_count}"
        )
    if any(len(cell) != 31 for cell in cells):
        raise ValueError("analytic certificate cell width drift")
    return [tuple(cell) for cell in cells]


def index_data(cells: list[tuple[Record, ...]]) -> tuple[
    list[tuple[int, int]], list[tuple[object, ...]], list[list[int]]
]:
    intervals: list[tuple[int, int]] = []
    interval_indices: dict[tuple[int, int], int] = {}
    records: list[tuple[object, ...]] = []
    record_indices: dict[tuple[object, ...], int] = {}
    plans: list[list[int]] = []

    def interval_index(value: tuple[int, int]) -> int:
        if value not in interval_indices:
            interval_indices[value] = len(intervals)
            intervals.append(value)
        return interval_indices[value]

    for cell in cells:
        plan = []
        for record in cell:
            values = record.values
            if record.kind == "sqrt":
                key: tuple[object, ...] = (
                    "sqrt", *(interval_index(value) for value in values)
                )
            elif record.kind == "inverse":
                if any(value != (0, 0) for value in values[2:]):
                    raise ValueError("nonzero inverse padding")
                key = (
                    "inverse", interval_index(values[0]),
                    interval_index(values[1]),
                )
            else:
                if values[4] != (0, 0):
                    raise ValueError("nonzero atan padding")
                key = (
                    "atan",
                    interval_index(values[0]) if record.lower_range else None,
                    interval_index(values[1]) if record.upper_range else None,
                    interval_index(values[2]), interval_index(values[3]),
                )
            if key not in record_indices:
                record_indices[key] = len(records)
                records.append(key)
            plan.append(record_indices[key])
        plans.append(plan)
    if len(intervals) != 23108 or len(records) != 7902:
        raise ValueError(
            f"dictionary cardinality drift: {len(intervals)}, {len(records)}"
        )
    return intervals, records, plans


def render_raw_interval(value: tuple[int, int]) -> str:
    lower, upper = value
    return (
        "C16594RawInterval "
        f"{'T' if lower < 0 else 'F'} {abs(lower)}w "
        f"{'T' if upper < 0 else 'F'} {abs(upper)}w"
    )


def render_index_option(value: object) -> str:
    return "NONE" if value is None else f"SOME {value}"


def render_raw_record(record: tuple[object, ...]) -> str:
    if record[0] == "sqrt":
        return "C16594RawSqrt " + " ".join(str(value) for value in record[1:])
    if record[0] == "inverse":
        return f"C16594RawInverse {record[1]} {record[2]}"
    return (
        "C16594RawAtan "
        f"({render_index_option(record[1])}) "
        f"({render_index_option(record[2])}) {record[3]} {record[4]}"
    )


def render_tree(values: list[object], renderer, begin: int, end: int,
                indent: str) -> str:
    if begin == end:
        return "C16594Empty"
    middle = (begin + end) // 2
    child_indent = "    "
    left = render_tree(values, renderer, begin, middle, child_indent)
    right = render_tree(values, renderer, middle + 1, end, child_indent)
    return "\n".join(
        [
            f"C16594Node {middle} ({renderer(values[middle])})",
            f"{child_indent}({left})",
            f"{child_indent}({right})",
        ]
    )


def render_plan(plan: list[int], final: bool) -> str:
    suffix = ";" if not final else ""
    values = ";".join(str(value) for value in plan)
    return f"    [{values}]{suffix}"


def render(cells: list[tuple[Record, ...]]) -> str:
    intervals, records, plans = index_data(cells)
    interval_tree = render_tree(
        intervals, render_raw_interval, 0, len(intervals), "  "
    )
    record_tree = render_tree(
        records, render_raw_record, 0, len(records), "  "
    )
    plan_data = "\n".join(
        render_plan(plan, index + 1 == len(plans))
        for index, plan in enumerate(plans)
    )
    return f'''(*
  GENERATED by generate_case16594_analytic_certificate_data.py.
  Analytic certificate SHA-256: {EXPECTED_CERTIFICATE_SHA256}
  DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.
*)
Theory compute_boundedCase16594AnalyticCertificateData
Ancestors
  compute_boundedAnalyticProgram
Libs
  bossLib

Datatype:
  bounded_case16594_raw_interval =
    C16594RawInterval bool word64 bool word64
End

Datatype:
  bounded_case16594_raw_certificate =
    C16594RawSqrt num num num num num
  | C16594RawInverse num num
  | C16594RawAtan (num option) (num option) num num
End

Datatype:
  bounded_case16594_tree =
    C16594Empty
  | C16594Node num 'a bounded_case16594_tree bounded_case16594_tree
End

Definition bounded_case16594_interval_tree_def:
  bounded_case16594_interval_tree =
    {interval_tree}
End

Definition bounded_case16594_certificate_tree_def:
  bounded_case16594_certificate_tree =
    {record_tree}
End

Definition bounded_case16594_certificate_plans_def:
  bounded_case16594_certificate_plans : num list list =
  [
{plan_data}
  ]
End

Theorem bounded_case16594_certificate_plans_shape:
  LENGTH bounded_case16594_certificate_plans = 875 ∧
  EVERY (λplan. LENGTH plan = 31)
    bounded_case16594_certificate_plans
Proof
  EVAL_TAC
QED

val _ = export_theory ();
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificates", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    cells = load_cells(args.certificates)
    args.output.write_text(render(cells), encoding="utf-8")


if __name__ == "__main__":
    main()
