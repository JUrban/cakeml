#!/usr/bin/env python3
"""Fail-closed inventory for the direct Flyspeck bootstrap directives.

This is deliberately not a source rewriter.  In particular, accepting a
``#load`` line here does not assert that the named library is present in the
compiled Candle environment.  It only freezes the exact directives for which
the loader must later provide an explicit library capability or a reviewed,
deterministic normalization.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
import sys


EXPECTED_LOADS = ("unix.cma", "str.cma")
DIRECTIVE = re.compile(
    r'#(?P<name>[A-Za-z_][A-Za-z0-9_]*)[ \t]+"'
    r'(?P<argument>(?:[^"\\]|\\.)*)"[ \t]*;;'
)


@dataclass(frozen=True)
class Directive:
    line: int
    name: str
    argument: str


def git_head(repository: Path) -> str:
    result = subprocess.run(
        ["git", "-C", str(repository), "rev-parse", "HEAD"],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return result.stdout.strip()


def skip_quoted(source: str, index: int, delimiter: str, line: int) -> tuple[int, int]:
    """Skip a string, character, or HOL quotation and preserve line count."""

    index += len(delimiter)
    while index < len(source):
        if delimiter in ('"', "'") and source[index] == "\\":
            index += min(2, len(source) - index)
            continue
        if source.startswith(delimiter, index):
            return index + len(delimiter), line
        if source[index] == "\n":
            line += 1
        index += 1
    raise ValueError(f"unterminated {delimiter!r} quotation before line {line}")


def scan(source: str) -> list[Directive]:
    found: list[Directive] = []
    index = 0
    line = 1
    line_has_code = False

    while index < len(source):
        if source[index] == "\n":
            line += 1
            line_has_code = False
            index += 1
            continue
        if source[index] in " \t\r\f":
            index += 1
            continue
        if source.startswith("(*", index):
            depth = 1
            index += 2
            while index < len(source) and depth:
                if source.startswith("(*", index):
                    depth += 1
                    index += 2
                elif source.startswith("*)", index):
                    depth -= 1
                    index += 2
                else:
                    if source[index] == "\n":
                        line += 1
                        line_has_code = False
                    index += 1
            if depth:
                raise ValueError(f"unterminated comment before line {line}")
            continue
        if source.startswith("``", index):
            index, line = skip_quoted(source, index, "``", line)
            line_has_code = True
            continue
        if source[index] == "`":
            index, line = skip_quoted(source, index, "`", line)
            line_has_code = True
            continue
        if source[index] in ('"', "'"):
            index, line = skip_quoted(source, index, source[index], line)
            line_has_code = True
            continue
        if source[index] == "#" and not line_has_code:
            match = DIRECTIVE.match(source, index)
            if match is None:
                line_end = source.find("\n", index)
                if line_end == -1:
                    line_end = len(source)
                spelling = source[index:line_end].strip()
                raise ValueError(f"malformed or unsupported directive at line {line}: {spelling}")
            # The allowlist spells the accepted filenames literally.  An
            # escaped alternative is intentionally a distinct, rejected
            # contract rather than another way to smuggle in a library name.
            found.append(Directive(line, match.group("name"), match.group("argument")))
            index = match.end()
            line_has_code = True
            continue

        line_has_code = True
        index += 1

    return found


def check_contract(directives: list[Directive]) -> None:
    actual = tuple(
        directive.argument
        for directive in directives
        if directive.name == "load"
    )
    unsupported = [directive for directive in directives if directive.name != "load"]
    if unsupported:
        rendered = ", ".join(
            f"line {directive.line}: #{directive.name}" for directive in unsupported
        )
        raise ValueError(f"unsupported bootstrap directives: {rendered}")
    if actual != EXPECTED_LOADS:
        raise ValueError(
            f"bootstrap load contract mismatch: expected {EXPECTED_LOADS!r}, got {actual!r}"
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root", required=True, type=Path)
    parser.add_argument("--expected-head", required=True)
    args = parser.parse_args()

    root = args.flyspeck_root.resolve()
    actual_head = git_head(root)
    if actual_head != args.expected_head:
        print(
            f"Flyspeck head mismatch: expected {args.expected_head}, got {actual_head}",
            file=sys.stderr,
        )
        return 1

    source_path = root / "text_formalization" / "build" / "strictbuild.hl"
    try:
        directives = scan(source_path.read_text(encoding="utf-8", errors="surrogateescape"))
        check_contract(directives)
    except (OSError, UnicodeError, ValueError) as error:
        print(f"{source_path}: {error}", file=sys.stderr)
        return 1

    print(f"flyspeck_head={actual_head}")
    print(f"source={source_path.relative_to(root)}")
    for directive in directives:
        print(f"line.{directive.line}=#{directive.name} {directive.argument}")
    print("FLYSPECK_BOOTSTRAP_DIRECTIVE_INVENTORY_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
