#!/usr/bin/env python3
"""Inventory module/open constructs in Flyspeck's ordered full build."""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import subprocess
import sys

from open_inventory import inventory, lex


def extract_string_list(source: str, binding: str) -> list[str]:
    marker = f"let {binding}"
    marker_index = source.find(marker)
    if marker_index == -1:
        raise ValueError(f"binding {binding!r} not found")
    index = source.find("[", marker_index + len(marker))
    if index == -1:
        raise ValueError(f"list for {binding!r} not found")
    index += 1
    paths: list[str] = []

    while index < len(source):
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
                    index += 1
            if depth:
                raise ValueError("unterminated comment in build list")
            continue
        if source.startswith("];;", index):
            return paths
        if source[index] == '"':
            index += 1
            path_chars: list[str] = []
            while index < len(source) and source[index] != '"':
                if source[index] == "\\" and index + 1 < len(source):
                    path_chars.append(source[index + 1])
                    index += 2
                else:
                    path_chars.append(source[index])
                    index += 1
            if index == len(source):
                raise ValueError("unterminated string in build list")
            paths.append("".join(path_chars))
            index += 1
            continue
        index += 1

    raise ValueError(f"unterminated list for {binding!r}")


def git_head(repository: Path) -> str:
    result = subprocess.run(
        ["git", "-C", str(repository), "rev-parse", "HEAD"],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return result.stdout.strip()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root", required=True, type=Path)
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--format", choices=("summary", "tsv"), default="summary")
    args = parser.parse_args()

    root = args.flyspeck_root.resolve()
    actual_head = git_head(root)
    if actual_head != args.expected_head:
        print(
            f"Flyspeck head mismatch: expected {args.expected_head}, got {actual_head}",
            file=sys.stderr,
        )
        return 1

    source_root = root / "text_formalization"
    build_file = source_root / "build" / "build.hl"
    paths = extract_string_list(
        build_file.read_text(encoding="utf-8", errors="surrogateescape"),
        "build_sequence_full",
    )

    rows: list[tuple[str, int, str, str]] = []
    missing: list[str] = []
    errors: list[tuple[str, str]] = []
    for relative_path in paths:
        source_path = (source_root / relative_path).resolve()
        if not source_path.is_file():
            missing.append(relative_path)
            continue
        try:
            source = source_path.read_text(
                encoding="utf-8", errors="surrogateescape"
            )
            source_inventory = inventory(
                lex(
                    source,
                    multiline_single_backticks=source_path.suffix == ".hl",
                )
            )
        except (OSError, ValueError) as error:
            errors.append((relative_path, str(error)))
            continue
        rows.extend(
            (relative_path, line, kind, path)
            for line, kind, path in source_inventory
        )

    if args.format == "tsv":
        print("manifest_path\tline\tkind\tpath")
        for relative_path, line, kind, path in rows:
            print(f"{relative_path}\t{line}\t{kind}\t{path}")
    else:
        counts = Counter(row[2] for row in rows)
        print(f"flyspeck_head={actual_head}")
        print(f"manifest_entries={len(paths)}")
        print(f"manifest_unique_paths={len(set(paths))}")
        print(f"missing_files={len(missing)}")
        print(f"scan_errors={len(errors)}")
        print(f"occurrences={len(rows)}")
        print(f"files_with_occurrences={len(set(row[0] for row in rows))}")
        for kind in sorted(counts):
            print(f"kind.{kind}={counts[kind]}")
        for kind in (
            "declaration-open-bang",
            "let-open",
            "let-open-bang",
            "functor",
            "first-class-module",
        ):
            if kind not in counts:
                print(f"kind.{kind}=0")
        nested_open = sum(
            1
            for _, _, kind, path in rows
            if kind == "declaration-open" and "." in path
        )
        print(f"nested_declaration_open={nested_open}")

    if missing:
        print(f"missing paths: {missing}", file=sys.stderr)
    if errors:
        print(f"scan errors: {errors}", file=sys.stderr)
    if missing or errors:
        return 1

    if args.format == "summary":
        print("FLYSPECK_OPEN_INVENTORY_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
