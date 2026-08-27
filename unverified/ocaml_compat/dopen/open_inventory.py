#!/usr/bin/env python3
"""Conservative lexical inventory for OCaml module/open constructs.

The Flyspeck sources contain HOL quotations that a stock OCaml parser cannot
consume without the HOL Light preprocessor.  This scanner therefore works at
the lexical level, ignores nested comments, strings and HOL backtick
quotations, and reports only constructs whose token prefix is unambiguous.
It is an inventory aid, not an OCaml parser or acceptance test.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import sys


@dataclass(frozen=True)
class Token:
    text: str
    line: int


def is_ident_start(char: str) -> bool:
    return char == "_" or char.isalpha()


def is_ident_continue(char: str) -> bool:
    return char == "_" or char == "'" or char.isalnum()


def lex(source: str) -> list[Token]:
    tokens: list[Token] = []
    index = 0
    line = 1
    length = len(source)

    while index < length:
        char = source[index]

        if char == "\n":
            line += 1
            index += 1
            continue

        if source.startswith("(*", index):
            depth = 1
            index += 2
            while index < length and depth:
                if source.startswith("(*", index):
                    depth += 1
                    index += 2
                elif source.startswith("*)", index):
                    depth -= 1
                    index += 2
                else:
                    if source[index] == "\n":
                        line += 1
                    index += 1
            if depth:
                raise ValueError(f"unterminated comment starting before line {line}")
            continue

        if char == '"':
            index += 1
            while index < length:
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    if source[index] == "\n":
                        line += 1
                    index += 1
            else:
                raise ValueError(f"unterminated string before line {line}")
            continue

        # Skip ordinary OCaml character literals without confusing type
        # variables such as 'a with quoted characters such as '"'.
        if char == "'" and index + 2 < length:
            char_end = index + 2
            if source[index + 1] == "\\":
                char_end = index + 2
                if char_end < length and source[char_end].isdigit():
                    while char_end < length and char_end < index + 5 and source[char_end].isdigit():
                        char_end += 1
                elif char_end < length and source[char_end] in "xX":
                    char_end = min(length, char_end + 3)
                else:
                    char_end += 1
            if char_end < length and source[char_end] == "'":
                index = char_end + 1
                continue

        # HOL Light quotations use `...`/``...``.  Camlp5 revised-syntax
        # stream patterns use an unpaired backtick before a token.  Treat a
        # single backtick as a quotation only when it closes on the same line;
        # double-backtick quotations may span lines.
        line_end = source.find("\n", index + 1)
        if line_end == -1:
            line_end = length
        single_quote_closes = source.find("`", index + 1, line_end) != -1
        if char == "`" and (
            source.startswith("``", index) or single_quote_closes
        ):
            delimiter_length = 2 if source.startswith("``", index) else 1
            delimiter = "`" * delimiter_length
            index += delimiter_length
            while index < length and not source.startswith(delimiter, index):
                if source[index] == "\n":
                    line += 1
                index += 1
            if index == length:
                raise ValueError(f"unterminated HOL quotation before line {line}")
            index += delimiter_length
            continue

        if is_ident_start(char):
            start = index
            token_line = line
            index += 1
            while index < length and is_ident_continue(source[index]):
                index += 1
            tokens.append(Token(source[start:index], token_line))
            continue

        if char in ".=()!:;":
            tokens.append(Token(char, line))

        index += 1

    return tokens


def read_module_path(tokens: list[Token], index: int) -> tuple[str | None, int]:
    if index >= len(tokens) or not tokens[index].text[0].isupper():
        return None, index

    segments = [tokens[index].text]
    index += 1
    while (
        index + 1 < len(tokens)
        and tokens[index].text == "."
        and tokens[index + 1].text[0].isupper()
    ):
        segments.append(tokens[index + 1].text)
        index += 2
    return ".".join(segments), index


def after_open_bang(tokens: list[Token], index: int) -> int:
    if index < len(tokens) and tokens[index].text == "!":
        return index + 1
    return index


def inventory(tokens: list[Token]) -> list[tuple[int, str, str]]:
    found: list[tuple[int, str, str]] = []
    index = 0

    while index < len(tokens):
        token = tokens[index]

        if (
            token.text == "let"
            and index + 1 < len(tokens)
            and tokens[index + 1].text == "open"
        ):
            path_index = after_open_bang(tokens, index + 2)
            path, _ = read_module_path(tokens, path_index)
            found.append((tokens[index + 1].line, "let-open", path or "?"))

        elif token.text == "open" and not (
            index > 0 and tokens[index - 1].text == "let"
        ):
            path_index = after_open_bang(tokens, index + 1)
            path, _ = read_module_path(tokens, path_index)
            found.append((token.line, "declaration-open", path or "?"))

        elif token.text == "include":
            path, _ = read_module_path(tokens, index + 1)
            found.append((token.line, "include", path or "?"))

        elif token.text == "functor":
            found.append((token.line, "functor", "?"))

        elif token.text == "module":
            if index > 0 and tokens[index - 1].text == "(":
                path, _ = read_module_path(tokens, index + 1)
                found.append((token.line, "first-class-module", path or "?"))
            elif index + 1 < len(tokens) and tokens[index + 1].text != "type":
                module_name = tokens[index + 1].text
                next_index = index + 2
                if next_index < len(tokens) and tokens[next_index].text == "(":
                    found.append((token.line, "functor", module_name))
                elif next_index < len(tokens) and tokens[next_index].text == "=":
                    if (
                        next_index + 1 < len(tokens)
                        and tokens[next_index + 1].text == "functor"
                    ):
                        # The `functor` token itself is reported on its own.
                        pass
                    else:
                        path, _ = read_module_path(tokens, next_index + 1)
                        if path is not None:
                            found.append((token.line, "module-alias", path))

        index += 1

    return found


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="+", type=Path)
    args = parser.parse_args()

    print("file\tline\tkind\tpath")
    for source_path in args.files:
        try:
            source = source_path.read_text(encoding="utf-8", errors="surrogateescape")
            rows = inventory(lex(source))
        except (OSError, UnicodeError, ValueError) as error:
            print(f"{source_path}: {error}", file=sys.stderr)
            return 1
        for line, kind, path in rows:
            print(f"{source_path}\t{line}\t{kind}\t{path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
