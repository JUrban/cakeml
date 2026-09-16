#!/usr/bin/env python3
"""Source contract for preserving separators inside nested constructs."""

from pathlib import Path
import unittest


BOOT = Path(__file__).with_name("candle_boot.ml")


class ModuleSeparatorContractTest(unittest.TestCase):
    def test_nested_semicolon_is_forwarded_to_the_parser(self) -> None:
        source = BOOT.read_text(encoding="utf-8")
        start = source.index("| Some Lexer.T_semis when level > 0 ->")
        end = source.index("| Some tok ->", start)
        branch = source[start:end]

        self.assertIn("Buffer.push_back output_buffer Lexer.T_semis", branch)
        self.assertIn("scan level contexts false", branch)
        self.assertNotIn("match contexts", branch)


if __name__ == "__main__":
    unittest.main()
