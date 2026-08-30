#!/usr/bin/env python3
"""Focused structural regressions for the parser-diagnostic x64 proof.

The executable bootstrap theory is intentionally expensive to replay.  These
checks fail closed if the lightweight, mode-specific proof obligations lose an
exact protocol field or cease to flow through the backend correctness theorem.
They supplement, rather than replace, a Holmake replay of the theory closure.
"""

from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[6]
COMPILER64 = ROOT / "compiler/bootstrap/translation/compiler64ProgScript.sml"
X64_PROOF = ROOT / (
    "compiler/bootstrap/compilation/x64/64/proofs/"
    "x64BootstrapProofScript.sml"
)


def theorem_block(text: str, theorem: str) -> str:
    start_marker = f"Theorem {theorem}"
    start = text.index(start_marker)
    end = text.index("\nQED", start) + len("\nQED")
    return text[start:end]


def definition_block(text: str, definition: str) -> str:
    start_marker = f"Definition {definition}"
    start = text.index(start_marker)
    end = text.index("\nEnd", start) + len("\nEnd")
    return text[start:end]


class ParserDiagnosticX64ProofTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.compiler64 = COMPILER64.read_text(encoding="utf-8")
        cls.x64 = X64_PROOF.read_text(encoding="utf-8")

    def test_ordinary_semantics_excludes_diagnostic_modes(self) -> None:
        ordinary = theorem_block(self.compiler64, "semantics_compiler64_prog:")
        self.assertIn(
            "¬has_candle_parser_diagnostic_mode (TL cl)", ordinary
        )

    def test_exact_error_source_theorem_binds_protocol_and_exit(self) -> None:
        error = theorem_block(
            self.compiler64, "semantics_compiler64_prog_parser_error_exact:"
        )
        required = (
            "caml_parser$run inp = INL (l,err)",
            "candle_parser_diagnostic_result_prefix ^ nonce ^",
            "«\\tPARSE_ERROR\\n»",
            "candle_parser_diagnostic_error_text (implode inp) l err",
            "Final_event (ExtCall «exit») [] [65w] FFI_diverged",
        )
        for fragment in required:
            with self.subTest(fragment=fragment):
                self.assertIn(fragment, error)

    def test_run_success_is_also_parser_result_specific(self) -> None:
        ok = theorem_block(
            self.compiler64, "semantics_compiler64_prog_parser_ok_exact:"
        )
        self.assertIn("caml_parser$run inp = INR res", ok)
        self.assertIn("candle_parser_diagnostic_result_prefix ^ nonce ^", ok)
        self.assertIn("«\\tOK\\n»", ok)

    def test_hol_reply_variables_do_not_capture_stdio_overloads(self) -> None:
        blocks = [
            definition_block(
                self.compiler64, "candle_parser_diagnostic_reply_def:"
            ),
            definition_block(
                self.compiler64, "candle_parser_diagnostic_success_fs_def:"
            ),
        ]
        for theorem in (
            "candle_parser_diagnostic_reply_calls_parser_directly:",
            "run_candle_parser_diagnostic_ok_spec:",
            "run_candle_parser_diagnostic_error_spec:",
            "main_candle_parser_diagnostic_ok_spec:",
            "main_candle_parser_diagnostic_error_spec:",
            "main_candle_parser_diagnostic_ok_whole_prog_spec:",
            "main_candle_parser_diagnostic_error_whole_prog_spec:",
            "semantics_compiler64_prog_parser_ok:",
            "semantics_compiler64_prog_parser_error:",
        ):
            blocks.append(theorem_block(self.compiler64, theorem))
        overloaded_name = re.compile(
            r"(?<![A-Za-z0-9_])(?:stdout|stderr)(?![A-Za-z0-9_])"
        )
        for block in blocks:
            with self.subTest(block=block.splitlines()[0]):
                self.assertIsNone(overloaded_name.search(block))

    def test_print_specs_bind_the_semantic_reply_explicitly(self) -> None:
        explicit_reply_print = re.compile(
            r"xapp_spec print_spec\n\s*\\\\ qexists_tac `reply_out`\n"
            r"\s*\\\\ xsimpl"
        )
        for theorem in (
            "run_candle_parser_diagnostic_ok_spec:",
            "run_candle_parser_diagnostic_error_spec:",
        ):
            block = theorem_block(self.compiler64, theorem)
            with self.subTest(theorem=theorem):
                self.assertEqual(block.count("xapp_spec print_spec"), 1)
                self.assertEqual(block.count("qexists_tac `reply_out`"), 1)
                self.assertEqual(len(explicit_reply_print.findall(block)), 1)

    def test_each_diagnostic_mode_has_a_distinct_compiled_theorem(self) -> None:
        for mode in ("capability", "ok", "error"):
            with self.subTest(mode=mode):
                compiled = theorem_block(
                    self.x64,
                    f"cake_parser_diagnostic_{mode}_compiled_thm =",
                )
                self.assertIn("x64_compile_correct_from_termination", compiled)

    def test_x64_bridge_uses_exact_run_theorems_and_backend_correctness(self) -> None:
        required = (
            "semantics_compiler64_prog_parser_capability",
            "semantics_compiler64_prog_parser_ok_exact",
            "semantics_compiler64_prog_parser_error_exact",
            "MATCH_MP semantics_prog_Terminate_not_Fail sem",
            "MATCH_MP compile_correct_eval (cj 1 compiler64_compiled)",
            "REWRITE_RULE [sem_sing,AND_IMP_INTRO]",
            "parser_capability_output",
            "parser_ok_output",
            "parser_error_output",
        )
        for fragment in required:
            with self.subTest(fragment=fragment):
                self.assertIn(fragment, self.x64)


if __name__ == "__main__":
    unittest.main()
