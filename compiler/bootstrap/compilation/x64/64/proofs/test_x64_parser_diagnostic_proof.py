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


CAPABILITY_MAIN_PREFIX = r"""  \\ xcf_with_def main_v_def
  \\ (xlet_auto >- (xcon \\ xsimpl))
  \\ (xlet_auto >- xsimpl)
  \\ (xlet_auto >- xsimpl)
  \\ xif
  \\ qexists_tac `T`
  \\ fs []
  \\ xapp_spec print_spec
  \\ qexistsl
       [‘COMMANDLINE cl’,
        ‘candle_parser_diagnostic_capability_line’,
        ‘fs’]
  \\ fs [fetch "-"
    "compiler64prog_candle_parser_diagnostic_capability_line_v_thm"]
  \\ xsimpl"""


CAPABILITY_FALSE_MAIN_PREFIX = r"""  \\ xcf_with_def main_v_def
  \\ (xlet_auto >- (xcon \\ xsimpl))
  \\ (xlet_auto >- xsimpl)
  \\ (xlet_auto >- xsimpl)
  \\ (xif >- gvs [])"""


DIAGNOSTIC_FALSE_MAIN_PREFIX = CAPABILITY_FALSE_MAIN_PREFIX + r"""
  \\ (xlet_auto >- xsimpl)"""


OK_MAIN_SUFFIX = r"""  \\ xapp_spec run_candle_parser_diagnostic_ok_spec
  \\ qexistsl [‘COMMANDLINE cl’,‘reply_out’,‘fs’,‘inp’,‘nonce’]
  \\ fs []
  \\ xsimpl"""


ERROR_MAIN_SUFFIX = r"""  \\ xapp_spec run_candle_parser_diagnostic_error_spec
  \\ qexistsl [‘COMMANDLINE cl’,‘reply_out’,‘reply_err’,‘fs’]
  \\ fs []
  \\ conj_tac >- (qexists_tac ‘nonce’ \\ fs [])
  \\ xsimpl"""


def capability_main_proof_shape(block: str) -> bool:
    return (
        CAPABILITY_MAIN_PREFIX in block
        and block.count("xapp_spec print_spec") == 1
        and re.search(r"(?m)^\s*\\\\ xapp(?:\s|$)", block) is None
    )


def diagnostic_run_main_proof_shape(block: str, suffix: str) -> bool:
    return DIAGNOSTIC_FALSE_MAIN_PREFIX in block and suffix in block


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

    def test_stdio_proofs_bind_frames_and_semantic_replies(self) -> None:
        ok = theorem_block(
            self.compiler64, "run_candle_parser_diagnostic_ok_spec:"
        )
        error = theorem_block(
            self.compiler64, "run_candle_parser_diagnostic_error_spec:"
        )
        for block in (ok, error):
            with self.subTest(theorem=block.splitlines()[0]):
                self.assertIn(
                    "qpat_x_assum `∃text pos. stdin fs text pos` "
                    "strip_assume_tac",
                    block,
                )
                self.assertIn(
                    "xlet_auto_spec (SOME openStdIn_spec_str) >- "
                    "(xcon \\\\ xsimpl)",
                    block,
                )
                self.assertEqual(
                    block.count("xlet_auto_spec (SOME openStdIn_spec_str)"),
                    2,
                )

        self.assertIn("qexistsl [‘emp’,‘inp’,‘fs’,‘0’]", ok)
        self.assertEqual(ok.count("xapp_spec print_spec"), 1)
        self.assertIn(
            "qexistsl [‘RUNTIME’,‘reply_out’,‘fastForwardFD fs 0’]",
            error,
        )
        self.assertIn(
            "[‘RUNTIME’,‘reply_err’,\n"
            "          ‘add_stdout (fastForwardFD fs 0) reply_out’]",
            error,
        )
        self.assertIn(
            "xapp_spec RuntimeProofTheory.Runtime_exit_spec", error
        )

    def test_capability_main_proof_evaluates_and_binds_exact_frame(self) -> None:
        capability = theorem_block(
            self.compiler64,
            "main_candle_parser_diagnostic_capability_spec:",
        )
        self.assertTrue(capability_main_proof_shape(capability))

        hostile_mutations = (
            (
                "  \\\\ (xlet_auto >- xsimpl)\n"
                "  \\\\ (xlet_auto >- xsimpl)\n"
                "  \\\\ xif",
                "  \\\\ (xlet_auto >- xsimpl)\n  \\\\ xif",
            ),
            ("qexists_tac `T`", "qexists_tac `F`"),
            ("[‘COMMANDLINE cl’,", "[‘emp’,"),
            (
                "‘candle_parser_diagnostic_capability_line’,",
                "‘compiler_help_string’,",
            ),
            ("        ‘fs’]", "        ‘fastForwardFD fs 0’]"),
            (
                "[‘COMMANDLINE cl’,\n"
                "        ‘candle_parser_diagnostic_capability_line’,\n"
                "        ‘fs’]",
                "[‘fs’,\n"
                "        ‘candle_parser_diagnostic_capability_line’,\n"
                "        ‘COMMANDLINE cl’]",
            ),
            ("xapp_spec print_spec", "xapp"),
            (
                "compiler64prog_candle_parser_diagnostic_capability_line_v_thm",
                "compiler_help_string_v_thm",
            ),
        )
        for old, new in hostile_mutations:
            with self.subTest(mutation=new):
                mutant = capability.replace(old, new, 1)
                self.assertNotEqual(mutant, capability)
                self.assertFalse(capability_main_proof_shape(mutant))

    def test_run_main_proofs_evaluate_capability_and_bind_frames(self) -> None:
        ok = theorem_block(
            self.compiler64, "main_candle_parser_diagnostic_ok_spec:"
        )
        error = theorem_block(
            self.compiler64, "main_candle_parser_diagnostic_error_spec:"
        )
        self.assertTrue(diagnostic_run_main_proof_shape(ok, OK_MAIN_SUFFIX))
        self.assertTrue(
            diagnostic_run_main_proof_shape(error, ERROR_MAIN_SUFFIX)
        )

        ordinary = theorem_block(self.compiler64, "main_spec:")
        self.assertIn(CAPABILITY_FALSE_MAIN_PREFIX, ordinary)

        ordinary_mutant = ordinary.replace(
            CAPABILITY_FALSE_MAIN_PREFIX,
            CAPABILITY_FALSE_MAIN_PREFIX.replace(
                "  \\\\ (xlet_auto >- xsimpl)\n"
                "  \\\\ (xlet_auto >- xsimpl)\n"
                "  \\\\ (xif >- gvs [])",
                "  \\\\ (xlet_auto >- xsimpl)\n"
                "  \\\\ (xif >- gvs [])",
                1,
            ),
            1,
        )
        self.assertNotEqual(ordinary_mutant, ordinary)
        self.assertNotIn(CAPABILITY_FALSE_MAIN_PREFIX, ordinary_mutant)

        hostile_mutations = (
            (ok, OK_MAIN_SUFFIX, "[‘COMMANDLINE cl’,", "[‘emp’,"),
            (ok, OK_MAIN_SUFFIX, "‘reply_out’,‘fs’", "‘reply_err’,‘fs’"),
            (ok, OK_MAIN_SUFFIX, "‘fs’,‘inp’,‘nonce’", "‘fs’,‘nonce’,‘inp’"),
            (ok, OK_MAIN_SUFFIX, "xapp_spec", "xapp"),
            (error, ERROR_MAIN_SUFFIX, "‘reply_out’,‘reply_err’", "‘reply_err’,‘reply_out’"),
            (error, ERROR_MAIN_SUFFIX, "‘reply_err’,‘fs’", "‘reply_err’,‘fastForwardFD fs 0’"),
            (error, ERROR_MAIN_SUFFIX, "xapp_spec", "xapp"),
            (
                error,
                ERROR_MAIN_SUFFIX,
                "conj_tac >- (qexists_tac ‘nonce’ \\\\ fs [])",
                "conj_tac >- (qexists_tac ‘inp’ \\\\ fs [])",
            ),
        )
        for block, suffix, old, new in hostile_mutations:
            with self.subTest(mutation=new):
                mutant = block.replace(old, new, 1)
                self.assertNotEqual(mutant, block)
                self.assertFalse(
                    diagnostic_run_main_proof_shape(mutant, suffix)
                )

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
