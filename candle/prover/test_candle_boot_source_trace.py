#!/usr/bin/env python3
"""Low-cost exact regression for the loader-owned source trace core."""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
BOOT = HERE / "candle_boot.ml"


class CandleBootSourceTraceTests(unittest.TestCase):
    def test_exact_trace_core_compiles_and_emits_closed_session(self) -> None:
        source = BOOT.read_text(encoding="utf-8")
        start = source.index("type sourceTraceBinding =")
        end = source.index("let normalizationOverlay = ref", start)
        exact_trace_source = source[start:end]
        nonce = "a" * 32
        fixture = "\n".join((
            "let isFile _ = true;;",
            "let print = print_string;;",
            "module String = struct",
            "  include String",
            "  let size = length",
            "  let explode s = List.of_seq (to_seq s)",
            "end;;",
            "module Char = struct",
            "  let ( <= ) a b = Stdlib.compare a b < 1",
            "end;;",
            "let pendingLoadedSourceIds = ref ([] : (string * string) list);;",
            exact_trace_source,
            f'let nonce = "{nonce}";;',
            "configureSourceTrace nonce [",
            f'  ("{"3" * 64}","/tree/text/../src/a.ml","/tree/src/a.ml",',
            '   "flyspeck:src/a.ml","a.ml",',
            f'   "{"1" * 32}","{"2" * 64}",',
            f'   "/tree/src/a.ml","{"2" * 64}","-")',
            "];;",
            "let request =",
            '  beginSourceTraceRequest None "needs"',
            '    "/tree/text/../src/a.ml" "/tree/src/a.ml"',
            '    "/tree/src/a.ml" false;;',
            'completeSourceTraceRequest request "cache-skip";;',
            "requestSourceTraceFinish nonce;;",
            "finishSourceTraceIfReady true;;",
            "",
        ))
        compiler = Path("/usr/bin/ocamlc")
        self.assertTrue(compiler.is_file(), "missing OCaml compiler")
        version = subprocess.run(
            [str(compiler), "-version"], check=True, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        ).stdout.strip()
        self.assertEqual(version, "4.14.1")
        with tempfile.TemporaryDirectory() as temporary:
            fixture_path = Path(temporary) / "source_trace.ml"
            executable = Path(temporary) / "source_trace"
            fixture_path.write_text(fixture, encoding="utf-8")
            compilation = subprocess.run(
                [str(compiler), "-o", str(executable), str(fixture_path)],
                check=False, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            self.assertEqual(compilation.returncode, 0, compilation.stderr)
            result = subprocess.run(
                [str(executable)], check=True, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
        self.assertEqual(result.stderr, "")
        self.assertEqual(result.stdout.splitlines(), [
            (
                f"CANDLE_FLYSPECK_SOURCE_TRACE_V1\t{nonce}\tREQUEST\t0\t-"
                f"\tneeds\t{'3' * 64}\tflyspeck:src/a.ml\ta.ml\t{'1' * 32}"
                f"\t{'2' * 64}\t{'2' * 64}\t-\tfresh-cache"
            ),
            f"CANDLE_FLYSPECK_SOURCE_TRACE_V1\t{nonce}\tOUTCOME\t0\tcache-skip",
            f"CANDLE_FLYSPECK_SOURCE_TRACE_V1\t{nonce}\tTERMINAL\t1",
        ])

    def test_loader_orders_requests_cache_outcomes_and_terminal(self) -> None:
        source = BOOT.read_text(encoding="utf-8")
        loader_start = source.index("let loadWithStatus =")
        loader_end = source.index("(* Instantiate lexer *)", loader_start)
        loader = source[loader_start:loader_end]
        self.assertLess(
            loader.index("beginSourceTraceRequest"),
            loader.index("let status = loader canonical selected"),
        )
        self.assertIn("SourceCacheSkip", loader)
        self.assertIn('failSourceTrace "read"', loader)
        done_start = source.index("| Some (Lexer.T_done) ->")
        done_end = source.index("| Some Lexer.T_semis", done_start)
        self.assertIn(
            'completeSourceTraceRequest trace_request "evaluated"',
            source[done_start:done_end],
        )
        eof_start = source.index("try match next () with")
        eof_end = source.index("Some Lexer.T_static_load", eof_start)
        self.assertIn("finishSourceTraceIfReady (loadStackEmpty ())", source[eof_start:eof_end])


if __name__ == "__main__":
    unittest.main()
