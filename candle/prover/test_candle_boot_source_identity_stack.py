#!/usr/bin/env python3
"""Exact low-cost regression for nested Flyspeck source identities."""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
BOOT = HERE / "candle_boot.ml"


class CandleBootSourceIdentityStackTests(unittest.TestCase):
    def test_exact_production_stack_handles_nested_loadt(self) -> None:
        source = BOOT.read_text(encoding="utf-8")
        start_marker = (
            "let loadedSourceIds = ref ([]: (string * string) list);;"
        )
        end_marker = "let stdIn = Text_io.openStdIn ();;"
        start = source.index(start_marker)
        end = source.index(end_marker, start)
        exact_stack_source = source[start:end]
        self.assertNotIn("pendingLoadedSourceId = ref (None", exact_stack_source)
        self.assertEqual(
            source.count(
                "pushPendingLoadedSourceId (sourceIdentity original);"
            ),
            2,
        )
        self.assertEqual(
            source.count("Cakeml.commitPendingLoadedSourceId false;;"), 1,
        )
        self.assertEqual(
            source.count("Cakeml.commitPendingLoadedSourceId true;;"), 1,
        )

        fixture = "\n".join((
            exact_stack_source,
            'let outer = ("serialization.hl","11111111111111111111111111111111");;',
            'let nested = ("update_database_400.ml",',
            '              "22222222222222222222222222222222");;',
            "pushPendingLoadedSourceId outer;;",
            "pushPendingLoadedSourceId nested;;",
            "commitPendingLoadedSourceId true;;",
            "commitPendingLoadedSourceId false;;",
            "if !loadedSourceIds <> [outer;nested] then",
            '  failwith "nested source identity order mismatch";;',
            "if !pendingLoadedSourceIds <> [] then",
            '  failwith "nested source identity stack did not drain";;',
            "let underflow_rejected =",
            "  try commitPendingLoadedSourceId false; false",
            '  with Failure message -> message = "missing pending Flyspeck source identity";;',
            "if not underflow_rejected then",
            '  failwith "pending source identity underflow was not rejected";;',
            'print_endline "CANDLE_NESTED_SOURCE_IDENTITIES_OK";;',
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
            fixture_path = Path(temporary) / "nested_source_identities.ml"
            executable = Path(temporary) / "nested_source_identities"
            fixture_path.write_text(fixture, encoding="utf-8")
            subprocess.run(
                [str(compiler), "-o", str(executable), str(fixture_path)],
                check=True, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            result = subprocess.run(
                [str(executable)], check=True, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
        self.assertEqual(result.stderr, "")
        self.assertEqual(
            result.stdout, "CANDLE_NESTED_SOURCE_IDENTITIES_OK\n",
        )


if __name__ == "__main__":
    unittest.main()
