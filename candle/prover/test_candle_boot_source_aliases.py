#!/usr/bin/env python3
"""Low-cost exact regression for authenticated source alias canonicalization."""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
BOOT = HERE / "candle_boot.ml"


class CandleBootSourceAliasTests(unittest.TestCase):
    def test_exact_alias_resolver_compiles_and_uses_canonical_identity(self) -> None:
        source = BOOT.read_text(encoding="utf-8")
        start = source.index(
            "let sourceIdentities =\n"
            "  ref (None: ((string * (string * string)) list) option);;"
        )
        end = source.index(
            "let normalizationOverlay = ref", start,
        )
        exact_resolver_source = source[start:end]
        fixture = "\n".join((
            "let isFile _ = true;;",
            "module String = struct include String let size = length end;;",
            "module Alist = struct",
            "  let rec lookup xs key =",
            "    match xs with",
            "    | [] -> None",
            "    | (candidate,value)::rest ->",
            "        if candidate = key then Some value else lookup rest key",
            "end;;",
            exact_resolver_source,
            'let canonical = "/tree/jHOLLight/a.ml";;',
            'let alias = "/tree/text_formalization/../jHOLLight/a.ml";;',
            'let identity = ("a.ml","11111111111111111111111111111111");;',
            "configureSourceIdentities [(canonical,identity)];;",
            "configureSourceAliases [(alias,canonical)];;",
            "if canonicalSourcePath alias <> canonical then",
            '  failwith "source alias did not canonicalize";;',
            "if sourceIdentity (canonicalSourcePath alias) <> identity then",
            '  failwith "source alias changed logical identity";;',
            "if canonicalSourcePath canonical <> canonical then",
            '  failwith "canonical source path changed";;',
            'print_endline "CANDLE_SOURCE_ALIAS_OK";;',
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
            fixture_path = Path(temporary) / "source_aliases.ml"
            executable = Path(temporary) / "source_aliases"
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
        self.assertEqual(result.stdout, "CANDLE_SOURCE_ALIAS_OK\n")

    def test_loader_cache_and_overlay_use_canonical_source_path(self) -> None:
        source = BOOT.read_text(encoding="utf-8")
        self.assertIn(
            "let canonical = canonicalSourcePath original in\n"
            "          let selected = selectNormalizedSource canonical in",
            source,
        )
        self.assertIn("match loader canonical selected with", source)
        self.assertIn(
            "List.exists (fun x -> x = original) (!loadedFiles)", source,
        )
        self.assertNotIn("match loader selected with", source)


if __name__ == "__main__":
    unittest.main()
